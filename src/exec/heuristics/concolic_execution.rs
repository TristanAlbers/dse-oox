

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    cfg::CFGStatement, dsl::and, exec::{collect_path_constraints, eval::evaluate, exec_assume, heuristics::fuzzer::*}, reachability::transitions_set, statistics::Statistics, z3_checker, Expression, Options, Statement, SymbolTable
};

// use im_rc::HashSet;
use itertools::Either;
use z3::SatResult;

use super::{
    execution_tree::{sym_exec_execution_tree, ExecutionTree, ExecutionTreeBasedHeuristic}, utils::random_fuzzer::RandomFuzzer, IdCounter, ProgramCounter, State, SymResult
};
use rand::rngs::ThreadRng;
use slog::{debug, info, Logger};

pub(super) struct ConcolicExecution {
    rng: ThreadRng,
    input_constraints: Vec<Rc<Expression>>,
    found_negations: Vec<Rc<Expression>>,
    coverage_tuples: HashMap<(u64, u64), u64>,
    previously_found_transitions: HashMap<(u64, u64), u64>,
    unreachable_tuples: HashMap<(u64, u64), u64>,
}

impl ConcolicExecution{
    pub(super) fn new(
        constraints: Vec<Rc<Expression>>,
        prev_transitons: &HashMap<(u64, u64), u64>,
        unreachable_tuples: HashMap<(u64, u64), u64>
    ) -> ConcolicExecution {
        ConcolicExecution {
            rng: rand::thread_rng(),
            input_constraints: constraints,
            found_negations: Vec::new(),
            coverage_tuples: HashMap::new(),
            previously_found_transitions: prev_transitons.to_owned(),
            unreachable_tuples,
        }
    }

    pub(super) fn add_negation(&mut self, expr: Rc<Expression>) {
        self.found_negations.push(expr);
    }

    pub(super) fn get_unreachable_tuples (self) -> HashMap<(u64, u64), u64> {
        self.unreachable_tuples
    }  

    pub(super) fn add_coverage_tuple(&mut self, leaf: Rc<RefCell<ExecutionTree>>) {
        let parent_statement = leaf.borrow().parent().upgrade().unwrap_or_default().borrow().statement();
        let child_statement = leaf.borrow().statement();
        let tuple = (parent_statement, child_statement);
        if let Some(value) = self.coverage_tuples.get(&tuple){
            self.coverage_tuples.insert(tuple, value + 1);
        } else {
            self.coverage_tuples.insert(tuple, 0);
        }
    }

    pub(super) fn add_found_transition(&mut self, tuple: (u64, u64)) {
        if let Some(value) = self.previously_found_transitions.get(&tuple){
            self.previously_found_transitions.insert(tuple, value + 1);
            // println!("Added {:?} \n in {:?}", tuple, self.previously_found_transitions)
        } else {
            self.previously_found_transitions.insert(tuple, 0);
            // println!("Added {:?} \n in {:?}", tuple, self.previously_found_transitions)
        }
    }
}

impl ExecutionTreeBasedHeuristic for ConcolicExecution {
    fn choice(
            &mut self,
            root: Rc<RefCell<ExecutionTree>>,
            program: &HashMap<u64, CFGStatement>,
            flows: &HashMap<u64, Vec<u64>>,
            st: &SymbolTable,
            _entry_method: &crate::cfg::MethodIdentifier,
            _coverage: &mut HashMap<ProgramCounter, usize>,
            root_logger: Logger,
            path_counter: Rc<RefCell<IdCounter<u64>>>,
            statistics: &mut Statistics,
            options: &Options,
        ) -> Rc<RefCell<ExecutionTree>> {
            let leafs = ExecutionTree::leafs(root.clone());
            let mut tuples: HashMap<(u64, u64), u64> = HashMap::new();
            
            for leaf in leafs.clone() {
                let cur_statement = RefCell::borrow(&leaf).statement();
                // let start_time =  Instant::now();
                let mut covers_new_code = false;
                
                if let Some(statements) = flows.get(&cur_statement){
                    for stmt in statements {
                        let tuple = (cur_statement, *stmt);
                        
                        let cur_encounters = self.coverage_tuples.get(&tuple).unwrap_or(&0);
                        let prev_encounters = self.previously_found_transitions.get(&tuple);
                        
                        if prev_encounters == None {
                            // previously uncovered code
                            covers_new_code = true;
                        } else if *cur_encounters > *prev_encounters.unwrap() {
                            // deeper executions of code
                            // println!("Discovers deeper code");
                            covers_new_code = true;
                        }
                        tuples.insert(tuple, *cur_encounters);
                    }
                } else {
                    covers_new_code = true;
                }
                // statistics.measure_xtra(start_time.elapsed().subsec_micros());
                let tuples_are_unreachable = tuples.clone().into_iter().map(|(k,v)| {
                    self.unreachable_tuples.get_key_value(&k) == Some((&k,&v))
                }).fold(true, |acc, num| {acc && num});
                if !covers_new_code || tuples_are_unreachable {
                    // reset tuples since in loop
                    tuples = HashMap::new();
                    continue;
                }

                match program.get(&cur_statement).unwrap() {
                    CFGStatement::Statement( Statement::Assume { assumption, .. } ) => {
                        let mut states = leaf.borrow_mut().take_states().unwrap();
                        leaf.borrow_mut().set_states(states.clone());
                        let mut target_state = states.pop().unwrap();

                        let en = &mut crate::exec::EngineContext {
                            remaining_states: &mut states,
                            path_counter: path_counter.clone(),
                            statistics,
                            st,
                            root_logger: &root_logger,
                            options,
                        };

                        let is_feasible_path = exec_assume(&mut target_state, assumption.clone(), en);
                        
                        if !is_feasible_path{

                            // Lift the constraints on input to check if that is the cause of infeasibility
                            for constr in &self.input_constraints{
                                target_state.constraints.remove(constr);
                            }
                            
                            // Solve for input leading to this specific branch
                            match assumption.clone() {
                                Either::Left(assumption_expr) => {
                                    // Only use the "assumption" here or otherwise we later create constraints for the "trace" which
                                    // we are currently following. 
                                    // Might still be usefull if we regard these both as different paths since it is a valid negation
                                    // because we would otherwise never reach it again ..... Design choices for later

                                    let constraints = collect_path_constraints(&target_state);
                                    let assumption = evaluate(&mut target_state, assumption_expr.clone(), en);
                                    let expression = evaluate(&mut target_state, and(constraints, assumption), en);
                                    
                                    if !(*expression == Expression::FALSE) {
                                        let result: SatResult = z3_checker::all_z3::verify(&expression, &target_state.alias_map).0;
                                        if result == SatResult::Sat && *expression != Expression::TRUE {
                                            // feasible after lifting input constraints, should solve
                                            debug!(root_logger, "Negation found: {:?}", expression);
                                            // println!("Feasible: {:?} \n tuples: {:?}", expression, &tuples);
                                            tuples.into_iter().for_each(|(k,_)| self.add_found_transition(k));
                                            self.add_negation(expression);
                                        } else {
                                            // println!("Infeasible");
                                            self.unreachable_tuples.extend(tuples);
                                        }
                                    } else {
                                        // println!("Infeasible");
                                        self.unreachable_tuples.extend(tuples);
                                    }
                                }
                                Either::Right(_assumption) => {
                                    // --Todo, instanceof calls are not handled.
                                    // Maybe they don't need to be handled since they don't add constraints to use input.
                                    todo!("instanceof calls are not handled");
                                }
                            }
                        }

                    },
                    _ => (),
                }
                self.add_coverage_tuple(Rc::clone(&leaf));
                return leaf;
            }
            
            self.add_coverage_tuple(Rc::clone(&leafs[0]));
            Rc::clone(&leafs[0])
    }
}

pub(crate) fn sym_exec(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    entry_method: crate::cfg::MethodIdentifier,
    options: &Options, 
) -> SymResult {

    // Call fuzzer, wait for output
    let mut fuzzer = RandomFuzzer::new();
    let mut negation_owner;
    let mut found_negations = None;
    let total_transitions = transitions_set(entry_method.clone(), program, flows, st).len();
    let mut prev_coverage = HashMap::new();
    let mut total_coverage = HashMap::new();
    let mut unreachable_tuples = HashMap::new();
    // let mut prev_precentage_coverage = 0.0;
    let concrete_options = default_concrete_options(options);
    let concolic_options = default_concolic_options(options);
    // let mut fake_statistics = Statistics::default();

    loop {
        info!(root_logger, "Concrete invoked"); println!("Concrete invoked");
        let concrete_res = start_fuzzing(
            &mut fuzzer,
            &mut found_negations,
            &mut total_coverage,
            state.clone(), 
            program, 
            flows, 
            st, 
            root_logger.clone(), 
            path_counter.clone(), 
            statistics, 
            entry_method.clone(), 
            &concrete_options
        );
        
        match concrete_res {
            Either::Left(symres) => return symres,
            Either::Right(trace) => {
                info!(root_logger, "Concolic invoked"); println!("Concolic invoked");
                debug!(root_logger, "Trace received: {:?}", trace);
                
                let cur_precentage_coverage = (total_coverage.len() as f32 / total_transitions as f32) * 100.0;
                
                if prev_coverage == total_coverage {
                    // Cannot progress further, is valid
                    return SymResult::Valid
                }
                println!("Progressing...\nCoverage percentage: {:?}", cur_precentage_coverage);
                prev_coverage = total_coverage.clone();
                statistics.measure_switch();
                // if cur_precentage_coverage > 98.0 {
                //     // Coverage is high enough to be valid.
                //     println!("Coverage higher than 98%");
                //     return SymResult::Valid
                // }

                // Otherwise generate new input for the concrete execution.
                // prev_precentage_coverage = cur_precentage_coverage;
                let mut loc_state = state.clone();
                for input in trace.clone() {
                    loc_state.constraints.insert(input);
                }
                let mut heuristic = ConcolicExecution::new(trace, &total_coverage, unreachable_tuples);
                let _concolic_res = sym_exec_execution_tree(
                    loc_state, 
                    program, 
                    flows, 
                    st, 
                    root_logger.clone(), 
                    path_counter.clone(), 
                    statistics, 
                    entry_method.clone(), 
                    &mut heuristic, 
                    &concolic_options
                );
                negation_owner = heuristic.found_negations.clone();
                found_negations = Some(&mut negation_owner);
                unreachable_tuples = heuristic.get_unreachable_tuples();
            },
        }
    }

}

fn default_concrete_options<'a>(options: &'a Options<'a>) -> Options<'a>{
    let mut new_options = options.clone();
    new_options.prune_path_z3 = false;
    new_options.local_solving_threshold = None;
    new_options
}

fn default_concolic_options<'a>(options: &'a Options<'a>) -> Options<'a>{
    let mut new_options = options.clone();
    new_options.prune_path_z3 = true;
    new_options.local_solving_threshold = Some(0);
    new_options
}



