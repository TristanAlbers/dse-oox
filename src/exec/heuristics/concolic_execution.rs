

use std::{cell::RefCell, collections::{HashMap, HashSet}, rc::Rc};

use crate::{
    cfg::CFGStatement, dsl::and, exec::{collect_path_constraints, eval::evaluate, exec_assume, heuristics::fuzzer::*}, reachability::transitions_set, statistics::Statistics, z3_checker, Expression, Options, Statement, SymbolTable
};

// use im_rc::HashSet;
use itertools::Either;
use z3::SatResult;

use super::{
    execution_tree::{sym_exec_execution_tree, ExecutionTree, ExecutionTreeBasedHeuristic}, IdCounter, ProgramCounter, State, SymResult
};
use rand::rngs::ThreadRng;
use slog::{debug, info, Logger};

pub(super) struct ConcolicExecution {
    rng: ThreadRng,
    input_constraints: Vec<Rc<Expression>>,
    found_negations: Vec<Rc<Expression>>,
    coverage_tuples: Vec<(u64, u64)>,
    previously_found_transitions: HashSet<(u64, u64)>,
}

impl ConcolicExecution{
    pub(super) fn new(constraints: Vec<Rc<Expression>>, prev_transitons: &HashSet<(u64, u64)>) -> ConcolicExecution {
        ConcolicExecution {
            rng: rand::thread_rng(),
            input_constraints: constraints,
            found_negations: Vec::new(),
            coverage_tuples: Vec::new(),
            previously_found_transitions: prev_transitons.to_owned(),
        }
    }

    pub(super) fn add_negation(&mut self, expr: Rc<Expression>) {
        self.found_negations.push(expr);
    } 

    pub(super) fn add_coverage_tuple(&mut self, tuple: (u64, u64)) {
        self.coverage_tuples.push(tuple);
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
            
            for leaf in leafs.clone() {
                let cur_statement = RefCell::borrow(&leaf).statement();
                let mut covers_new_code = false;
                if let Some(items) = flows.get(&cur_statement){
                    for stmt in items{
                        if !(self.previously_found_transitions.contains(&(cur_statement, *stmt))){
                            covers_new_code = true;
                        }
                    }
                } else {
                    covers_new_code = true;
                }
                if !covers_new_code { continue; }

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
                                            self.add_negation(expression);
                                        }
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
                return leaf;
            }
            
            leafs[0].clone()
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
    let mut total_coverage = HashSet::new();
    let mut prev_precentage_coverage = 0.0;
    let concrete_options = default_concrete_options(options);
    let concolic_options = default_concolic_options(options);

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
                
                let cur_precentage_coverage = (total_coverage.len() as f32 / total_transitions as f32) * 100.0;
                println!("Coverage: {:?}", cur_precentage_coverage);
                
                if cur_precentage_coverage <= prev_precentage_coverage {
                    // Cannot progress further, is valid
                    return SymResult::Valid
                }
                if cur_precentage_coverage > 98.0 {
                    // Coverage is high enough to be valid.
                    println!("Coverage higher than 98%");
                    return SymResult::Valid
                }

                // Otherwise generate new input for the concrete execution.
                prev_precentage_coverage = cur_precentage_coverage;
                let mut loc_state = state.clone();
                for input in trace.clone() {
                    loc_state.constraints.insert(input);
                }
                let mut heuristic = ConcolicExecution::new(trace, &total_coverage);
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



