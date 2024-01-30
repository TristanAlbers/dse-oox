

use std::{borrow::BorrowMut, cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    cfg::CFGStatement, exec::{self, eval::evaluate, exec_assume, heuristics::fuzzer::*}, statistics::Statistics, z3_checker, Expression, Identifier, Options, Statement, SymbolTable
};

use itertools::Either;
use z3::SatResult;

use super::{
    execution_tree::{sym_exec_execution_tree, ExecutionTree, ExecutionTreeBasedHeuristic}, IdCounter, ProgramCounter, State, SymResult
};
use rand::rngs::ThreadRng;
use slog::Logger;

pub(super) struct ConcolicExecution {
    rng: ThreadRng,
    input_constraints: Vec<Rc<Expression>>,
    found_negations: Vec<Rc<Expression>>
}

impl ConcolicExecution{
    pub(super) fn new(constraints: Vec<Rc<Expression>>) -> ConcolicExecution {
        ConcolicExecution {
            rng: rand::thread_rng(),
            input_constraints: constraints,
            found_negations: Vec::new()
        }
    }

    pub(super) fn add_negation(&mut self, expr: Rc<Expression>) {
        self.found_negations.push(expr);
    } 
}

impl ExecutionTreeBasedHeuristic for ConcolicExecution {
    fn choice(
            &mut self,
            root: Rc<RefCell<ExecutionTree>>,
            program: &HashMap<u64, CFGStatement>,
            _flows: &HashMap<u64, Vec<u64>>,
            st: &SymbolTable,
            _entry_method: &crate::cfg::MethodIdentifier,
            _coverage: &mut HashMap<ProgramCounter, usize>,
            root_logger: Logger,
            path_counter: Rc<RefCell<IdCounter<u64>>>,
            statistics: &mut Statistics,
            options: &Options,
        ) -> Rc<RefCell<ExecutionTree>> {
            let leafs = ExecutionTree::leafs(root.clone());
            let mut chosen = None;
            
            leafs.into_iter()
            .filter(
                |l|
                if let CFGStatement::Statement( Statement::Assume { .. } ) = program.get(&l.borrow().statement()).unwrap() {
                    true
                } else {
                    false
                }
            )
            .for_each(
                |x|
                {
                    let cfg_statement = program.get(&x.borrow().statement()).unwrap();

                    // idiotic auto reference issues see following link for explanation:
                    // https://stackoverflow.com/questions/75021342/why-creating-a-local-binding-with-borrow-in-rust-makes-inferring-the-type-imposs
                    let mut temp = RefCell::borrow_mut(&x);

                    let mut states = temp.take_states().unwrap();
                    temp.set_states(states.clone());

                    if states.len() > 1 { panic!("Should not happen")}
                    let mut state = states.pop().unwrap();
                    

                    if let CFGStatement::Statement( Statement::Assume { assumption, .. } ) = cfg_statement {
                        
                        let en = &mut crate::exec::EngineContext {
                            remaining_states: &mut states,
                            path_counter: path_counter.clone(),
                            statistics,
                            st,
                            root_logger: &root_logger,
                            options,
                        };

                        let is_feasible_path = exec_assume(state.borrow_mut(), assumption.clone(), en);
                        
                        if !is_feasible_path{

                            // Lift the constraints on input to check if that is the cause of infeasibility
                            for constr in &self.input_constraints{
                                state.constraints.remove(constr);
                            }
                            
                            // Solve for input leading to this specific branch

                            match assumption.clone() {
                                Either::Left(assumption_expr) => {
                                    // dbg!(assumption_expr);
    
                                    let en = &mut crate::exec::EngineContext {
                                        remaining_states: &mut states,
                                        path_counter: path_counter.clone(),
                                        statistics,
                                        st,
                                        root_logger: &root_logger,
                                        options,
                                    };
                                    
                                    // Only use the "assumption" here or otherwise we later create constraints for the "trace" which
                                    // we are currently following. 
                                    // Might still be usefull if we regard these both as different paths since it is a valid negation
                                    // because we would otherwise never reach it again ..... Design choices for later
                                    let expression = evaluate(state.borrow_mut(), assumption_expr, en);

                                    // let constraints = collect_path_constraints(state);
                                    // let assumption = evaluate(state, assumption, en);
                                    // // dbg!(&assumption);
                                    // let expression = evaluate(state, and(constraints, assumption.clone()), en);

                                    if *expression == Expression::FALSE {
                                        // Not feasible, even when input constraints are lifted
                                    } else {
                                        let result: SatResult = z3_checker::all_z3::verify(&expression, &state.alias_map).0;
                                        // eval_assertion(state, expression, en)
                                        if result == SatResult::Sat {
                                            if *expression != Expression::TRUE {
                                                // feasible after lifting input constraints, should solve

                                                self.add_negation(expression);
                                                chosen = Some(Rc::clone(&x));
                                            }
                                        } else {
                                            // Not feasible, even when input constraints are lifted
                                        }
                                    }
                                }
                                Either::Right(_assumption) => {
                                    // --Todo, instanceof calls are not handled.
                                    // Maybe they don't need to be handled since they don't add constraints to use input.
                                }
                            }
                        }

                        
                    ()
                    }
                }
            );

            // When encountering a solveable infeasibility call, choose that branch as the next to be executed
            // This prunes the infeasible branch, allowing us to trace the input further.
            if let Some(option) = chosen{
                return option
            }

            exec::heuristics::random_path::random_path(root, &mut self.rng)
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
    
    let mut state_first_run = state.clone();
    let mut fuzzer = Fuzzer::new(FuzzerType::EXPERIMENTAL);
    let stack_variables = state.stack.current_variables().unwrap();

    let fuzzed_inputs = fuzzer.fuzz_inputs(stack_variables);

    // print initial fuzzed inputs
    println!("Starting first run ...");
    println!("Initial fuzzed inputs: {:?}", fuzzed_inputs);

    // Add input constraints according to fuzzer
    for input in fuzzed_inputs.clone() {
        state_first_run.constraints.insert(input);
    }

    // Create reference to input constraints to be lifted later
    let mut owner_heuristic = ConcolicExecution::new(fuzzed_inputs);

    // Start First SymExe
    let res = sym_exec_execution_tree(
        state_first_run, // ToDo -- Remove clone()
        program, 
        flows, 
        st, 
        root_logger.clone(), 
        path_counter.clone(), 
        statistics, 
        entry_method.clone(), 
        &mut owner_heuristic, 
        options
    );

    // printing result first run:
    println!("First run returned: {:?}", res);
    println!("Found negations: {:?}", owner_heuristic.found_negations);

    // Resulting negations, should solve for new inputs in concolic part.

    let mut new_constraints: Vec<Rc<Expression>> = Vec::new();

    for expr in owner_heuristic.found_negations{
        let (_, solve_str) = z3_checker::all_z3::verify(&expr, &state.alias_map);

        let new_values: Vec<&str> = solve_str.split("\n").filter(|s| s.len() > 0).collect();

        for value_comb in new_values{
            let key_value: Vec<&str> = value_comb.split(" -> ").collect();
            assert!(key_value.len() == 2);

            let pair: Vec<(&Identifier, &Rc<Expression>)> = stack_variables.into_iter().filter(|(k, _)| k.as_str() == *key_value.first().unwrap()).collect();
            assert!(pair.len() == 1);

            let constr = fuzzer.create_constraint(*pair.first().unwrap(), ( key_value.first().unwrap().to_string(), key_value.last().unwrap().to_string()));
            new_constraints.push(constr);
        }
    }

    // Second Run
    println!("Starting second run ...");
    println!("New inputs: {:?}", new_constraints);
    
    // Reset constraints to new set
    let mut owner_heuristic = ConcolicExecution::new(new_constraints.clone());
    let mut state_second_run = state;

    for input in new_constraints {
        state_second_run.constraints.insert(input);
    }

    // SymExe
    let second_res = sym_exec_execution_tree(
        state_second_run,
        program, 
        flows, 
        st, 
        root_logger, 
        path_counter, 
        statistics, 
        entry_method, 
        &mut owner_heuristic, 
        options
    );

    println!("Finished second run ...");
    second_res
}




