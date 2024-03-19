use std::{borrow::Borrow, cell::RefCell, collections::HashMap, ops::Deref, rc::Rc, time::Instant };

use itertools::Either;
use libafl::{executors::ExitKind, inputs::BytesInput};
use slog::{debug, Logger};

use crate::{
    cfg::CFGStatement, exec::{heuristics::utils::afl_fuzzer::oox_fuzzer, IdCounter, State}, stack::StackFrame, statistics::Statistics, Expression, Identifier, Options, RuntimeType::*, SourcePos::UnknownPosition, SymResult, SymbolTable
};

use super::{ concrete_execution::ConcreteExecution, execution_tree::sym_exec_execution_tree};

pub(crate) trait Fuzz {
    fn fuzz_inputs(
        &mut self, 
        state: &State, 
        inputs: &HashMap<Identifier, Rc<Expression>>, 
        max_array_size: u64, 
        found_negations: &mut Option<&mut Vec<Rc<Expression>>>, 
        am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, 
        requirements: Option<Rc<Expression>>, 
        st: &SymbolTable
    ) -> (Vec<Rc<Expression>>, State);
    fn fuzz_inputs_from_negations(
        &mut self, 
        state: &mut State, 
        inputs: &HashMap<Identifier, Rc<Expression>>, 
        negations: &mut Vec<Rc<Expression>>, 
        am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, 
        fuzzed_inputs: Vec<Rc<Expression>>
    ) -> Vec<Rc<Expression>>;
    fn set_latest_input(&mut self, inputs: Vec<Rc<Expression>>);
    fn get_latest_input(&self) -> Vec<Rc<Expression>>;
}



fn get_array_size(expr: Rc<Expression>, array_name: &Identifier) -> Option<Rc<Expression>> {
    match expr.borrow() {
        Expression::BinOp { lhs, rhs, bin_op, type_, info } => {
            if let Expression::SizeOf { var , ..} = lhs.borrow(){
                if var.as_str() == array_name.as_str() {
                    // We convert the SizeOf to a SymbolicVar so it can be solved with z3
                    let new_expr = Rc::new(Expression::BinOp { 
                        lhs: Rc::new(Expression::SymbolicVar { var: array_name.clone(), type_: IntRuntimeType, info: UnknownPosition }), 
                        rhs: rhs.clone(), 
                        bin_op: bin_op.clone(),
                        type_: type_.clone(), 
                        info: info.clone() 
                    });
                    return Some(new_expr); 
                }
            } 
            let left = get_array_size(lhs.clone(), array_name);
            let right = get_array_size(rhs.clone(), array_name);
            if let Some( .. ) = left.clone(){
                return left;
            }
            if let Some( .. ) = right.clone(){
                return right;
            }
            None
        },
        _ => None
    }
}

pub(crate) fn start_fuzzing(
    fuzzer: &mut impl Fuzz,
    found_negations: &mut Option<&mut Vec<Rc<Expression>>>,
    prev_found_transitions: &mut HashMap<(u64, u64), u64>,
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    entry_method: crate::cfg::MethodIdentifier,
    options: &Options,
) -> Either<SymResult, Vec<Rc<Expression>>>{
    let mut total_executions = 0;
    let mut stuck_counter = 0;
    let mut requirements = None;
    let StackFrame { current_member, .. } = state.stack.current_stackframe().unwrap();
            if let Some((requires, _type_guard)) = current_member.requires() {
                requirements = Some(requires.clone());
            }
    let stack_variables = state.stack.current_variables().unwrap();
    let alias_map = state.alias_map.clone();
    let (mut fuzzed_inputs, mut fuzzed_state) = fuzzer.fuzz_inputs(&state, stack_variables, options.symbolic_array_size, found_negations, alias_map.clone(), requirements.clone(), st);
    
    let total_found_transitions = prev_found_transitions;

    loop{
        // Constraint inputs via initial seed
        let now = Instant::now();
        debug!(root_logger, "Stack of concrete program: {:?}", &fuzzed_state);

        let map = Rc::new(RefCell::new(HashMap::<(u64, u64), u64>::new()));
        let mut heuristic = ConcreteExecution::new(map.clone());
        
        // -------------------------------------------------------------
        
        let harness = |_input: &BytesInput| {
            let res = sym_exec_execution_tree(
                fuzzed_state.clone(), 
                program, 
                flows, 
                st, 
                root_logger.clone(), 
                path_counter.clone(), 
                statistics, 
                entry_method.clone(), 
                &mut heuristic, 
                options
            );
            match res {
                SymResult::Valid => {
                    let mut found_new_transitions = false;
                    heuristic.coverage_tuples.deref().borrow_mut().clone().into_iter().for_each(|k| {
                        if let Some(value) = total_found_transitions.get(&k.0){
                            if k.1 > *value {
                                found_new_transitions = true;
                                total_found_transitions.insert(k.0, k.1);
                            }
                        } else {
                            found_new_transitions = true;
                            total_found_transitions.insert(k.0, k.1);
                        }
                    });
                    return ExitKind::Ok;
                },
                // Return Invalid when violation is found
                SymResult::Invalid(..) => return ExitKind::Crash,
            }
        };
        println!("\n---------AFL FUZZER START----------");
        let found_error = oox_fuzzer(harness, map.clone());
        println!("---------AFL  FUZZER  END----------");

        if found_error {
            return Either::Left(SymResult::Invalid(UnknownPosition));
        }

        // -------------------------------------------------------------

        // Run Program
        /* 
        let res = sym_exec_execution_tree(
            fuzzed_state.clone(), 
            program, 
            flows, 
            st, 
            root_logger.clone(), 
            path_counter.clone(), 
            statistics, 
            entry_method.clone(), 
            &mut heuristic, 
            options
        );
        debug!( root_logger,"Conceretely executed in {:?} millis", now.elapsed().as_millis());
        total_executions += 1;
        match res {
            SymResult::Valid => {
                let mut found_new_transitions = false;

                heuristic.coverage_tuples.deref().borrow_mut().clone().into_iter().for_each(|k| {
                    if let Some(value) = total_found_transitions.get(&k.0){
                        if k.1 > *value {
                            found_new_transitions = true;
                            total_found_transitions.insert(k.0, k.1);
                        }
                    } else {
                        found_new_transitions = true;
                        total_found_transitions.insert(k.0, k.1);
                    }
                });

                // dbg!(found_new_transitions);
                if found_new_transitions { 
                    stuck_counter = 0;
                    fuzzer.set_latest_input(fuzzed_inputs.clone()); 
                } else if *found_negations == None { 
                    stuck_counter += 1  
                };
                // When stuck return the trace
                // println!("Stuck counter: {:?}", stuck_counter);
                if stuck_counter > 5 {
                    debug!( root_logger,"Total concrete executions: {:?}", total_executions);
                    return Either::Right(fuzzer.get_latest_input())
                };
                // Choose new fuzzing inputs (random or based on other inputs)
                (fuzzed_inputs, fuzzed_state) = fuzzer.fuzz_inputs(&state,stack_variables, options.symbolic_array_size, found_negations, alias_map.clone(), requirements.clone(), st);
            },
            // Return Invalid when violation is found
            SymResult::Invalid(..) => return Either::Left(res),
        }
        // Repeat untill stuck
        */
    }
}


