use std::{cell::RefCell, collections::{HashMap, HashSet}, ops::Deref, rc::Rc };

use itertools::Either;
use ordered_float::NotNan;
use rand::{rngs::ThreadRng, Rng};
use slog::Logger;

use crate::{
    cfg::CFGStatement, exec::{IdCounter, State}, statistics::Statistics, typeable::Typeable, z3_checker, BinOp, Expression, Identifier, Lit::*, Options, RuntimeType::{self, *}, SourcePos::UnknownPosition, SymResult, SymbolTable
};

use super::{ concrete_execution::ConcreteExecution, execution_tree::sym_exec_execution_tree};

pub(crate) enum FuzzerType{
    SAGE,
    AFL,
    INCREMENTAL,
    EXPERIMENTAL
}

pub(crate) trait Fuzz {
    fn fuzz_inputs(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, coverage: Option<Vec<(u64,u64)>>, found_negations: &mut Option<&mut Vec<Rc<Expression>>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>) -> Vec<Rc<Expression>>;
    fn fuzz_inputs_from_negations(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, negations: &mut Vec<Rc<Expression>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>) -> Vec<Rc<Expression>>;
}

impl Fuzz for RandomFuzzer{

    fn fuzz_inputs_from_negations(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, negations: &mut Vec<Rc<Expression>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>) -> Vec<Rc<Expression>> {
        assert!(negations.len() > 0); // Should be handled in Some call
        let expr = negations.pop().unwrap();
        let mut new_constraints: Vec<Rc<Expression>> = Vec::new();
        let (_, solve_str) = z3_checker::all_z3::verify(expr.deref(), &am);

        let new_values: Vec<&str> = solve_str.split("\n").filter(|s| s.len() > 0).collect();
        for value_comb in new_values{
            let key_value: Vec<&str> = value_comb.split(" -> ").collect();
            assert!(key_value.len() == 2);

            let pair: Vec<(&Identifier, &Rc<Expression>)> = inputs.into_iter().filter(|(k, _)| k.as_str() == *key_value.first().unwrap()).collect();
            assert!(pair.len() == 1);

            let constr = self.create_constraint(*pair.first().unwrap(), ( key_value.first().unwrap().to_string(), key_value.last().unwrap().to_string()));
            new_constraints.push(constr);
        }
        new_constraints
    }

    fn fuzz_inputs(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, _coverage: Option<Vec<(u64,u64)>>, found_negations: &mut Option<&mut Vec<Rc<Expression>>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>) -> Vec<Rc<Expression>>{
        if let Some(paths) = found_negations{
            if paths.len() > 0 {
                return self.fuzz_inputs_from_negations(inputs, *paths, am);
            }
        }
        *found_negations = None;
        let mut fuzzed_inputs: Vec<Rc<Expression>> = Vec::new();
        inputs.into_iter().for_each(
            |(id, ex)|
            {
                match ex.type_of() {
                    t@IntRuntimeType => 
                    {
                        let rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: self.rng.gen::<i64>() }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs, id));
                    },
                    t@UIntRuntimeType => 
                    {
                        let rhs = Rc::new(Expression::Lit { lit: UIntLit { uint_value: self.rng.gen::<u64>() }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs, id));
                    },
                    t@CharRuntimeType => 
                    {
                        let idx = self.rng.gen_range(0..self.charset.len());
                        let rhs = Rc::new(Expression::Lit { lit: CharLit { char_value: self.charset[idx] as char }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs, id));
                    },
                    t@BoolRuntimeType => 
                    {
                        let rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: self.rng.gen_bool(0.5) }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs, id));
                    },
                    t@FloatRuntimeType => 
                    {
                        let rhs = Rc::new(Expression::Lit { lit: FloatLit { float_value: NotNan::new(self.rng.gen::<f64>()).unwrap() }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs, id));
                    },
                    UnknownRuntimeType => panic!("Cannot fuzz unknown input!"),
                    VoidRuntimeType => panic!("Cannot fuzz void input!"),
                    _ => println!("Fuzzing of this type is not implemented!")
                }
            }
        );
        fuzzed_inputs
    }

}

pub(crate) struct RandomFuzzer {
    rng: ThreadRng,
    charset: [u8; 73]
}

impl RandomFuzzer{
    pub(crate) fn new() -> Self {
        Self {
            rng: rand::thread_rng(),
            charset: *b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789)(*&^%$#@!~"
        }
    }

    pub(crate) fn create_constraint(&mut self, (id, expr): (&Identifier, &Rc<Expression>), (_, new_value): (String, String)) -> Rc<Expression>{
        match expr.type_of() {
            t@IntRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: new_value.parse::<i64>().unwrap() }, type_ : t.clone(), info: UnknownPosition });
                self.create_input_expression(t, rhs, id)
            },
            t@UIntRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: UIntLit { uint_value: new_value.parse::<u64>().unwrap() }, type_ : t.clone(), info: UnknownPosition });
                self.create_input_expression(t, rhs, id)
            },
            t@CharRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: CharLit { char_value: new_value.parse::<char>().unwrap() }, type_ : t.clone(), info: UnknownPosition });
                self.create_input_expression(t, rhs, id)
            },
            t@BoolRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: new_value.parse::<bool>().unwrap() }, type_ : t.clone(), info: UnknownPosition });
                self.create_input_expression(t, rhs, id)
            },
            t@FloatRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: FloatLit { float_value: NotNan::new(new_value.parse::<f64>().unwrap()).unwrap() }, type_ : t.clone(), info: UnknownPosition });
                self.create_input_expression(t, rhs, id)
            },
            UnknownRuntimeType => panic!("Cannot fuzz unknown input!"),
            VoidRuntimeType => panic!("Cannot fuzz void input!"),
            _ => panic!("Fuzzing of this type is not implemented!")
        }
    }    

    fn create_input_expression(&self, var_type: RuntimeType, rhs: Rc<Expression>, id: &Identifier ) -> Rc<Expression> {
        Rc::new(Expression::BinOp { 
            bin_op: BinOp::Equal, 
            lhs: Rc::new(Expression::SymbolicVar { var: id.clone(), type_: var_type.clone(), info: UnknownPosition }), 
            rhs, 
            type_: var_type.clone(), 
            info: UnknownPosition 
        })
    }
}

pub(crate) fn start_fuzzing(
    fuzzer: &mut impl Fuzz,
    found_negations: &mut Option<&mut Vec<Rc<Expression>>>,
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    entry_method: crate::cfg::MethodIdentifier,
    options: &Options, 
) -> Either<SymResult, (Vec<Rc<Expression>>, HashSet<(u64, u64)>)>{
    let mut stuck_counter = 0;
    let stack_variables = state.stack.current_variables().unwrap();
    let alias_map: im_rc::HashMap<Identifier, crate::exec::AliasEntry> = state.alias_map.clone();
    let mut fuzzed_inputs = fuzzer.fuzz_inputs(stack_variables, None, found_negations, alias_map.clone());
    let mut new_options = options.clone();
    new_options.prune_path_z3 = true;
    let mut total_found_transitions = HashSet::new();

    loop{
        // Constraint inputs via initial seed
        let mut loc_state = state.clone();
        for input in fuzzed_inputs.clone(){
            loc_state.constraints.insert(dbg!(input));
        }
        // println!("Inputs in concrete: {:?}", fuzzed_inputs);
        let mut heuristic = ConcreteExecution::new();
        

        // Run Program
        let res = sym_exec_execution_tree(
            loc_state, 
            program, 
            flows, 
            st, 
            root_logger.clone(), 
            path_counter.clone(), 
            statistics, 
            entry_method.clone(), 
            &mut heuristic, 
            &new_options
        );

        match res {
            SymResult::Valid => {
                let mut found_new_transitions = false;
                heuristic.coverage_tuples.clone().into_iter().for_each(|k| {if total_found_transitions.insert(k) { found_new_transitions = true } });
                if found_new_transitions { stuck_counter = 0 } else { stuck_counter += 1  };

                // When stuck return the trace
                // println!("Stuck counter: {:?}", stuck_counter);
                if stuck_counter > 5 { return Either::Right((fuzzed_inputs, total_found_transitions)) };
                // Choose new fuzzing inputs (random or based on other inputs)
                fuzzed_inputs = fuzzer.fuzz_inputs(stack_variables, Some(heuristic.coverage_tuples), found_negations, alias_map.clone());
            },
            // Return Invalid when violation is found
            SymResult::Invalid(..) => return Either::Left(res),
        }
        // Repeat untill stuck
    }
}

