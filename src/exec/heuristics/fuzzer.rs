use std::{borrow::Borrow, cell::RefCell, collections::{HashMap, HashSet}, ops::Deref, rc::Rc, time::Instant };

use itertools::Either;
use ordered_float::NotNan;
use rand::{rngs::ThreadRng, Rng};
use slog::Logger;

use crate::{
    cfg::CFGStatement, exec::{IdCounter, State}, stack::StackFrame, statistics::Statistics, typeable::Typeable, z3_checker, BinOp, Expression, Identifier, Lit::*, Options, RuntimeType::{self, *}, SourcePos::UnknownPosition, SymResult, SymbolTable
};

use super::{ concrete_execution::ConcreteExecution, execution_tree::sym_exec_execution_tree};

pub(crate) enum FuzzerType{
    SAGE,
    AFL,
    INCREMENTAL,
    EXPERIMENTAL
}

pub(crate) trait Fuzz {
    fn fuzz_inputs(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, coverage: Option<Vec<(u64,u64)>>, found_negations: &mut Option<&mut Vec<Rc<Expression>>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, requirements: Option<Rc<Expression>>) -> Vec<Rc<Expression>>;
    fn fuzz_inputs_from_negations(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, negations: &mut Vec<Rc<Expression>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, fuzzed_inputs: Vec<Rc<Expression>>) -> Vec<Rc<Expression>>;
    fn set_latest_input(&mut self, inputs: Vec<Rc<Expression>>);
    fn get_latest_input(&self) -> Vec<Rc<Expression>>;
}

impl Fuzz for RandomFuzzer{

    fn get_latest_input(&self) -> Vec<Rc<Expression>> {
        self.prev_inputs.clone()
    }

    fn set_latest_input(&mut self, inputs: Vec<Rc<Expression>>) {
        self.prev_inputs = inputs.to_owned();
    }

    fn fuzz_inputs_from_negations(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, negations: &mut Vec<Rc<Expression>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, fuzzed_inputs: Vec<Rc<Expression>>) -> Vec<Rc<Expression>> {
        assert!(negations.len() > 0); // Should be handled in Some call
        let expr = negations.pop().unwrap();
        let mut new_constraints: Vec<Rc<Expression>> = Vec::new();
        let (_, solve_str) = z3_checker::all_z3::verify(expr.deref(), &am);

        let new_values: Vec<&str> = solve_str.split("\n").filter(|s| s.len() > 0).collect();
        let mut constrained_inputs = HashSet::new();

        for value_comb in new_values{
            let key_value: Vec<&str> = value_comb.split(" -> ").collect();
            constrained_inputs.insert(key_value[0]);
            assert!(key_value.len() == 2);
            
            let pair: Vec<(&Identifier, &Rc<Expression>)> = inputs.into_iter().filter(|(k, _)| k.as_str() == *key_value.first().unwrap()).collect();
            if pair.len() != 1 {
                // Maybe input wasn't found because its an array type.
                let new_id = Identifier::from(key_value[0]);
                let rhs= Rc::new(Expression::Lit { lit: IntLit { int_value: key_value[1].parse::<i64>().unwrap() }, type_ : IntRuntimeType, info: UnknownPosition });                            
                new_constraints.push(self.create_input_expression(IntRuntimeType, rhs, &new_id));
            } else {
                if let ArrayRuntimeType { .. } = pair[0].1.type_of()  { continue; }
                let constr = self.create_constraint(*pair.first().unwrap(), ( key_value.first().unwrap().to_string(), key_value.last().unwrap().to_string()));
                new_constraints.push(constr);
            }
        }

        fuzzed_inputs.clone().into_iter().filter(|x| {
            match x.as_ref() {
                Expression::BinOp {lhs, .. } => {
                    match lhs.as_ref() {
                        Expression::SymbolicVar { var, .. } => {
                            if constrained_inputs.contains(var.as_str()) { false } else { true }
                        },
                        _ => true
                    }
                },
                _ => true
            }
        }).for_each(|x| new_constraints.push(x));

        new_constraints
    }

    fn fuzz_inputs(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>, _coverage: Option<Vec<(u64,u64)>>, found_negations: &mut Option<&mut Vec<Rc<Expression>>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, requirements: Option<Rc<Expression>>) -> Vec<Rc<Expression>>{
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
                    _t@ArrayRuntimeType { .. } => // We assume only Int arrays are allowed since other arrays are not implemented yet (?)
                    {
                        if requirements.is_none() {todo!("Figure out how to fuzz array with unknown size")}
                        
                        if let Some(expr) = requirements.borrow() {
                            let array_size_range = get_array_size(expr.clone(), id);
                            assert!(array_size_range.is_some());
                            // This solving could be optimized. Lot CAN go wrong
                            let (_, solve_str) = z3_checker::all_z3::verify(array_size_range.unwrap().deref(), &am);
                            let clean_str = solve_str.replace(&[' ','\n'][..], "");
                            let size = clean_str.split("->").collect::<Vec<&str>>().last().unwrap().parse::<i64>().unwrap();
                            
                            // Constrain all elements with random input
                            for i in 0..size {
                                let new_id = Identifier::from(format!("{}{i}", id.as_str()));
                                let rhs= Rc::new(Expression::Lit { lit: IntLit { int_value: self.rng.gen::<i64>() }, type_ : IntRuntimeType, info: UnknownPosition });                            
                                fuzzed_inputs.push(self.create_input_expression(IntRuntimeType, rhs, &new_id));
                            }
                        }
                    },
                    UnknownRuntimeType => panic!("Cannot fuzz unknown input!"),
                    VoidRuntimeType => panic!("Cannot fuzz void input!"),
                    t@_ => todo!("Fuzzing of type: '{:?}' is not implemented!",t)
                }
            }
        );

        if let Some(paths) = found_negations{
            if paths.len() > 0 {
                return self.fuzz_inputs_from_negations(inputs, *paths, am, fuzzed_inputs);
            }
        }
        *found_negations = None;

        fuzzed_inputs
    }

}

pub(crate) struct RandomFuzzer {
    rng: ThreadRng,
    charset: [u8; 73],
    prev_inputs: Vec<Rc<Expression>>,
}

impl RandomFuzzer{
    pub(crate) fn new() -> Self {
        Self {
            rng: rand::thread_rng(),
            charset: *b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789)(*&^%$#@!~",
            prev_inputs: Vec::new(),
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
    prev_found_transitions: &mut HashSet<(u64, u64)>,
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
    let mut stuck_counter = 0;
    let mut requirements = None;
    let StackFrame { current_member, .. } = state.stack.current_stackframe().unwrap();
            if let Some((requires, _type_guard)) = current_member.requires() {
                requirements = Some(requires.clone());
            }
    let stack_variables = state.stack.current_variables().unwrap();
    let alias_map: im_rc::HashMap<Identifier, crate::exec::AliasEntry> = state.alias_map.clone();
    let mut fuzzed_inputs = fuzzer.fuzz_inputs(stack_variables, None, found_negations, alias_map.clone(), requirements.clone());
    let mut new_options = options.clone();
    new_options.prune_path_z3 = true;
    let mut total_found_transitions = prev_found_transitions;

    loop{
        // Constraint inputs via initial seed
        let now = Instant::now();
        let mut loc_state = state.clone();
        for input in fuzzed_inputs.clone(){
            loc_state.constraints.insert(input);
        }
        println!("Inputs in concrete: {:?}", fuzzed_inputs);
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
        println!("Conceretely executed in {:?} seconds", now.elapsed().as_secs());
        match res {
            SymResult::Valid => {
                let mut found_new_transitions = false;
                heuristic.coverage_tuples.clone().into_iter().for_each(|k| {if total_found_transitions.insert(k) { found_new_transitions = true } });
                if found_new_transitions { stuck_counter = 0; fuzzer.set_latest_input(fuzzed_inputs.clone()); } else { stuck_counter += 1  };

                // When stuck return the trace
                // println!("Stuck counter: {:?}", stuck_counter);
                if stuck_counter > 5 { return Either::Right(fuzzer.get_latest_input()) };
                // Choose new fuzzing inputs (random or based on other inputs)
                fuzzed_inputs = fuzzer.fuzz_inputs(stack_variables, Some(heuristic.coverage_tuples), found_negations, alias_map.clone(), requirements.clone());
            },
            // Return Invalid when violation is found
            SymResult::Invalid(..) => return Either::Left(res),
        }
        // Repeat untill stuck
    }
}

