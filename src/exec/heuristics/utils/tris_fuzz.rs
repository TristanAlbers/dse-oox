use std::{borrow::Borrow, collections::{HashMap, HashSet}, ops::Deref, rc::Rc};

use ordered_float::NotNan;
use rand::{rngs::ThreadRng, Rng};

use crate::{
    exec::{
        array_initialisation, 
        heuristics::fuzzer::Fuzz, 
        single_alias_elimination, 
        write_elem_concrete_index, 
        State
    },
    typeable::Typeable, 
    z3_checker, 
    BinOp, 
    Expression, 
    Identifier, 
    Lit::*, 
    RuntimeType::{self, *}, 
    SourcePos::UnknownPosition,
    SymbolTable
};

impl Fuzz for AFLFuzzer{

    fn get_latest_input(&self) -> Vec<Rc<Expression>> {
        self.prev_inputs.clone()
    }

    fn set_latest_input(&mut self, inputs: Vec<Rc<Expression>>) {
        self.prev_inputs = inputs.to_owned();
    }

    fn fuzz_inputs_from_negations(&mut self, state: &mut State, inputs: &HashMap<Identifier, Rc<Expression>>, negations: &mut Vec<Rc<Expression>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, fuzzed_inputs: Vec<Rc<Expression>>) -> Vec<Rc<Expression>> {
        todo!();
    }

    fn fuzz_inputs(
        &mut self, 
        state: &State, 
        inputs: &HashMap<Identifier, Rc<Expression>>, 
        max_array_size: u64, 
        found_negations: &mut Option<&mut Vec<Rc<Expression>>>,
        am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, 
        requirements: Option<Rc<Expression>>, 
        st: &SymbolTable
    ) -> (Vec<Rc<Expression>>, State){
        let mut fuzzed_inputs: Vec<Rc<Expression>> = Vec::new();
        let mut new_state = state.clone();
        inputs.into_iter().for_each(
            |(id, ex)|
            {
                let mutator = self.get_mutator();
                match ex.type_of() {
                    t@IntRuntimeType => {
                        let value = mutator.mutate_i64(None); // Could be from mutator
                        let rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: value }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.symbolicvar_equal_expr(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@UIntRuntimeType =>{
                        let value = mutator.mutate_u64(None);
                        let rhs = Rc::new(Expression::Lit { lit: UIntLit { uint_value: value }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.symbolicvar_equal_expr(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@CharRuntimeType =>{
                        let value = mutator.mutate_char(None);
                        let rhs = Rc::new(Expression::Lit { lit: CharLit { char_value: value }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.symbolicvar_equal_expr(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@BoolRuntimeType => {
                        let value = mutator.mutate_bool(None);
                        let rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: value }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.symbolicvar_equal_expr(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@FloatRuntimeType => {
                        let value = mutator.mutate_float(None);
                        let rhs = Rc::new(Expression::Lit { lit: FloatLit { float_value: NotNan::new(value).unwrap() }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.symbolicvar_equal_expr(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@ArrayRuntimeType { .. } => { // We assume only Int arrays are allowed since other arrays are not implemented yet (?)
                        if requirements.is_none() {todo!("Figure out how to fuzz array with unknown size")}
                        
                        if let Some(_expr) = requirements.borrow() {
                            let size = max_array_size;
                            
                            // Constrain all elements with random input
                            let inner_type = match t.clone() {
                                RuntimeType::ArrayRuntimeType { inner_type } => inner_type,
                                _ => panic!("Expected array type, found {:?}", t),
                            };

                            array_initialisation(&mut new_state, id, size, t, *inner_type.clone(), st);

                            let ref_ = new_state
                                .stack
                                .lookup(id)
                                .unwrap_or_else(|| panic!("array {:?} was not found on the stack", id));

                            let ref_ = single_alias_elimination(ref_.clone(), &new_state.alias_map)
                                .expect_reference()
                                .unwrap_or_else(|| panic!("expected array ref, found expr {:?}", &ref_));

                            for i in 0..size {
                                let new_id = Identifier::from(format!("{}{i}", id.as_str()));
                                let rhs;
                                if *inner_type == IntRuntimeType {
                                    let value = mutator.mutate_i64(None);
                                    rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: value }, type_ : IntRuntimeType, info: UnknownPosition })
                                } else if *inner_type == BoolRuntimeType {
                                    let value = mutator.mutate_bool(None);
                                    rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: value }, type_ : BoolRuntimeType, info: UnknownPosition })
                                } else {
                                    panic!("Inner array type not implemented: {:?}", *inner_type);
                                }                   
                                write_elem_concrete_index(&mut new_state, ref_, i as i64, rhs.clone());
                                fuzzed_inputs.push(self.symbolicvar_equal_expr(rhs.type_of(), rhs, &new_id));
                            }
                        }
                    },
                    UnknownRuntimeType => panic!("Cannot fuzz unknown input!"),
                    VoidRuntimeType => panic!("Cannot fuzz void input!"),
                    t@_ => println!("Fuzzing of type: '{:?}' is not implemented!",t),
                }
            }
        );

        if let Some(paths) = found_negations{
            if paths.len() > 0 {
                fuzzed_inputs = self.fuzz_inputs_from_negations(&mut new_state, inputs, *paths, am, fuzzed_inputs);
            } else {
                *found_negations = None;
            }
        }        

        (fuzzed_inputs, new_state)
    }

}

pub(crate) struct AFLFuzzer {
    rng: ThreadRng,
    charset: [u8; 73],
    prev_inputs: Vec<Rc<Expression>>,
    mutators: Vec<Box<dyn Mutator>>
}

impl AFLFuzzer{
    pub(crate) fn new() -> Self {
        Self {
            rng: rand::thread_rng(),
            charset: *b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789)(*&^%$#@!~",
            prev_inputs: Vec::new(),
            mutators: Vec::new()
        }
    }    

    fn symbolicvar_equal_expr(&self, var_type: RuntimeType, rhs: Rc<Expression>, id: &Identifier ) -> Rc<Expression> {
        Rc::new(Expression::BinOp { 
            bin_op: BinOp::Equal, 
            lhs: Rc::new(Expression::SymbolicVar { var: id.clone(), type_: var_type.clone(), info: UnknownPosition }), 
            rhs, 
            type_: var_type.clone(), 
            info: UnknownPosition 
        })
    }

    fn get_mutator(&mut self) -> Box<dyn Mutator> {
        // Some decision procedure can be implemented here
        self.mutators.pop().unwrap()
    }
}

pub(crate) trait Mutator {
    fn mutate_i64(&self, input: Option<i64>) -> i64;
    fn mutate_u64(&self, input: Option<u64>) -> u64;
    fn mutate_bool(&self, input: Option<bool>) -> bool;
    fn mutate_char(&self, input: Option<char>) -> char;
    fn mutate_float(&self, input: Option<f64>) -> f64;
}
