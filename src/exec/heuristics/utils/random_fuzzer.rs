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

impl Fuzz for RandomFuzzer{

    fn get_latest_input(&self) -> Vec<Rc<Expression>> {
        self.prev_inputs.clone()
    }

    fn set_latest_input(&mut self, inputs: Vec<Rc<Expression>>) {
        self.prev_inputs = inputs.to_owned();
        // println!("Updated last input to: {:?}", inputs)
    }

    fn fuzz_inputs_from_negations(&mut self, state: &mut State, inputs: &HashMap<Identifier, Rc<Expression>>, negations: &mut Vec<Rc<Expression>>, am: im_rc::HashMap<Identifier, crate::exec::AliasEntry>, fuzzed_inputs: Vec<Rc<Expression>>) -> Vec<Rc<Expression>> {
        assert!(negations.len() > 0); // Should be handled in Some call

        // Solve expression with Z3
        let expr = negations.pop().unwrap();
        let mut new_constraints: Vec<Rc<Expression>> = Vec::new();
        let (_, solve_str) = z3_checker::all_z3::verify(expr.deref(), &am);
        let new_values: Vec<&str> = solve_str.split("\n").filter(|s| s.len() > 0).collect();
        let mut constrained_inputs = HashSet::new();

        // Parse Z3 solutions from string to inputs
        for value_comb in new_values{
            let key_value: Vec<&str> = value_comb.split(" -> ").collect();
            constrained_inputs.insert(key_value[0]);
            assert!(key_value.len() == 2);
            let clean_value_str = key_value[1].replace(&[' ','\n','(', ')'][..], "");
            
            let pair: Vec<(&Identifier, &Rc<Expression>)> = inputs.into_iter().filter(|(k, _)| k.as_str() == *key_value.first().unwrap()).collect();
            if pair.len() != 1 {
                // Maybe input wasn't found because its an array type.
                let start = key_value[0].chars().position(|x| x.is_digit(10)).unwrap();
                let index = key_value[0][start..].parse::<i64>().unwrap();
                let array_name = &key_value[0][0..start];

                let ref_ = state
                .stack
                .lookup(&Identifier::from(array_name))
                .unwrap_or_else(|| panic!("array {:?} was not found on the stack", array_name));

                let type_ = ref_.type_of();

                let ref_ = single_alias_elimination(ref_.clone(), &state.alias_map)
                .expect_reference()
                .unwrap_or_else(|| panic!("expected array ref, found expr {:?}", &ref_));

                let new_id = Identifier::from(key_value[0]);
                let rhs;
                match type_ {
                    ArrayRuntimeType { inner_type} => {
                        match *inner_type {
                            t@IntRuntimeType => rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: clean_value_str.parse::<i64>().unwrap() }, type_ : t, info: UnknownPosition }),
                            FloatRuntimeType => todo!(),
                            t@BoolRuntimeType => rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: clean_value_str.parse::<bool>().unwrap() }, type_ : t, info: UnknownPosition }),
                            t@CharRuntimeType => rhs = Rc::new(Expression::Lit { lit: CharLit { char_value: clean_value_str.parse::<char>().unwrap() }, type_ : t, info: UnknownPosition }),
                            t => panic!("Unimplemented array type: {:?}", t),
                        };
                    },
                    t => panic!("Expected array type but found: {:?}", t),
                }
                // let rhs= Rc::new(Expression::Lit { lit: IntLit { int_value: clean_value_str.parse::<i64>().unwrap() }, type_ : IntRuntimeType, info: UnknownPosition });  

                write_elem_concrete_index(state, ref_, index, rhs.clone());
                new_constraints.push(self.create_input_expression(rhs.type_of(), rhs, &new_id));

            } else {
                if let ArrayRuntimeType { .. } = pair[0].1.type_of()  { continue; }
                let constr = self.create_constraint(state, *pair.first().unwrap(), clean_value_str);
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
                match ex.type_of() {
                    t@IntRuntimeType => {
                        let value = self.rng.gen::<i16>(); // Could be from mutator
                        let rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: i64::from(value) }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@UIntRuntimeType =>{
                        let value = self.rng.gen::<u16>();
                        let rhs = Rc::new(Expression::Lit { lit: UIntLit { uint_value: u64::from(value) }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@CharRuntimeType =>{
                        let idx = self.rng.gen_range(0..self.charset.len());
                        let value = self.charset[idx] as char;
                        let rhs = Rc::new(Expression::Lit { lit: CharLit { char_value: value }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@BoolRuntimeType => {
                        let value = self.rng.gen_bool(0.5);
                        let rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: value }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs.clone(), id));
                        new_state.stack.insert_variable(id.clone(), rhs);
                    },
                    t@FloatRuntimeType => {
                        let value = NotNan::new(self.rng.gen::<f64>()).unwrap();
                        let rhs = Rc::new(Expression::Lit { lit: FloatLit { float_value: value }, type_ : t.clone(), info: UnknownPosition });
                        fuzzed_inputs.push(self.create_input_expression(t, rhs.clone(), id));
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
                                    rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: self.rng.gen::<i64>() }, type_ : IntRuntimeType, info: UnknownPosition })
                                } else if *inner_type == BoolRuntimeType {
                                    rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: self.rng.gen_bool(0.5) }, type_ : BoolRuntimeType, info: UnknownPosition })
                                } else {
                                    panic!("Inner array type not implemented: {:?}", *inner_type);
                                }                   
                                write_elem_concrete_index(&mut new_state, ref_, i as i64, rhs.clone());
                                fuzzed_inputs.push(self.create_input_expression(rhs.type_of(), rhs, &new_id));
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

    pub(crate) fn create_constraint(&mut self, state: &mut State, (id, expr): (&Identifier, &Rc<Expression>), new_value: String) -> Rc<Expression>{
        match expr.type_of() {
            t@IntRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: IntLit { int_value: new_value.parse::<i64>().expect(&format!("Parsing Error {:?}", new_value)) }, type_ : t.clone(), info: UnknownPosition });
                state.stack.insert_variable(id.clone(), rhs.clone());
                self.create_input_expression(t, rhs, id)
            },
            t@UIntRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: UIntLit { uint_value: new_value.parse::<u64>().expect(&format!("Parsing Error {:?}", new_value)) }, type_ : t.clone(), info: UnknownPosition });
                state.stack.insert_variable(id.clone(), rhs.clone());
                self.create_input_expression(t, rhs, id)
            },
            t@CharRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: CharLit { char_value: new_value.parse::<char>().expect(&format!("Parsing Error {:?}", new_value)) }, type_ : t.clone(), info: UnknownPosition });
                state.stack.insert_variable(id.clone(), rhs.clone());
                self.create_input_expression(t, rhs, id)
            },
            t@BoolRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: BoolLit { bool_value: new_value.parse::<bool>().expect(&format!("Parsing Error {:?}", new_value)) }, type_ : t.clone(), info: UnknownPosition });
                state.stack.insert_variable(id.clone(), rhs.clone());
                self.create_input_expression(t, rhs, id)
            },
            t@FloatRuntimeType => 
            {
                let rhs = Rc::new(Expression::Lit { lit: FloatLit { float_value: NotNan::new(new_value.parse::<f64>().expect(&format!("Parsing Error {:?}", new_value))).unwrap() }, type_ : t.clone(), info: UnknownPosition });
                state.stack.insert_variable(id.clone(), rhs.clone());
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
