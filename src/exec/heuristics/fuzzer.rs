use std::{collections::HashMap, rc::Rc };

use ordered_float::NotNan;
use rand::{rngs::ThreadRng, Rng};

use crate::{
    Lit::*,
    typeable::Typeable, 
    BinOp, 
    Expression, 
    Identifier, 
    RuntimeType::{self, *}, 
    SourcePos::UnknownPosition,
};

pub(crate) enum FuzzerType{
    SAGE,
    AFL,
    INCREMENTAL,
    EXPERIMENTAL
}

pub(crate) struct Fuzzer {
    kind: FuzzerType,
    rng: ThreadRng,
    charset: [u8; 73]
}

impl Fuzzer{
    pub(crate) fn new(kind: FuzzerType) -> Fuzzer {
        Fuzzer{
            kind,
            rng: rand::thread_rng(),
            charset: *b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789)(*&^%$#@!~"
        }
    }

    pub(crate) fn fuzz_inputs(&mut self, inputs: &HashMap<Identifier, Rc<Expression>>) -> Vec<Rc<Expression>>{
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
                    _ => panic!("Fuzzing of this type is not implemented!")
                }
            }
        );
        fuzzed_inputs
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

// pub(crate) fn expression_to_value(xpr: Rc<Expression>) -> () {
//     match xpr.as_ref() {

//     }
// }
