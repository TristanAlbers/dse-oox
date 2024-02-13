use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use std::convert::TryFrom;

use z3::{
    ast::Bool,
    ast::{Ast, Int},
    Config, Context, SatResult, Solver,
};

use crate::{
    syntax::{BinOp, Expression, Identifier, Lit, RuntimeType, UnOp},
    typeable::Typeable,
};

pub mod concretization {
    use super::*;

    /// Verify one of the concretized expressions produced by concretization.rs.
    ///
    /// Since in a concretized expression the symbolic references are replaced by concrete references, we assume that expression contains no symbolic references.
    pub fn verify(expression: &Expression) -> SatResult {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);

        let solver = Solver::new(&ctx);
        let z3_assertion = expression_to_z3_node(&ctx, expression);
        solver.assert(&z3_assertion);
        solver.check()
    }
}

/// A different approach where we don't concretize the expression but leave it up to Z3
/// This starts off by initialising for each symbolic object (used in the expression), a Z3 set of their concrete values.
/// Then we add a Z3 constraint that the symbolic object is one of the values in the set.
pub mod all_z3 {
    use z3::Sort;

    use crate::exec::alias_map::AliasMap;

    use super::*;

    pub fn verify<'a>(expression: &Expression, alias_map: &AliasMap) -> (SatResult, String) {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);

        let solver = Solver::new(&ctx);
        let int_sort = Sort::int(&ctx);

        let (symbolic_variables, literals, symbolic_refs) = super::symbolic_variables(expression);

        let id_to_z3_node =
            super::id_to_z3_node(&ctx, &symbolic_variables, &literals, &symbolic_refs);

        for (symbolic_ref_name, alias_entry) in alias_map
            .iter()
            .filter(|(id, _)| symbolic_refs.contains(id))
        {
            let symbolic_ref =
                Int::try_from(id_to_z3_node[&NodeEntry::sym_ref(symbolic_ref_name)].clone())
                    .unwrap();

            let mut set = z3::ast::Set::empty(&ctx, &int_sort);

            for alias in &alias_entry.aliases {
                if **alias == Expression::NULL {
                    set = set.add(&z3::ast::Int::from_i64(&ctx, 0));
                } else {
                    let ref_ = alias.expect_reference().unwrap();
                    set = set.add(&z3::ast::Int::from_i64(&ctx, ref_));
                }
            }
            solver.assert(&set.member(&symbolic_ref));
        }

        let z3_assertion = expr_to_z3(expression, &id_to_z3_node);
        solver.assert(&Bool::try_from(z3_assertion).unwrap());

        // println!("{}", solver.to_string());
        let res = solver.check();

        let str;

        if let Some(model) = solver.get_model() {
            str = model.to_string();
        } else {
            str = "None Model".to_string();
        }

        (res, str)
    }
}

enum IntOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

enum IntExpr {
    Value(i64),
    Op(IntOp, Box<IntExpr>, Box<IntExpr>),
    Cond(BE, Box<IntExpr>, Box<IntExpr>),
}

enum BoolOp {
    And,
    Or,
    Implies,
}

enum BE {
    Value(i64),
    Op(BoolOp, Box<IntExpr>, Box<IntExpr>),
    Cond(Box<BE>, Box<BE>, Box<BE>),
}

#[derive(Clone)]
enum AstNode<'ctx> {
    Bool(Bool<'ctx>),
    Int(Int<'ctx>),
}

impl<'ctx> AstNode<'ctx> {
    fn add(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? + Int::try_from(other)?))
    }

    fn sub(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? - Int::try_from(other)?))
    }

    fn mul(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? * Int::try_from(other)?))
    }

    fn div(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? / Int::try_from(other)?))
    }

    fn _mod(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Int(Int::try_from(self)? % Int::try_from(other)?))
    }

    fn eq(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        match self {
            AstNode::Bool(b) => Ok(AstNode::Bool(b._eq(&Bool::try_from(other)?))),
            AstNode::Int(i) => Ok(AstNode::Bool(i._eq(&Int::try_from(other)?))),
        }
    }

    fn lt(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.lt(&Int::try_from(other)?),
        ))
    }

    fn gt(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.gt(&Int::try_from(other)?),
        ))
    }

    fn lte(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.le(&Int::try_from(other)?),
        ))
    }

    fn gte(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Int::try_from(self)?.ge(&Int::try_from(other)?),
        ))
    }

    fn and(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        let ctx = self.get_ctx();
        Ok(AstNode::Bool(Bool::and(
            ctx,
            &[&Bool::try_from(self)?, &Bool::try_from(other)?],
        )))
    }

    fn or(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        let ctx = self.get_ctx();
        Ok(AstNode::Bool(Bool::or(
            ctx,
            &[&Bool::try_from(self)?, &Bool::try_from(other)?],
        )))
    }

    fn implies(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        Ok(AstNode::Bool(
            Bool::try_from(self)?.implies(&Bool::try_from(other)?),
        ))
    }

    fn conditional(self, true_: AstNode<'ctx>, false_: AstNode<'ctx>) -> Result<AstNode<'ctx>, ()> {
        let guard = Bool::try_from(self)?;

        guard.ite(&guard, &guard);
        match true_ {
            AstNode::Bool(true_) => Ok(AstNode::Bool(guard.ite(&true_, &Bool::try_from(false_)?))),
            AstNode::Int(true_) => Ok(AstNode::Int(guard.ite(&true_, &Int::try_from(false_)?))),
        }
    }

    fn neq(self, other: AstNode<'ctx>) -> Result<AstNode, ()> {
        match self {
            AstNode::Bool(b) => Ok(AstNode::Bool(!b._eq(&Bool::try_from(other)?))),
            AstNode::Int(i) => Ok(AstNode::Bool(!i._eq(&Int::try_from(other)?))),
        }
    }

    fn negate(self) -> Result<AstNode<'ctx>, ()> {
        Ok(AstNode::Bool(Bool::try_from(self)?.not()))
    }
}

impl<'ctx> AstNode<'ctx> {
    fn get_ctx(&self) -> &'ctx Context {
        match self {
            AstNode::Bool(v) => v.get_ctx(),
            AstNode::Int(v) => v.get_ctx(),
        }
    }
}

impl<'ctx> TryFrom<AstNode<'ctx>> for Bool<'ctx> {
    type Error = ();

    fn try_from(value: AstNode<'ctx>) -> Result<Self, Self::Error> {
        if let AstNode::Bool(v) = value {
            Ok(v)
        } else {
            Err(())
        }
    }
}
impl<'ctx> TryFrom<AstNode<'ctx>> for Int<'ctx> {
    type Error = ();

    fn try_from(value: AstNode<'ctx>) -> Result<Self, Self::Error> {
        if let AstNode::Int(v) = value {
            Ok(v)
        } else {
            Err(())
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum NodeEntry<'a> {
    Lit(Lit),
    Var(Cow<'a, str>),
    SymbolicRef(Cow<'a, str>),
}

impl<'a> NodeEntry<'a> {
    fn var(s: &'a str) -> NodeEntry {
        NodeEntry::Var(Cow::Borrowed(s))
    }
    fn sym_ref(s: &'a str) -> NodeEntry {
        NodeEntry::SymbolicRef(Cow::Borrowed(s))
    }
}

// Assuming that expression is a boolean type
fn expression_to_z3_node<'ctx>(ctx: &'ctx Context, expression: &Expression) -> Bool<'ctx> {
    assert!(expression.type_of() == RuntimeType::BoolRuntimeType);

    // dbg!(expression);
    let (symbolic_variables, literals, symbolic_refs) = symbolic_variables(expression);
    assert!(symbolic_refs.is_empty());
    // dbg!(&literals);
    let id_to_z3_node = symbolic_variables
        .into_iter()
        .map(|(id, type_)| match type_ {
            RuntimeType::BoolRuntimeType => (
                NodeEntry::Var(Cow::Owned(id.clone().into())),
                AstNode::Bool(Bool::new_const::<String>(ctx, id.into())),
            ),
            RuntimeType::IntRuntimeType => (
                NodeEntry::Var(Cow::Owned(id.clone().into())),
                AstNode::Int(Int::new_const::<String>(ctx, id.into())),
            ),
            _ => todo!(),
        })
        .chain(literals.into_iter().map(|lit| {
            let z3_node = match &lit {
                Lit::BoolLit { bool_value } => AstNode::Bool(Bool::from_bool(ctx, *bool_value)),
                Lit::IntLit { int_value } => AstNode::Int(Int::from_i64(ctx, *int_value)),
                Lit::NullLit => AstNode::Int(Int::from_i64(ctx, 0)),
                _ => todo!(),
            };
            (NodeEntry::Lit(lit), z3_node)
        }))
        .collect::<HashMap<_, _>>();

    // generate all possible concrete expressions from symbolic references.

    let ast_node = expr_to_z3(expression, &id_to_z3_node);

    Bool::try_from(ast_node).unwrap()
}

/// Turns an OOX expression into a Z3 expression
fn expr_to_z3<'ctx>(
    expression: &Expression,
    vars: &HashMap<NodeEntry, AstNode<'ctx>>,
) -> AstNode<'ctx> {
    match expression {
        Expression::SymbolicVar { var, type_, .. } => match type_ {
            RuntimeType::BoolRuntimeType => vars.get(&NodeEntry::var(var)).unwrap().clone(),
            RuntimeType::IntRuntimeType => vars.get(&NodeEntry::var(var)).unwrap().clone(),
            _ => todo!(),
        },
        Expression::BinOp {
            bin_op, lhs, rhs, ..
        } => match bin_op {
            BinOp::And => AstNode::and(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::Or => AstNode::or(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::Equal => AstNode::eq(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::GreaterThan => {
                AstNode::gt(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap()
            }
            BinOp::GreaterThanEqual => {
                AstNode::gte(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap()
            }
            BinOp::LessThan => AstNode::lt(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::LessThanEqual => {
                AstNode::lte(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap()
            }

            BinOp::Implies => {
                AstNode::implies(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap()
            }
            BinOp::Minus => AstNode::sub(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::Plus => AstNode::add(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::Multiply => AstNode::mul(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::NotEqual => AstNode::neq(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::Divide => AstNode::div(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
            BinOp::Modulo => AstNode::_mod(expr_to_z3(lhs, vars), expr_to_z3(rhs, vars)).unwrap(),
        },

        Expression::UnOp { un_op, value, .. } => match un_op {
            UnOp::Negative => todo!(),
            UnOp::Negate => AstNode::negate(expr_to_z3(value, vars)).unwrap(),
        },
        Expression::Lit { lit, .. } => vars.get(&NodeEntry::Lit(lit.clone())).unwrap().clone(),
        Expression::Ref { ref_, .. } => {
            // dbg!(*ref_);
            vars.get(&NodeEntry::Lit(Lit::IntLit { int_value: *ref_ }))
                .unwrap()
                .clone()
        }
        Expression::Conditional {
            guard,
            true_,
            false_,
            ..
        } => AstNode::conditional(
            expr_to_z3(guard, vars),
            expr_to_z3(true_, vars),
            expr_to_z3(false_, vars),
        )
        .unwrap(),
        Expression::SymbolicRef { var, .. } => vars.get(&NodeEntry::sym_ref(var)).unwrap().clone(),
        _ => todo!(),
    }
}

/// Return all symbolic variables, literals and symbolic references in the expression.
fn symbolic_variables(
    expression: &Expression,
) -> (
    HashSet<(Identifier, RuntimeType)>,
    HashSet<Lit>,
    HashSet<Identifier>,
) {
    let mut variables = HashSet::new();
    let mut literals = HashSet::new();
    let mut symbolic_refs = HashSet::new();

    fn helper(
        variables: &mut HashSet<(Identifier, RuntimeType)>,
        literals: &mut HashSet<Lit>,
        symbolic_refs: &mut HashSet<Identifier>,
        expression: &Expression,
    ) {
        match expression {
            Expression::BinOp { lhs, rhs, .. } => {
                helper(variables, literals, symbolic_refs, lhs);
                helper(variables, literals, symbolic_refs, rhs);
            }
            Expression::UnOp { value, .. } => {
                helper(variables, literals, symbolic_refs, value);
            }
            Expression::Conditional {
                guard,
                true_,
                false_,
                ..
            } => {
                helper(variables, literals, symbolic_refs, guard);
                helper(variables, literals, symbolic_refs, true_);
                helper(variables, literals, symbolic_refs, false_);
            }
            Expression::SymbolicVar { var, type_, .. } => {
                variables.insert((var.clone(), type_.clone()));
            }
            Expression::Lit { lit, .. } => {
                literals.insert(lit.clone());
            } // Lits are handled elsewhere
            Expression::Ref { ref_, .. } => {
                literals.insert(Lit::IntLit { int_value: *ref_ });
            }
            Expression::SymbolicRef { var, .. } => {
                symbolic_refs.insert(var.to_owned());
            }
            _ => todo!("Yet to figure out: {:?}", expression),
        }
    }

    helper(
        &mut variables,
        &mut literals,
        &mut symbolic_refs,
        expression,
    );

    (variables, literals, symbolic_refs)
}

fn id_to_z3_node<'a>(
    ctx: &'a Context,
    symbolic_variables: &HashSet<(Identifier, RuntimeType)>,
    literals: &HashSet<Lit>,
    symbolic_refs: &HashSet<Identifier>,
) -> HashMap<NodeEntry<'a>, AstNode<'a>> {
    symbolic_variables
        .iter()
        .map(|(id, type_)| match type_ {
            RuntimeType::BoolRuntimeType => (
                NodeEntry::Var(Cow::Owned(id.clone().into())),
                AstNode::Bool(Bool::new_const::<String>(ctx, id.to_string())),
            ),
            RuntimeType::IntRuntimeType => (
                NodeEntry::Var(Cow::Owned(id.clone().into())),
                AstNode::Int(Int::new_const::<String>(ctx, id.to_string())),
            ),
            _ => todo!(),
        })
        .chain(literals.iter().map(|lit| {
            let z3_node = match &lit {
                Lit::BoolLit { bool_value } => AstNode::Bool(Bool::from_bool(ctx, *bool_value)),
                Lit::IntLit { int_value } => AstNode::Int(Int::from_i64(ctx, *int_value)),
                Lit::NullLit => AstNode::Int(Int::from_i64(ctx, 0)),
                _ => todo!(),
            };
            (NodeEntry::Lit(lit.clone()), z3_node)
        }))
        .chain(symbolic_refs.iter().map(|sym_ref| {
            let z3_node = AstNode::Int(z3::ast::Int::new_const::<String>(ctx, sym_ref.to_string()));
            (
                NodeEntry::SymbolicRef(Cow::Owned(sym_ref.to_string())),
                z3_node,
            )
        }))
        .collect::<HashMap<_, _>>()
}
