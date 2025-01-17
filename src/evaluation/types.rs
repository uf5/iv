use crate::syntax::ast::*;

#[derive(Debug)]
pub enum EvaluatorError {
    NoMain,
}

#[derive(Debug)]
pub enum Value {
    User {
        constr_name: String,
        args: Vec<Value>,
    },
    Quote {
        ops: Vec<Op>,
    },
}
