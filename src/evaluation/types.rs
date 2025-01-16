use crate::syntax::ast::*;

#[derive(Debug)]
pub enum EvaluatorError {
    NoMain,
    MainIsAConstructor,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Value {
    User {
        constr_name: String,
        args: Vec<Value>,
    },
    Quote {
        ops: Vec<Op>,
    },
}
