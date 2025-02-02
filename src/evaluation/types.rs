use crate::syntax::ast::*;

#[derive(Debug)]
pub enum EvaluatorError {
    NoMain,
}

#[derive(Debug, Clone)]
pub enum Value {
    User {
        constr_name: String,
        args: Vec<Value>,
    },
    Quoted(Quoted),
}

#[derive(Clone, Debug)]
pub enum Quoted {
    Sentence { ops: Vec<Op> },
    Value { value: Box<Value> },
    Composed { a: Box<Quoted>, b: Box<Quoted> },
}
