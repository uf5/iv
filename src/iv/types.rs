use std::collections::HashMap;

#[derive(Debug)]
pub struct Module {
    pub data_defs: HashMap<String, DataDef>,
    pub op_defs: HashMap<String, OpDef>,
}

#[derive(Debug)]
pub struct DataDef {
    pub params: Vec<String>,
    pub constructors: HashMap<String, DataConstr>,
}

#[derive(Debug)]
pub struct DataConstr {
    pub params: Vec<Type>,
}

#[derive(Debug)]
pub enum Type {
    Mono(String),
    Poly(String),
    Op(OpType),
    App(Box<Type>, Box<Type>),
}

#[derive(Debug)]
pub struct OpType {
    pub pre: Vec<Type>,
    pub post: Vec<Type>,
}

#[derive(Debug)]
pub struct OpDef {
    pub ann: OpType,
    pub body: Body,
}

#[derive(Debug)]
pub enum Body {
    Body(Vec<Op>),
    Constructor,
}

#[derive(Debug)]
pub enum Op {
    Literal(Literal),
    Name(String),
    Case(Vec<CaseArm>),
}

#[derive(Debug)]
pub enum Literal {
    Int(i32),
}

#[derive(Debug)]
pub struct CaseArm {
    pub constr: String,
    pub body: Vec<Op>,
}
