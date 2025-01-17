use crate::typing::types::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug)]
pub struct ConstrInfo {
    pub associated_data: String,
    pub op_type: OpType,
}

#[derive(Debug)]
pub struct Module {
    pub data_defs: HashMap<String, DataDef>,
    pub op_defs: HashMap<String, OpDef>,
}

impl Module {
    pub fn new(data_defs: HashMap<String, DataDef>, op_defs: HashMap<String, OpDef>) -> Self {
        Module { data_defs, op_defs }
    }
}

#[derive(Debug)]
pub struct DataDef {
    pub params: Vec<String>,
    pub constrs: HashMap<String, DataConstr>,
    pub span: Span,
}

#[derive(Debug)]
pub struct DataConstr {
    pub params: Vec<Type>,
    pub span: Span,
}

#[derive(Debug)]
pub struct OpDef {
    pub ann: OpType,
    pub body: Body,
    pub span: Span,
}

#[derive(Debug)]
pub enum Body {
    Body(Vec<Op>),
    Constructor(String),
    Primitive,
}

#[derive(Debug, Clone)]
pub enum Op {
    Literal {
        value: Literal,
        span: Span,
    },
    Name {
        value: String,
        span: Span,
    },
    Quote {
        value: Vec<Op>,
        span: Span,
    },
    Case {
        head_arm: CaseArm,
        arms: Vec<CaseArm>,
        span: Span,
    },
}

impl Op {
    // TODO: smth like SpannedOp instead of this
    pub fn get_span(&self) -> &Span {
        match self {
            Op::Literal { span, .. } => span,
            Op::Name { span, .. } => span,
            Op::Quote { span, .. } => span,
            Op::Case { span, .. } => span,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i32),
}

#[derive(Debug, Clone)]
pub struct CaseArm {
    pub constr: String,
    pub body: Vec<Op>,
}
