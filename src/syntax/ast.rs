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
    pub constructor_info: HashMap<String, ConstrInfo>,
}

impl Module {
    pub fn new(data_defs: HashMap<String, DataDef>, op_defs: HashMap<String, OpDef>) -> Self {
        let constructor_info = data_defs
            .iter()
            .flat_map(|(data_name, data_def)| {
                let constructed_mono = Type::Mono(data_name.to_owned());
                let constructed_type = data_def
                    .params
                    .iter()
                    .cloned()
                    .fold(constructed_mono, |a, x| {
                        Type::App(Box::new(a), Box::new(Type::Poly(x)))
                    });
                data_def
                    .constrs
                    .iter()
                    .map(move |(constr_name, constr_def)| {
                        (
                            constr_name.clone(),
                            ConstrInfo {
                                associated_data: data_name.clone(),
                                op_type: OpType {
                                    pre: constr_def.params.clone(),
                                    post: vec![constructed_type.clone()],
                                },
                            },
                        )
                    })
            })
            .collect();
        Module {
            data_defs,
            op_defs,
            constructor_info,
        }
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
