use crate::typing::types::*;
use std::collections::HashMap;

#[derive(Debug)]
pub struct Module {
    pub data_defs: HashMap<String, DataDef>,
    pub op_defs: HashMap<String, OpDef>,
}

impl Module {
    /// Creates a new module with the constructors of the user defined data types mirrored as op definitions.
    pub fn new(data_defs: HashMap<String, DataDef>, op_defs: HashMap<String, OpDef>) -> Self {
        let op_defs = {
            // prelude with fixed-length arguments
            let prelude_fixed = vec![
                (
                    String::from("dup"),
                    OpDef {
                        ann: OpType {
                            pre: vec![Type::Poly(String::from("a"))],
                            post: vec![
                                Type::Poly(String::from("a")),
                                Type::Poly(String::from("a")),
                            ],
                        },
                        body: Body::Primitive,
                    },
                ),
                (
                    String::from("swap"),
                    OpDef {
                        ann: OpType {
                            pre: vec![Type::Poly(String::from("a")), Type::Poly(String::from("b"))],
                            post: vec![
                                Type::Poly(String::from("b")),
                                Type::Poly(String::from("a")),
                            ],
                        },
                        body: Body::Primitive,
                    },
                ),
                (
                    String::from("quote"),
                    OpDef {
                        ann: OpType {
                            pre: vec![Type::Poly(String::from("a"))],
                            post: vec![Type::Op(OpType {
                                pre: vec![],
                                post: vec![Type::Poly(String::from("a"))],
                            })],
                        },
                        body: Body::Primitive,
                    },
                ),
            ]
            .into_iter();
            // user defined ops
            let op_defs = op_defs.into_iter();
            // constructors as ops
            let constr_defs = data_defs.iter().flat_map(
                |(
                    data_name,
                    DataDef {
                        params: data_params,
                        constrs,
                    },
                )| {
                    // construct a resulting type from the constructor
                    let post_type = data_params
                        .iter()
                        .fold(Type::Mono(data_name.to_owned()), |lhs, rhs| {
                            Type::App(Box::new(lhs), Box::new(Type::Poly(rhs.to_owned())))
                        });
                    // create op definitions from constructors
                    constrs
                        .iter()
                        .map(move |(constr_name, DataConstr { params })| {
                            (
                                constr_name.to_owned(),
                                OpDef {
                                    ann: OpType {
                                        pre: params.clone(),
                                        post: vec![(&post_type).clone()],
                                    },
                                    body: Body::Constructor(data_name.to_owned()),
                                },
                            )
                        })
                },
            );
            prelude_fixed.chain(op_defs).chain(constr_defs).collect()
        };
        Module { data_defs, op_defs }
    }
}

#[derive(Debug)]
pub struct DataDef {
    pub params: Vec<String>,
    pub constrs: HashMap<String, DataConstr>,
}

#[derive(Debug)]
pub struct DataConstr {
    pub params: Vec<Type>,
}

#[derive(Debug)]
pub struct OpDef {
    pub ann: OpType,
    pub body: Body,
}

#[derive(Debug)]
pub enum Body {
    Body(Vec<Op>),
    Constructor(String),
    Primitive,
}

#[derive(Debug, Clone)]
pub enum Op {
    Literal(Literal),
    Name(String),
    Quote(Vec<Op>),
    Case(CaseArm, Vec<CaseArm>),
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
