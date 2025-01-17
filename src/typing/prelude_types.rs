use super::types::*;
use lazy_static::lazy_static;
use std::collections::HashMap;

lazy_static! {
    pub static ref PRELUDE_OP_TYPES: HashMap<&'static str, OpType> = {
        let mut m = HashMap::new();
        m.insert(
            "dup",
            OpType {
                pre: vec![Type::Poly("a".to_owned())],
                post: vec![Type::Poly("a".to_owned()), Type::Poly("a".to_owned())],
            },
        );
        m.insert(
            "swap",
            OpType {
                pre: vec![Type::Poly("a".to_owned()), Type::Poly("b".to_owned())],
                post: vec![Type::Poly("b".to_owned()), Type::Poly("a".to_owned())],
            },
        );
        m
    };
}
