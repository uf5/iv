use super::types::*;
use lazy_static::lazy_static;
use std::collections::HashMap;

lazy_static! {
    static ref PRELUDE_OP_TYPES: HashMap<&'static str, OpType> = {
        let mut m = HashMap::new();
        m.insert(
            "dup",
            OpType {
                pre: vec![],
                post: vec![],
            },
        );
        m
    };
}
