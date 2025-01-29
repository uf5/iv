use super::types::*;
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::iter::once;

fn gen_prelude_type(prefix: &str, i: usize) -> Type {
    Type::Poly(format!("_prelude_{}_{}", prefix, i))
}

lazy_static! {
    static ref PRELUDE_OP_TYPES: HashMap<&'static str, OpType> = {
        let mut m = HashMap::new();
        m.insert(
            "dup",
            OpType {
                pre: vec![Type::Poly("a".to_owned())],
                post: vec![Type::Poly("a".to_owned()), Type::Poly("a".to_owned())],
            },
        );
        m.insert(
            "pop",
            OpType {
                pre: vec![Type::Poly("a".to_owned())],
                post: vec![],
            },
        );
        m.insert(
            "quote",
            OpType {
                pre: vec![Type::Poly("a".to_owned())],
                post: vec![Type::Op(OpType {
                    pre: vec![],
                    post: vec![Type::Poly("a".to_owned())],
                })],
            },
        );
        m
    };
}

fn parse_bury(name: &str) -> Option<usize> {
    name.strip_prefix("br-")?.parse().ok()
}

fn get_bury(name: &str) -> Option<OpType> {
    let n = parse_bury(name)?;
    let tau = gen_prelude_type("tau", 0);
    let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
    let pre = once(&tau).chain(alpha.iter()).cloned().collect();
    let post = alpha.iter().chain(once(&tau)).cloned().collect();
    Some(OpType { pre, post })
}

fn parse_dig(name: &str) -> Option<usize> {
    name.strip_prefix("dg-")?.parse().ok()
}

fn get_dig(name: &str) -> Option<OpType> {
    let n = parse_dig(name)?;
    let tau = gen_prelude_type("tau", 0);
    let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
    let pre = alpha.iter().chain(once(&tau)).cloned().collect();
    let post = once(&tau).chain(alpha.iter()).cloned().collect();
    Some(OpType { pre, post })
}

fn get_parametric(name: &str) -> Option<OpType> {
    get_bury(name).or_else(|| get_dig(name))
}

pub fn get(name: &str) -> Option<OpType> {
    PRELUDE_OP_TYPES
        .get(name)
        .cloned()
        .or_else(|| get_parametric(name))
}
