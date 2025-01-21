use super::types::*;
use lazy_static::lazy_static;
use regex::Regex;
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
            "swap",
            OpType {
                pre: vec![Type::Poly("a".to_owned()), Type::Poly("b".to_owned())],
                post: vec![Type::Poly("b".to_owned()), Type::Poly("a".to_owned())],
            },
        );
        m
    };
    static ref RE_PARAMETRIC: Regex = Regex::new(r"^([a-z]+)-([\d]+)$").unwrap();
    static ref MAP_PARAMETRIC: HashMap<&'static str, fn(usize) -> OpType> = {
        let mut m = HashMap::new();
        m.insert(
            "br",
            (|n| {
                let tau = gen_prelude_type("tau", 0);
                let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
                let pre = once(&tau).chain(alpha.iter()).cloned().collect();
                let post = alpha.iter().chain(once(&tau)).cloned().collect();
                OpType { pre, post }
            }) as fn(usize) -> OpType,
        );
        m.insert(
            "dg",
            (|n| {
                let tau = gen_prelude_type("tau", 0);
                let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
                let pre = alpha.iter().chain(once(&tau)).cloned().collect();
                let post = once(&tau).chain(alpha.iter()).cloned().collect();
                OpType { pre, post }
            }) as fn(usize) -> OpType,
        );
        m
    };
}

fn parse_parametric(name: &str) -> Option<(&str, usize)> {
    let caps = RE_PARAMETRIC.captures(name)?;
    let op_name = caps.get(1).unwrap().as_str();
    let param = caps.get(2).unwrap().as_str().parse().unwrap();
    Some((op_name, param))
}

fn get_parametric(name: &str) -> Option<OpType> {
    let (op_name, param) = parse_parametric(name)?;

    Some(MAP_PARAMETRIC.get(op_name)?(param))
}

pub fn get(name: &str) -> Option<OpType> {
    PRELUDE_OP_TYPES
        .get(name)
        .cloned()
        .or_else(|| get_parametric(name))
}
