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

fn parse_parametric<const N: usize>(prefix: &str, s: &str) -> Option<[usize; N]> {
    let rest = s.strip_prefix(prefix)?;
    rest.split('-')
        .map(str::parse)
        .collect::<Result<Vec<_>, _>>()
        .ok()?
        .try_into()
        .ok()
}

fn get_bury(s: &str) -> Option<OpType> {
    let [n] = parse_parametric("br-", s)?;
    let tau = gen_prelude_type("tau", 0);
    let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
    let pre = once(&tau).chain(alpha.iter()).cloned().collect();
    let post = alpha.iter().chain(once(&tau)).cloned().collect();
    Some(OpType { pre, post })
}

fn get_dig(s: &str) -> Option<OpType> {
    let [n] = parse_parametric("dg-", s)?;
    let tau = gen_prelude_type("tau", 0);
    let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
    let pre = alpha.iter().chain(once(&tau)).cloned().collect();
    let post = once(&tau).chain(alpha.iter()).cloned().collect();
    Some(OpType { pre, post })
}

fn get_comp(s: &str) -> Option<OpType> {
    let [a_pre, a_post, b_pre, b_post] = parse_parametric("comp-", s)?;
    todo!()
}

fn get_exec(s: &str) -> Option<OpType> {
    let [pre, post] = parse_parametric("exec-", s)?;
    todo!()
}

fn get_parametric(s: &str) -> Option<OpType> {
    get_bury(s)
        .or_else(|| get_dig(s))
        .or_else(|| get_comp(s))
        .or_else(|| get_exec(s))
}

pub fn get(s: &str) -> Option<OpType> {
    PRELUDE_OP_TYPES
        .get(s)
        .cloned()
        .or_else(|| get_parametric(s))
}
