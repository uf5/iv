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
        m.insert(
            "exec",
            OpType {
                pre: vec![
                    Type::Op(OpType {
                        pre: vec![Type::Poly("a".to_owned())],
                        post: vec![Type::Poly("b".to_owned())],
                    }),
                    Type::Poly("a".to_owned()),
                ],
                post: vec![Type::Poly("b".to_owned())],
            },
        );
        m.insert(
            "comp",
            OpType {
                pre: vec![
                    Type::Op(OpType {
                        pre: vec![Type::Poly("b".to_owned())],
                        post: vec![Type::Poly("c".to_owned())],
                    }),
                    Type::Op(OpType {
                        pre: vec![Type::Poly("a".to_owned())],
                        post: vec![Type::Poly("b".to_owned())],
                    }),
                ],
                post: vec![Type::Op(OpType {
                    pre: vec![Type::Poly("a".to_owned())],
                    post: vec![Type::Poly("c".to_owned())],
                })],
            },
        );
        m
    };
}

fn parse_parametric(prefix: &'static str, name: &str) -> Option<usize> {
    name.strip_prefix(prefix)?.parse().ok()
}

fn get_bury(name: &str) -> Option<OpType> {
    let n = parse_parametric("br-", name)?;
    let tau = gen_prelude_type("tau", 0);
    let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
    let pre = once(&tau).chain(alpha.iter()).cloned().collect();
    let post = alpha.iter().chain(once(&tau)).cloned().collect();
    Some(OpType { pre, post })
}

fn get_dig(name: &str) -> Option<OpType> {
    let n = parse_parametric("dg-", name)?;
    let tau = gen_prelude_type("tau", 0);
    let alpha: Vec<Type> = (0..n).map(|i| gen_prelude_type("alpha", i)).collect();
    let pre = alpha.iter().chain(once(&tau)).cloned().collect();
    let post = once(&tau).chain(alpha.iter()).cloned().collect();
    Some(OpType { pre, post })
}

fn get_pack(name: &str) -> Option<OpType> {
    let n = parse_parametric("pack-", name)?;
    let elems: Vec<Type> = (0..n).map(|i| gen_prelude_type("elem", i)).collect();
    let tuple = elems.iter().cloned().fold(Type::mono_unit(), |acc, v| {
        Type::App(
            Box::new(Type::App(Box::new(Type::mono_tuple()), Box::new(v))),
            Box::new(acc),
        )
    });
    Some(OpType {
        pre: elems,
        post: vec![tuple],
    })
}

fn get_unpack(name: &str) -> Option<OpType> {
    let n = parse_parametric("unpack-", name)?;
    let elems: Vec<Type> = (0..n).map(|i| gen_prelude_type("elem", i)).collect();
    let tuple = elems.iter().cloned().fold(Type::mono_unit(), |acc, v| {
        Type::App(
            Box::new(Type::App(Box::new(Type::mono_tuple()), Box::new(v))),
            Box::new(acc),
        )
    });
    Some(OpType {
        pre: vec![tuple],
        post: elems,
    })
}

fn get_parametric(name: &str) -> Option<OpType> {
    get_bury(name)
        .or_else(|| get_dig(name))
        .or_else(|| get_pack(name))
        .or_else(|| get_unpack(name))
}

pub fn get(name: &str) -> Option<OpType> {
    PRELUDE_OP_TYPES
        .get(name)
        .cloned()
        .or_else(|| get_parametric(name))
}
