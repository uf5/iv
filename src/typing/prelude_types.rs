use super::types::*;
use std::iter::once;

fn gen_prelude_type(prefix: &str, i: usize) -> Type {
    Type::Poly(format!("_prelude_{}_{}", prefix, i))
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

fn get_basic(s: &str) -> Option<OpType> {
    match s {
        "dup" => Some(OpType {
            pre: vec![Type::Poly("a".to_owned())],
            post: vec![Type::Poly("a".to_owned()), Type::Poly("a".to_owned())],
        }),
        "pop" => Some(OpType {
            pre: vec![Type::Poly("a".to_owned())],
            post: vec![],
        }),
        "quote" => Some(OpType {
            pre: vec![Type::Poly("a".to_owned())],
            post: vec![Type::Op(OpType {
                pre: vec![],
                post: vec![Type::Poly("a".to_owned())],
            })],
        }),
        _ => None,
    }
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
    let [a_pre_n, a_post_n, b_pre_n, b_post_n] = parse_parametric("comp-", s)?;

    let (tail_n, overlap_n) = if a_post_n >= b_pre_n {
        // overflow chain
        (a_post_n - b_pre_n, b_pre_n)
    } else {
        // underflow chain
        (b_pre_n - a_post_n, a_post_n)
    };

    let a_pre: Vec<_> = (0..a_pre_n).map(|i| gen_prelude_type("a_pre", i)).collect();
    let b_post: Vec<_> = (0..b_post_n)
        .map(|i| gen_prelude_type("b_post", i))
        .collect();
    let overlap: Vec<_> = (0..overlap_n)
        .map(|i| gen_prelude_type("overlap", i))
        .collect();
    let tail: Vec<_> = (0..tail_n).map(|i| gen_prelude_type("tail", i)).collect();

    let (a, b, composed) = if a_post_n >= b_pre_n {
        // overflow chain

        // [a_pre] [overlap * tail] , [overlap] [b_post]
        // [a_pre] [b_post * tail]

        (
            OpType {
                pre: a_pre.clone(),
                post: overlap
                    .iter()
                    .cloned()
                    .chain(tail.iter().cloned())
                    .collect(),
            },
            OpType {
                pre: overlap.clone(),
                post: b_post.clone(),
            },
            OpType {
                pre: a_pre.clone(),
                post: b_post.iter().cloned().chain(tail.iter().cloned()).collect(),
            },
        )
    } else {
        // underflow chain

        // [a_pre] [overlap] , [overlap * tail] [b_post]
        // [a_pre * tail] [b_post]

        (
            OpType {
                pre: a_pre.clone(),
                post: overlap.clone(),
            },
            OpType {
                pre: overlap
                    .iter()
                    .cloned()
                    .chain(tail.iter().cloned())
                    .collect(),
                post: b_post.clone(),
            },
            OpType {
                pre: a_pre.iter().cloned().chain(tail.iter().cloned()).collect(),
                post: b_post.clone(),
            },
        )
    };

    Some(OpType {
        pre: vec![Type::Op(b), Type::Op(a)],
        post: vec![Type::Op(composed)],
    })
}

fn get_exec(s: &str) -> Option<OpType> {
    let [pre_n, post_n] = parse_parametric("exec-", s)?;
    let pre: Vec<_> = (0..pre_n).map(|i| gen_prelude_type("pre", i)).collect();
    let post: Vec<_> = (0..post_n).map(|i| gen_prelude_type("post", i)).collect();
    Some(OpType {
        pre: once(Type::Op(OpType {
            pre: pre.clone(),
            post: post.clone(),
        }))
        .chain(pre)
        .collect(),
        post: post.clone(),
    })
}

fn get_parametric(s: &str) -> Option<OpType> {
    get_bury(s)
        .or_else(|| get_dig(s))
        .or_else(|| get_comp(s))
        .or_else(|| get_exec(s))
}

pub fn get(s: &str) -> Option<OpType> {
    get_basic(s).or_else(|| get_parametric(s))
}
