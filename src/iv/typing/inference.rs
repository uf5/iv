use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::zip;

use crate::iv::types::*;

#[derive(Debug)]
pub enum InferenceError {
    AnnInfConflict(OpType, OpType),
    UnificationError(Type, Type),
    OccursCheckError(String, Type),
    UnknownOp(String),
    ChainError,
}

type Err<T> = Result<T, InferenceError>;

type Subst = HashMap<String, Type>;

fn compose(s1: &Subst, s2: &Subst) -> Subst {
    s2.iter()
        .map(|(v, t)| (v.to_owned(), t.apply(s1)))
        .chain(s1.clone().into_iter())
        .collect()
}

trait Typeable {
    fn ftv(&self) -> HashSet<String>;
    fn apply(&self, subst: &Subst) -> Self;
}

impl Typeable for Type {
    fn ftv(&self) -> HashSet<String> {
        match self {
            Type::Mono(_) => HashSet::new(),
            Type::Poly(v) => HashSet::from([v.clone()]),
            Type::Op(op_type) => op_type.ftv(),
            Type::App(t1, t2) => {
                let mut f = t1.ftv();
                f.extend(t2.ftv().into_iter());
                f
            }
        }
    }

    fn apply(&self, subst: &Subst) -> Self {
        match self {
            Type::Mono(_) => self.clone(),
            Type::Poly(v) => match subst.get(v) {
                Some(t) => t.clone(),
                None => self.clone(),
            },
            Type::Op(op_type) => Type::Op(op_type.apply(subst)),
            Type::App(t1, t2) => Type::App(Box::new(t1.apply(subst)), Box::new(t2.apply(subst))),
        }
    }
}

impl Typeable for OpType {
    fn ftv(&self) -> HashSet<String> {
        self.pre
            .iter()
            .chain(self.post.iter())
            .flat_map(Typeable::ftv)
            .collect()
    }

    fn apply(&self, subst: &Subst) -> Self {
        let pre = self.pre.iter().map(|t| t.apply(subst)).collect();
        let post = self.post.iter().map(|t| t.apply(subst)).collect();
        OpType { pre, post }
    }
}

pub struct Inference<'m> {
    pub module: &'m Module,
    counter: usize,
}

impl<'m> Inference<'m> {
    pub fn new(module: &'m Module) -> Self {
        Inference { module, counter: 0 }
    }

    pub fn infer(&mut self) -> Err<()> {
        for (op_name, op_def) in self.module.op_defs.iter() {
            if op_name.starts_with("noc") {
                continue;
            }
            let Body::Body(ref body) = op_def.body else {
                continue;
            };
            let (_, inf) = self.ti(&body)?;
            let s = self.unify_op(&op_def.ann, &inf)?;
            // ann matches the inf when all subs values are poly
            for v in op_def.ann.ftv().iter().filter_map(|t| s.get(t)) {
                match v {
                    Type::Poly(_) => (),
                    _ => Err(InferenceError::AnnInfConflict(
                        op_def.ann.clone(),
                        inf.clone(),
                    ))?,
                }
            }
        }
        Ok(())
    }

    fn gen_name(&mut self) -> Type {
        let name = format!("gen_{}", self.counter);
        self.counter += 1;
        Type::Poly(name)
    }

    fn instantiate_op(&mut self, op: &OpType) -> OpType {
        let new_var_subst = op
            .ftv()
            .iter()
            .map(|v| (v.to_owned(), self.gen_name()))
            .collect();
        op.apply(&new_var_subst)
    }

    fn unify(&mut self, t1: &Type, t2: &Type) -> Err<Subst> {
        match (t1, t2) {
            (Type::Mono(m1), Type::Mono(m2)) if m1 == m2 => Ok(Subst::new()),
            (Type::Mono(_), Type::Mono(_)) => {
                Err(InferenceError::UnificationError(t1.clone(), t2.clone()))
            }
            (Type::Poly(v1), Type::Poly(v2)) if v1 == v2 => Ok(Subst::new()),
            (Type::Poly(v), t) | (t, Type::Poly(v)) => {
                if t.ftv().contains(v) {
                    Err(InferenceError::OccursCheckError(v.clone(), t.clone()))
                } else {
                    Ok(Subst::from([(v.clone(), t.clone())]))
                }
            }
            (Type::App(l1, r1), Type::App(l2, r2)) => {
                let s1 = self.unify(l1, l2)?;
                let s2 = self.unify(&r1.apply(&s1), &r2.apply(&s1))?;
                Ok(compose(&s2, &s1))
            }
            (Type::Op(o1), Type::Op(o2)) => self.unify_op(o1, o2),
            (_, _) => Err(InferenceError::UnificationError(t1.clone(), t2.clone())),
        }
    }

    /// Performs unification on two slices.
    /// Performs min(l1.len(), l2.len()) unifications.
    fn unify_list(&mut self, s: Subst, l1: &[Type], l2: &[Type]) -> Err<Subst> {
        zip(l1.iter(), l2.iter()).try_fold(s, |s_acc, (t1, t2)| {
            Ok(compose(
                &self.unify(&t1.apply(&s_acc), &t2.apply(&s_acc))?,
                &s_acc,
            ))
        })
    }

    fn unify_op(&mut self, o1: &OpType, o2: &OpType) -> Err<Subst> {
        let OpType {
            pre: pre1,
            post: post1,
        } = o1;
        let OpType {
            pre: pre2,
            post: post2,
        } = o2;
        // ensure that the two types have the same size of pre and post stacks
        if pre1.len() != pre2.len() || post1.len() != post2.len() {
            return Err(InferenceError::UnificationError(
                Type::Op(o1.clone()),
                Type::Op(o2.clone()),
            ));
        }
        // unify stacks
        let s1 = self.unify_list(Subst::new(), pre1, pre2)?;
        self.unify_list(s1, post1, post2)
    }

    fn ti_lit(&self, lit: &Literal) -> OpType {
        let lit_type = match lit {
            Literal::Int(_) => Type::Mono("Int".to_owned()),
        };
        OpType {
            pre: vec![],
            post: vec![lit_type],
        }
    }

    fn ti_op(&mut self, op: &Op) -> Err<(Subst, OpType)> {
        match op {
            Op::Literal(lit) => Ok((Subst::new(), self.ti_lit(lit))),
            Op::Name(n) => {
                let op_def = self
                    .module
                    .op_defs
                    .get(n)
                    .ok_or_else(|| InferenceError::UnknownOp(n.clone()))?;
                Ok((Subst::new(), self.instantiate_op(&op_def.ann)))
            }
            Op::Case(_arms) => todo!(),
        }
    }

    fn chain(&mut self, ot1: &OpType, ot2: &OpType) -> Err<(Subst, OpType)> {
        if ot1.post.len() <= ot2.pre.len() {
            let OpType {
                pre: alpha,
                post: beta,
            } = ot1;
            let OpType {
                pre: beta_gamma,
                post: delta,
            } = ot2;
            let s = self.unify_list(Subst::new(), beta_gamma, beta)?;
            let alpha_gamma_applied = alpha
                .iter()
                .chain(beta_gamma.iter().skip(beta.len()))
                .map(|t| t.apply(&s))
                .collect();
            let delta_applied = delta.iter().map(|t| t.apply(&s)).collect();
            Ok((
                s,
                OpType {
                    pre: alpha_gamma_applied,
                    post: delta_applied,
                },
            ))
        } else {
            let OpType {
                pre: alpha,
                post: beta_gamma,
            } = ot1;
            let OpType {
                pre: beta,
                post: delta,
            } = ot2;
            let s = self.unify_list(Subst::new(), beta_gamma, beta)?;
            let alpha_applied = alpha.iter().map(|t| t.apply(&s)).collect();
            let delta_gamma_applied = delta
                .iter()
                .chain(beta_gamma.iter().skip(beta.len()))
                .map(|t| t.apply(&s))
                .collect();
            Ok((
                s,
                OpType {
                    pre: alpha_applied,
                    post: delta_gamma_applied,
                },
            ))
        }
    }

    fn ti(&mut self, ops: &[Op]) -> Err<(Subst, OpType)> {
        match ops {
            [] => Ok((Subst::new(), OpType::empty())),
            [o, os @ ..] => {
                let (s1, t1) = self.ti_op(o)?;
                let (s2, t2) = self.ti(os)?;
                let (s3, t3) = self.chain(&t1, &t2)?;
                let s = compose(&s3, &compose(&s2, &s1));
                let t = t3.apply(&s);
                Ok((s, t))
            }
        }
    }
}

/// Test suite designed around the "noc" nocheck prefix. That allows creating different scenarios
/// in the inference process.
#[cfg(test)]
mod noc_tests {
    use crate::iv::syntax::parse;
    use crate::iv::typing::inference::*;

    #[test]
    fn sanity() {
        let input = "define [a, a] nocadd [a]: 1 2 3.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn subst_int_ann_vs_inf() {
        let input = "data Alpha:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn ann_ss_pre() {
        let input = "data Alpha:. define [a, a] nocadd [a]:.
        define [a, Alpha] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_post() {
        let input = "data Alpha:. define [a, a] nocadd [a]:.
        define [Alpha, a] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_double() {
        let input = "data Alpha:. define [a, a] nocadd [a]:.
        define [a, a] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_trans_stack() {
        let input = "data Alpha:. data Beta:. define [a] nocdup [a, a]:.
        define [Alpha] intadd [Beta, Beta]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_trans_stack_ok() {
        let input = "data Alpha:. data Beta:. data Gamma:. define [a, b, c] nocfoobar [c, b, a]:.
        define [Alpha, Beta, Gamma] intadd [Gamma, Beta, Apha]: nocfoobar.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn int_add_uf_chain() {
        let input = "data Alpha: alpha. define [a, a] nocadd [a]:.
        define [Alpha] alphainc [Alpha]: alpha nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn int_add_datapoly() {
        let input = "data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either Alpha b]: alpha left.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn int_add_datapoly_err() {
        let input = "data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either a Alpha]: alpha left.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }
}
