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
    UnknownConstructor(String),
    NotAConstructor(String),
    DuplicateConstructor,
    NotAllConstructorsCovered,
    DifferentData(String),
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

    pub fn infer(&mut self) -> Err<HashMap<String, OpType>> {
        let mut inferred_map = HashMap::new();
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
            inferred_map.insert(op_name.clone(), inf.apply(&s));
        }
        Ok(inferred_map)
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

    /// Unify two types. t1 has priority over t2, i.e., (Poly(v), t) is picked over (t, Poly(v)).
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
        let (
            OpType {
                pre: pre1,
                post: post1,
            },
            OpType {
                pre: pre2,
                post: post2,
            },
        ) = self.balance_op_stack_lengths(o1.clone(), o2.clone());
        // ensure that the two types have the same size of pre and post stacks
        if pre1.len() != pre2.len() || post1.len() != post2.len() {
            return Err(InferenceError::UnificationError(
                Type::Op(o1.clone()),
                Type::Op(o2.clone()),
            ));
        }
        // unify stacks
        let s1 = self.unify_list(Subst::new(), &pre1, &pre2)?;
        self.unify_list(s1, &post1, &post2)
    }

    /// Perform nop-expansion on op type pre and post.
    fn balance_op_stack_lengths(&mut self, mut o1: OpType, mut o2: OpType) -> (OpType, OpType) {
        while o1.pre.len() < o2.pre.len() && o1.post.len() < o2.post.len() {
            let new_var = self.gen_name();
            o1.pre.push(new_var.clone());
            o1.post.push(new_var.clone());
        }
        while o2.pre.len() < o1.pre.len() && o2.post.len() < o1.post.len() {
            let new_var = self.gen_name();
            o2.pre.push(new_var.clone());
            o2.post.push(new_var.clone());
        }
        (o1, o2)
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

    fn ti_case_arm<'a>(&'a mut self, arm: &CaseArm) -> Err<(&'a DataDef, Subst, OpType)> {
        let constr = self
            .module
            .op_defs
            .get(&arm.constr)
            .ok_or_else(|| InferenceError::UnknownConstructor(arm.constr.to_owned()))?;
        let Body::Constructor(data_name) = &constr.body else {
            return Err(InferenceError::NotAConstructor(arm.constr.clone()));
        };
        let Some(data_def) = self.module.data_defs.get(data_name) else {
            unreachable!();
        };
        let destr_op_type = OpType {
            pre: constr.ann.post.clone(),
            post: constr.ann.pre.clone(),
        };
        let (s1, body_optype) = self.ti(&arm.body)?;
        let arm_body_post_destr_instantiated = self.instantiate_op(&destr_op_type);
        let (s2, chained_optype) = self.chain(&arm_body_post_destr_instantiated, &body_optype)?;
        let s = compose(&s2, &s1);
        let chained_optype_applied = chained_optype.apply(&s);
        Ok((data_def, s, chained_optype_applied))
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
            Op::Case(head_arm, arms) => {
                // the head case arm which dictates which type would be matched, and what would
                // be the output type
                let (_head_dd, _, mut ot) = self.ti_case_arm(head_arm)?;
                let mut s = Subst::new();
                for arm in arms {
                    let (_arm_dd, _, mut arm_ot) = self.ti_case_arm(arm)?;
                    (ot, arm_ot) = self.balance_op_stack_lengths(ot, arm_ot);
                    let new_s = self.unify_op(&ot, &arm_ot)?;
                    s = compose(&new_s, &s);
                    ot = ot.apply(&s);
                }
                Ok((s, ot))
            }
        }
    }

    /// Chain two operator types through unification. This includes overflow and underflow chain.
    fn chain(&mut self, ot1: &OpType, ot2: &OpType) -> Err<(Subst, OpType)> {
        let OpType {
            pre: alpha,
            post: beta,
        } = ot1;
        let OpType {
            pre: gamma,
            post: delta,
        } = ot2;
        let s = self.unify_list(Subst::new(), &beta, &gamma)?;
        if beta.len() >= gamma.len() {
            // overflow chain
            let beta_skip_gamma = beta.iter().skip(gamma.len());
            let pre = alpha.iter().map(|t| t.apply(&s)).collect();
            let post = delta
                .iter()
                .chain(beta_skip_gamma)
                .map(|t| t.apply(&s))
                .collect();
            Ok((s, OpType { pre, post }))
        } else {
            // underflow chain
            let gamma_skip_beta = gamma.iter().skip(beta.len());
            let pre = alpha
                .iter()
                .chain(gamma_skip_beta)
                .map(|t| t.apply(&s))
                .collect();
            let post = delta.iter().map(|t| t.apply(&s)).collect();
            Ok((s, OpType { pre, post }))
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
        let input = "
        define [a, a] nocadd [a]: 1 2 3.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn subst_int_ann_vs_inf() {
        let input = "
        data Alpha:.
        define [a, a] nocadd [a]:.
        define [Alpha, Alpha] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn ann_ss_pre() {
        let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [a, Alpha] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_post() {
        let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [Alpha, a] intadd [Alpha]: nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_double() {
        let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [a, a] intadd [Alpha]: nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_trans_stack() {
        let input = "
        data Alpha: alpha.
        data Beta: beta.
        define [a] nocdup [a, a]:.
        define [Alpha] intadd [Beta, Beta]: nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn ann_ss_trans_stack_ok() {
        let input = "
        data Alpha:. data Beta:.
        data Gamma:. define [a, b, c] nocfoobar [c, b, a]:.
        define [Alpha, Beta, Gamma] intadd [Gamma, Beta, Apha]: nocfoobar.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn uf_triple_add_ok() {
        let input = "
        define [a, a] nocadd [a]:.
        define [a, a, a] tripleadd [a]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn uf_triple_add_ok_spec() {
        let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Alpha] tripleadd [Alpha]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn uf_triple_add_ok_err1() {
        let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Alpha] tripleadd [a]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn uf_triple_add_ok_err2() {
        let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Beta] tripleadd [Alpha]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn of_triple1() {
        let input = "
        data Alpha:. data Beta:.
        define [a] nocdup [a, a]:.
        define [a] tripledup [a, a, a]: nocdup nocdup.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn op_triple2() {
        let input = "
        data Alpha:. data Beta:.
        define [a, a] nocadd [a]:.
        define [a] nocdup [a, a]:.
        define [a] tripledup [a, a, a]: nocdup nocdup nocadd nocdup.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn int_add_uf_chain() {
        let input = "
        data Alpha: alpha. define [a, a] nocadd [a]:.
        define [Alpha] alphainc [Alpha]: alpha nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn int_add_datapoly() {
        let input = "
        data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either Alpha b]: alpha left.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_ok());
    }

    #[test]
    fn int_add_datapoly_err() {
        let input = "
        data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either a Alpha]: alpha left.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).infer().is_err());
    }

    #[test]
    fn case_maybe_nat() {
        let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Maybe Nat] incnatmaybe [Maybe Nat]: case { just { suc just }, nothing { nothing } }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn case_maybe_nat_add_nop_expansion_err() {
        let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { just { nocswap nocdup nocdup nocrot nocnatadd just }, nothing { nothing } }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn case_maybe_nat_add_nop_expansion() {
        let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { just { nocswap nocdup nocrot nocnatadd just }, nothing { nothing } }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn case_maybe_nat_add_nop_expansion_arms_swapped() {
        let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { nothing { nothing }, just { nocswap nocdup nocrot nocnatadd just } }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn case_maybe_nat_add_nop_expansion_wrong_constr() {
        let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        data Either a b: [a] left, [b] right.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { just { nocswap nocdup nocrot nocnatadd just }, left { nothing } }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn nop_unification_test() {
        let input = "
        define [a] nocnop [a]:. define [] nop []: nocnop.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn nop_unification_test_err_poly() {
        let input = "
        define [a] nocnonop [a, a]:.
        define [] nop []: nocnonop.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn nop_unification_test_err_mono() {
        let input = "
        data Alpha: alpha.
        data Beta: beta.
        define [Alpha] nocnonop [Beta]:.
        define [] nop []: nocnonop.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn nop_unification_test_complex() {
        let input = "
        data Maybe a: [a] just, nothing.
        data Nat: [Nat] suc, zero.
        define [Maybe Nat, Nat] nocfoobar [Maybe Nat, Nat]:.
        define [Maybe Nat] nop [Maybe Nat]: nocfoobar.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).infer();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }
}
