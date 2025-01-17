use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::zip;

use super::prelude_types;
use super::types::*;
use crate::syntax::ast::*;

#[derive(Debug)]
pub struct InferenceError {
    pub span: Span,
    pub error: InferenceErrorMessage,
}

#[derive(Debug)]
pub enum InferenceErrorMessage {
    AnnInfConflict(OpType, OpType),
    UnificationError(Type, Type),
    OccursCheckError(String, Type),
    UnknownOp(String),
    ChainError,
    UnknownConstructor(String),
    DuplicateConstructor(String),
    NotAllConstructorsCovered,
    ConstructorBelongsToDifferentData(String),
}

type Subst = HashMap<String, Type>;

fn compose(s1: Subst, s2: Subst) -> Subst {
    let mut s: Subst = s1.into_iter().map(|(v, t)| (v, t.apply(&s2))).collect();
    s.extend(s2);
    s
}

trait Typeable {
    fn ftv(&self) -> HashSet<String>;
    fn apply(self, subst: &Subst) -> Self;
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

    fn apply(self, subst: &Subst) -> Self {
        match self {
            Type::Mono(_) => self.clone(),
            Type::Poly(v) => match subst.get(&v) {
                Some(t) => t.clone(),
                None => Type::Poly(v),
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

    fn apply(self, subst: &Subst) -> Self {
        let pre = self.pre.into_iter().map(|t| t.apply(subst)).collect();
        let post = self.post.into_iter().map(|t| t.apply(subst)).collect();
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

    pub fn typecheck(&mut self) -> Result<HashMap<String, OpType>, InferenceError> {
        let mut inferred_map = HashMap::new();
        for (op_name, op_def) in self.module.op_defs.iter() {
            if op_name.starts_with("noc") {
                continue;
            }
            let Body::Body(ref body) = op_def.body else {
                // skip constructors and primitives
                continue;
            };
            let inf = self.infer(&body)?;
            let foobar = self
                .inf_vs_ann(inf, &op_def.ann)
                .map_err(|error| InferenceError {
                    error,
                    span: op_def.span.clone(),
                })?;
            inferred_map.insert(op_name.to_owned(), foobar);
        }
        Ok(inferred_map)
    }

    fn inf_vs_ann(&mut self, inf: OpType, ann: &OpType) -> Result<OpType, InferenceErrorMessage> {
        let s = self.unify_op(ann, &inf)?;
        // ann matches the inf when all subs associated with ftv of annotation are poly
        for v in ann.ftv().iter().filter_map(|t| s.get(t)) {
            match v {
                Type::Poly(_) => (),
                _ => Err(InferenceErrorMessage::AnnInfConflict(
                    ann.clone(),
                    inf.clone(),
                ))?,
            }
        }
        Ok(inf.apply(&s))
    }

    fn gen_name(&mut self) -> Type {
        let name = format!("_gen_{}", self.counter);
        self.counter += 1;
        Type::Poly(name)
    }

    fn instantiate_op(&mut self, op: OpType) -> OpType {
        let new_var_subst = op
            .ftv()
            .iter()
            .map(|v| (v.to_owned(), self.gen_name()))
            .collect();
        op.clone().apply(&new_var_subst)
    }

    /// Unify two types. t1 has priority over t2, i.e., (Poly(v), t) is picked over (t, Poly(v)).
    fn unify(&mut self, t1: &Type, t2: &Type) -> Result<Subst, InferenceErrorMessage> {
        match (t1, t2) {
            (Type::Mono(m1), Type::Mono(m2)) if m1 == m2 => Ok(Subst::new()),
            (Type::Mono(_), Type::Mono(_)) => Err(InferenceErrorMessage::UnificationError(
                t1.clone(),
                t2.clone(),
            )),
            (Type::Poly(v1), Type::Poly(v2)) if v1 == v2 => Ok(Subst::new()),
            (Type::Poly(v), t) | (t, Type::Poly(v)) => {
                if t.ftv().contains(v) {
                    Err(InferenceErrorMessage::OccursCheckError(
                        v.clone(),
                        t.clone(),
                    ))
                } else {
                    Ok(Subst::from([(v.clone(), t.clone())]))
                }
            }
            (Type::App(l1, r1), Type::App(l2, r2)) => {
                let s1 = self.unify(l1, l2)?;
                let s2 = self.unify(&r1.clone().apply(&s1), &r2.clone().apply(&s1))?;
                Ok(compose(s1, s2))
            }
            (Type::Op(o1), Type::Op(o2)) => self.unify_op(o1, o2),
            (_, _) => Err(InferenceErrorMessage::UnificationError(
                t1.clone(),
                t2.clone(),
            )),
        }
    }

    /// Performs unification on two slices.
    /// Performs min(l1.len(), l2.len()) unifications.
    fn unify_list(
        &mut self,
        s: Subst,
        l1: &[Type],
        l2: &[Type],
    ) -> Result<Subst, InferenceErrorMessage> {
        zip(l1.iter(), l2.iter()).try_fold(s, |s_acc, (t1, t2)| {
            let s = self.unify(&t1.clone().apply(&s_acc), &t2.clone().apply(&s_acc))?;
            Ok(compose(s_acc, s))
        })
    }

    fn unify_op(&mut self, o1: &OpType, o2: &OpType) -> Result<Subst, InferenceErrorMessage> {
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
            return Err(InferenceErrorMessage::UnificationError(
                Type::Op(o1.clone()),
                Type::Op(o2.clone()),
            ));
        }
        // unify stacks
        let s1 = self.unify_list(Subst::new(), &pre1, &pre2)?;
        self.unify_list(s1, &post1, &post2)
    }

    /// Try to make both optypes have the same lengths of pre and post
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

    fn lit_optype(&self, lit: &Literal) -> OpType {
        let lit_type = match lit {
            Literal::Int(_) => Type::Mono("Int".to_owned()),
        };
        OpType {
            pre: vec![],
            post: vec![lit_type],
        }
    }

    fn make_destr(constr: &OpType) -> OpType {
        OpType {
            pre: constr.post.clone(),
            post: constr.pre.clone(),
        }
    }

    fn infer_case_arm(
        &mut self,
        arm: &CaseArm,
    ) -> Result<(&'m DataDef, OpType), InferenceErrorMessage> {
        // find the constructor op type and the data def associated with the constructor
        let ConstrInfo {
            associated_data: data_def_name,
            op_type: constr_ot,
        } = self
            .module
            .constructor_info
            .get(&arm.constr)
            .ok_or_else(|| InferenceErrorMessage::UnknownConstructor(arm.constr.to_owned()))?;
        let data_def = self
            .module
            .data_defs
            .get(data_def_name)
            .expect("broken constructor info");
        // infer the op type of the body
        let body_optype = self.infer(&arm.body).map_err(|error| error.error)?;
        // create a destructor from the constructor op type and instantiate it
        let destr = Self::make_destr(&constr_ot);
        let inst_destr = self.instantiate_op(destr);
        // chain the destructor with the arm body to get the complete op type
        let (s, chained_optype) = self.chain(inst_destr, body_optype)?;
        let chained_optype_applied = chained_optype.apply(&s);
        Ok((data_def, chained_optype_applied))
    }

    fn prelude_optype(&self, name: &str) -> Option<OpType> {
        prelude_types::PRELUDE_OP_TYPES.get(name).cloned()
    }

    fn constr_optype(&self, name: &str) -> Option<OpType> {
        self.module
            .constructor_info
            .get(name)
            .map(|info| info.op_type.clone())
    }

    fn user_optype(&self, name: &str) -> Option<OpType> {
        self.module
            .op_defs
            .get(name)
            .map(|op_def| &op_def.ann)
            .cloned()
    }

    fn lookup_op_optype(&self, name: &str) -> Option<OpType> {
        // lookup the prelude, constructors, user defined
        self.prelude_optype(name)
            .or_else(|| self.constr_optype(name))
            .or_else(|| self.user_optype(name))
    }

    fn infer_op(&mut self, op: &Op) -> Result<OpType, InferenceErrorMessage> {
        match op {
            Op::Literal { value: lit, .. } => Ok(self.lit_optype(lit)),
            Op::Name { value: n, .. } => {
                let op_type = self
                    .lookup_op_optype(n)
                    .ok_or_else(|| InferenceErrorMessage::UnknownOp(n.clone()))?;
                Ok(self.instantiate_op(op_type))
            }
            Op::Case { head_arm, arms, .. } => {
                let (head_dd, mut ot) = self.infer_case_arm(head_arm)?;
                let mut covered_constructors = HashSet::new();
                covered_constructors.insert(&head_arm.constr);

                let mut s = Subst::new();
                for arm in arms {
                    if !covered_constructors.insert(&arm.constr) {
                        return Err(InferenceErrorMessage::DuplicateConstructor(
                            arm.constr.clone(),
                        ));
                    }
                    let (_, mut arm_ot) = self.infer_case_arm(arm)?;
                    (ot, arm_ot) = self.balance_op_stack_lengths(ot, arm_ot);
                    let new_s = self.unify_op(&ot, &arm_ot)?;
                    s = compose(s, new_s);
                    ot = ot.apply(&s);
                }

                if covered_constructors == head_dd.constrs.keys().collect() {
                    Ok(ot)
                } else {
                    Err(InferenceErrorMessage::NotAllConstructorsCovered)
                }
            }
            Op::Quote { value: ops, .. } => {
                let quoted_optype = self.infer(ops).map_err(|error| error.error)?;
                Ok(OpType {
                    pre: vec![],
                    post: vec![Type::Op(quoted_optype)],
                })
            }
        }
    }

    /// Chain two operator types through unification. This includes overflow and underflow chain.
    fn chain(
        &mut self,
        ot1: OpType,
        ot2: OpType,
    ) -> Result<(Subst, OpType), InferenceErrorMessage> {
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
            let beta_skip_gamma = beta.into_iter().skip(gamma.len());
            let pre = alpha.into_iter().map(|t| t.apply(&s)).collect();
            let post = delta
                .into_iter()
                .chain(beta_skip_gamma)
                .map(|t| t.apply(&s))
                .collect();
            Ok((s, OpType { pre, post }))
        } else {
            // underflow chain
            let gamma_skip_beta = gamma.into_iter().skip(beta.len());
            let pre = alpha
                .into_iter()
                .chain(gamma_skip_beta)
                .map(|t| t.apply(&s))
                .collect();
            let post = delta.into_iter().map(|t| t.apply(&s)).collect();
            Ok((s, OpType { pre, post }))
        }
    }

    fn infer_rest(&mut self, ops: &[Op]) -> Result<(Subst, OpType), InferenceError> {
        match ops {
            [] => Ok((Subst::new(), OpType::empty())),
            [o, os @ ..] => {
                let t1 = self.infer_op(o).map_err(|error| InferenceError {
                    error,
                    span: o.get_span().clone(),
                })?;
                let (s2, t2) = self.infer_rest(os)?;
                let (s3, t3) = self.chain(t1, t2).map_err(|error| InferenceError {
                    error,
                    span: o.get_span().clone(),
                })?;
                let s = compose(s2, s3);
                let t = t3.apply(&s);
                Ok((s, t))
            }
        }
    }

    /// Infer the type of a sentence
    fn infer(&mut self, ops: &[Op]) -> Result<OpType, InferenceError> {
        let (_, op_type) = self.infer_rest(ops)?;
        Ok(op_type)
    }
}

#[cfg(test)]
mod tests {
    use crate::syntax::parse;
    use crate::typing::inference::*;

    #[test]
    fn sanity() {
        let input = "
        define [a, a] nocadd [a]: 1 2 3.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_ok());
    }

    #[test]
    fn subst_int_ann_vs_inf() {
        let input = "
        data Alpha:.
        define [a, a] nocadd [a]:.
        define [Alpha, Alpha] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_ok());
    }

    #[test]
    fn ann_ss_pre() {
        let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [a, Alpha] intadd [Alpha]: nocadd.";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_err());
    }

    #[test]
    fn ann_ss_post() {
        let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [Alpha, a] intadd [Alpha]: nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_err());
    }

    #[test]
    fn ann_ss_double() {
        let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [a, a] intadd [Alpha]: nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_err());
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
        assert!(Inference::new(&module).typecheck().is_err());
    }

    #[test]
    fn ann_ss_trans_stack_ok() {
        let input = "
        data Alpha:. data Beta:.
        data Gamma:. define [a, b, c] nocfoobar [c, b, a]:.
        define [Alpha, Beta, Gamma] intadd [Gamma, Beta, Apha]: nocfoobar.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_err());
    }

    #[test]
    fn uf_triple_add_ok() {
        let input = "
        define [a, a] nocadd [a]:.
        define [a, a, a] tripleadd [a]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_ok());
    }

    #[test]
    fn uf_triple_add_ok_spec() {
        let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Alpha] tripleadd [Alpha]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_ok());
    }

    #[test]
    fn uf_triple_add_ok_err1() {
        let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Alpha] tripleadd [a]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_err());
    }

    #[test]
    fn uf_triple_add_ok_err2() {
        let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Beta] tripleadd [Alpha]: nocadd nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_err());
    }

    #[test]
    fn of_triple1() {
        let input = "
        data Alpha:. data Beta:.
        define [a] nocdup [a, a]:.
        define [a] tripledup [a, a, a]: nocdup nocdup.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_ok());
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
        assert!(Inference::new(&module).typecheck().is_ok());
    }

    #[test]
    fn int_add_uf_chain() {
        let input = "
        data Alpha: alpha. define [a, a] nocadd [a]:.
        define [Alpha] alphainc [Alpha]: alpha nocadd.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_ok());
    }

    #[test]
    fn int_add_datapoly() {
        let input = "
        data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either Alpha b]: alpha left.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_ok());
    }

    #[test]
    fn int_add_datapoly_err() {
        let input = "
        data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either a Alpha]: alpha left.
        ";
        let module = parse(&input).unwrap();
        assert!(Inference::new(&module).typecheck().is_err());
    }

    #[test]
    fn case_maybe_nat() {
        let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Maybe Nat] incnatmaybe [Maybe Nat]: case { just { suc just }, nothing { nothing } }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
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
        let inferred = Inference::new(&module).typecheck();
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
        let inferred = Inference::new(&module).typecheck();
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
        let inferred = Inference::new(&module).typecheck();
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
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn case_totality() {
        let input = "
        data Expr:
            int, float, string, add.
        define [Expr] foobar [Int]:
            case { int {1}, float {2}, string {3}, add {4}}.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn case_totality_err() {
        let input = "
        data Expr:
            int, float, string, add.
        define [Expr] foobar [Int]:
            case { int {1}, float {2}, add {4}}.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn nop_unification_test() {
        let input = "
        define [a] nocnop [a]:. define [] nop []: nocnop.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
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
        let inferred = Inference::new(&module).typecheck();
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
        let inferred = Inference::new(&module).typecheck();
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
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn op_quote_test() {
        let input = "
        define [] foobar [[][Int, Int, Int]]: (1 2 3).
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }
}
