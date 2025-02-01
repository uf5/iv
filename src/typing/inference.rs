use super::prelude_types;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::once;
use std::iter::zip;

use super::types::*;
use crate::syntax::ast::*;
use crate::syntax::module_wrapper::ModuleConstrMaps;

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
    TypeOrderErrorElem { general: Type, concrete: Type },
    TypeOrderErrorOp { general: OpType, concrete: OpType },
    OpPrePostLenNeq { general: OpType, concrete: OpType },
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
                f.extend(t2.ftv());
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

struct ModuleConstrOpTypeMap<'m> {
    pub constr_to_optype_map: HashMap<&'m str, OpType>,
}

impl<'m> ModuleConstrOpTypeMap<'m> {
    pub fn new(module: &'m Module) -> Self {
        let mut constr_to_optype_map = HashMap::new();
        for (data_name, data_def) in module.data_defs.iter() {
            for (constr_name, constr_def) in data_def.constrs.iter() {
                let constructed_type = data_def
                    .params
                    .iter()
                    .map(|p| Type::Poly(p.to_owned()))
                    .fold(Type::Mono(data_name.to_owned()), |a, x| {
                        Type::App(Box::new(a), Box::new(x))
                    });
                let optype = OpType {
                    pre: constr_def.params.clone(),
                    post: vec![constructed_type],
                };
                constr_to_optype_map.insert(constr_name.as_str(), optype);
            }
        }
        ModuleConstrOpTypeMap {
            constr_to_optype_map,
        }
    }
}

pub struct Inference<'m> {
    module: &'m Module,
    constr_maps: ModuleConstrMaps<'m>,
    optype_maps: ModuleConstrOpTypeMap<'m>,
    counter: usize,
}

impl<'m> Inference<'m> {
    pub fn new(module: &'m Module) -> Self {
        let constr_maps = ModuleConstrMaps::new(module);
        let optype_maps = ModuleConstrOpTypeMap::new(module);
        Inference {
            module,
            constr_maps,
            optype_maps,
            counter: 0,
        }
    }

    pub fn typecheck(&mut self) -> Result<(), InferenceError> {
        for (op_name, op_def) in self.module.op_defs.iter() {
            if op_name.starts_with("noc") {
                continue;
            }
            let inf = self.infer(&op_def.body)?;
            println!("for {} inferred {:?}", op_name, inf);
            self.inf_vs_ann(inf, &op_def.ann)
                .map_err(|error| InferenceError {
                    error,
                    span: op_def.span.clone(),
                })?;
        }
        Ok(())
    }

    fn inf_vs_ann(&mut self, inf: OpType, ann: &OpType) -> Result<(), InferenceErrorMessage> {
        // augment stacks toward the annotation
        let inf = self.augment_towards(inf, ann);
        let s = self.unify_op_ow(&inf, ann)?;
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
        Ok(())
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
        op.apply(&new_var_subst)
    }

    fn unify_list_bw(
        &mut self,
        s: Subst,
        l1: &[Type],
        l2: &[Type],
    ) -> Result<Subst, InferenceErrorMessage> {
        self.unify_list_ow(s.clone(), l1, l2)
            .or_else(|_| self.unify_list_ow(s.clone(), l2, l1))
    }

    fn unify_list_ow(
        &mut self,
        s: Subst,
        general: &[Type],
        concrete: &[Type],
    ) -> Result<Subst, InferenceErrorMessage> {
        zip(general.iter(), concrete.iter()).try_fold(s, |s_acc, (g, t)| {
            let s = self.unify_ow(&g.clone().apply(&s_acc), &t.clone().apply(&s_acc))?;
            Ok(compose(s_acc, s))
        })
    }

    fn unify_op_bw(&mut self, o1: &OpType, o2: &OpType) -> Result<Subst, InferenceErrorMessage> {
        self.unify_op_ow(o1, o2)
            .or_else(|_| self.unify_op_ow(o2, o1))
    }

    fn unify_op_ow(
        &mut self,
        general: &OpType,
        concrete: &OpType,
    ) -> Result<Subst, InferenceErrorMessage> {
        // this augmented op type gets deleted after exiting this funciton's
        // scope.
        // in theory it would be better to replace the general optype
        // with the augmented one, but i dont think this will be an
        // issue since [][Foo] <= [a][Foo, a].
        // in addition, the formalized type inference rules includes the
        // augmentation rule, which, roughly speaking, does not change the type.
        let aug_general = self.augment_towards(general.clone(), concrete);
        // op type pre post stacks length equality check
        if aug_general.pre.len() != concrete.pre.len()
            || aug_general.post.len() != concrete.post.len()
        {
            return Err(InferenceErrorMessage::OpPrePostLenNeq {
                general: aug_general.clone(),
                concrete: concrete.clone(),
            });
        }
        // unify stacks
        let s1 = self.unify_list_ow(Subst::new(), &aug_general.pre, &concrete.pre)?;
        self.unify_list_ow(s1, &aug_general.post, &concrete.post)
    }

    /// one way type unification: general <= concrete
    fn unify_ow(
        &mut self,
        general: &Type,
        concrete: &Type,
    ) -> Result<Subst, InferenceErrorMessage> {
        match (general, concrete) {
            (Type::Mono(m1), Type::Mono(m2)) if m1 == m2 => Ok(Subst::new()),
            (Type::Poly(p1), Type::Poly(p2)) if p1 == p2 => Ok(Subst::new()),
            (Type::Poly(v), t) => Ok(once((v.clone(), t.clone())).collect()),
            (Type::App(f1, x1), Type::App(f2, x2)) => {
                let s1 = self.unify_ow(f1, f2)?;
                let s2 = self.unify_ow(&x1.clone().apply(&s1), &x2.clone().apply(&s1))?;
                Ok(compose(s1, s2))
            }
            (Type::Op(o1), Type::Op(o2)) => self.unify_op_ow(o1, o2),
            (general, concrete) => Err(InferenceErrorMessage::TypeOrderErrorElem {
                general: general.clone(),
                concrete: concrete.clone(),
            }),
        }
    }

    /// Augments the first argument's pre and post stacks towards the target
    fn augment_towards(&mut self, mut aug: OpType, target: &OpType) -> OpType {
        while aug.pre.len() < target.pre.len() && aug.post.len() < target.post.len() {
            let new_var = self.gen_name();
            aug.pre.push(new_var.clone());
            aug.post.push(new_var.clone());
        }
        aug
    }

    /// augment both optypes aso that both optypes have the same stacks lengths
    fn augment_both(&mut self, o1: OpType, o2: OpType) -> (OpType, OpType) {
        let o1 = self.augment_towards(o1, &o2);
        let o2 = self.augment_towards(o2, &o1);
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

    fn lookup_constructor_optype(&self, name: &str) -> Result<OpType, InferenceErrorMessage> {
        self.optype_maps
            .constr_to_optype_map
            .get(name)
            .cloned()
            .ok_or_else(|| InferenceErrorMessage::UnknownConstructor(name.to_owned()))
    }

    fn lookup_constructor_data_def(&self, name: &str) -> Result<&&DataDef, InferenceErrorMessage> {
        self.constr_maps
            .constr_to_data_map
            .get(name)
            .map(|(_data_name, data_def)| data_def)
            .ok_or_else(|| InferenceErrorMessage::UnknownConstructor(name.to_owned()))
    }

    fn infer_case_arm(&mut self, arm: &CaseArm) -> Result<OpType, InferenceErrorMessage> {
        let constr_ot = self.lookup_constructor_optype(arm.constr.as_str())?;
        let body_optype = self.infer(&arm.body).map_err(|error| error.error)?;
        // create a destructor from the constructor op type and instantiate it
        let destr = Self::make_destr(&constr_ot);
        let inst_destr = self.instantiate_op(destr);
        // chain the destructor with the arm body to get the complete op type
        self.chain(inst_destr, body_optype)
    }

    fn get_prelude_optype(&self, name: &str) -> Option<OpType> {
        prelude_types::get(name)
    }

    fn get_constr_optype(&self, name: &str) -> Option<OpType> {
        self.optype_maps.constr_to_optype_map.get(name).cloned()
    }

    fn get_user_optype(&self, name: &str) -> Option<OpType> {
        self.module
            .op_defs
            .get(name)
            .map(|op_def| &op_def.ann)
            .cloned()
    }

    fn lookup_op_optype(&self, name: &str) -> Option<OpType> {
        // lookup the prelude, constructors, user defined
        self.get_prelude_optype(name)
            .or_else(|| self.get_constr_optype(name))
            .or_else(|| self.get_user_optype(name))
    }

    fn infer_op(&mut self, op: &Op) -> Result<OpType, InferenceErrorMessage> {
        match op {
            Op::Ann { value, ann, .. } => {
                let inf = self.infer_op(value)?;
                self.inf_vs_ann(inf.clone(), ann)?;
                Ok(self.instantiate_op(ann.clone()))
            }
            Op::Literal { value: lit, .. } => Ok(self.lit_optype(lit)),
            Op::Name { value: n, .. } => {
                let op_type = self
                    .lookup_op_optype(n)
                    .ok_or_else(|| InferenceErrorMessage::UnknownOp(n.clone()))?;
                Ok(self.instantiate_op(op_type))
            }
            Op::Case { head_arm, arms, .. } => {
                let head_constrs = self
                    .lookup_constructor_data_def(head_arm.constr.as_str())?
                    .constrs
                    .keys()
                    .cloned()
                    .collect();
                let mut head_ot = self.infer_case_arm(head_arm)?;
                let mut covered_constructors = HashSet::new();
                covered_constructors.insert(head_arm.constr.clone());

                let mut s = Subst::new();
                for arm in arms {
                    if !covered_constructors.insert(arm.constr.clone()) {
                        return Err(InferenceErrorMessage::DuplicateConstructor(
                            arm.constr.clone(),
                        ));
                    }
                    let mut arm_ot = self.infer_case_arm(arm)?;
                    (head_ot, arm_ot) = self.augment_both(head_ot, arm_ot);
                    let new_s = self.unify_op_bw(&head_ot, &arm_ot)?;
                    s = compose(s, new_s);
                    head_ot = head_ot.apply(&s);
                }

                if covered_constructors == head_constrs {
                    Ok(head_ot)
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
    fn chain(&mut self, ot1: OpType, ot2: OpType) -> Result<OpType, InferenceErrorMessage> {
        let OpType {
            pre: alpha,
            post: beta,
        } = ot1;
        let OpType {
            pre: gamma,
            post: delta,
        } = ot2;
        let s = self.unify_list_bw(Subst::new(), &beta, &gamma)?;
        if beta.len() >= gamma.len() {
            // overflow chain
            let beta_skip_gamma = beta.into_iter().skip(gamma.len());
            let pre = alpha.into_iter().collect();
            let post = delta.into_iter().chain(beta_skip_gamma).collect();
            Ok(OpType { pre, post }.apply(&s))
        } else {
            // underflow chain
            let gamma_skip_beta = gamma.into_iter().skip(beta.len());
            let pre = alpha.into_iter().chain(gamma_skip_beta).collect();
            let post = delta.into_iter().collect();
            Ok(OpType { pre, post }.apply(&s))
        }
    }

    /// Infer the type of a sentence
    fn infer(&mut self, ops: &[Op]) -> Result<OpType, InferenceError> {
        let mut inf_acc = OpType::empty();
        for op in ops {
            let t1 = self.infer_op(op).map_err(|error| InferenceError {
                error,
                span: op.get_span().clone(),
            })?;
            let chained = self.chain(inf_acc, t1).map_err(|error| InferenceError {
                error,
                span: op.get_span().clone(),
            })?;
            inf_acc = chained;
        }
        Ok(inf_acc)
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
        define [] nop []:. define [a] foobar [a]: nop.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn nop_unification_test_err() {
        let input = "
        define [a] nocnop [a]:. define [] nop []: nocnop.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
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
        define [Maybe Nat] natnop [Maybe Nat]:.
        define [Maybe Nat, Nat] foobar [Maybe Nat, Nat]: natnop.
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

    #[test]
    fn prelude_br_test() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [Bar, Foo, Foo, Foo] foobar [Foo, Foo, Foo, Bar]: br-3.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn prelude_br_test_err() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [Bar, Foo, Foo, Foo] foobar [Foo, Foo, Foo, Bar]: br-2.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn prelude_dg_test() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [Foo, Foo, Foo, Bar] foobar [Bar, Foo, Foo, Foo]: dg-3.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn prelude_dg_test_err() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [Foo, Foo, Foo, Bar] foobar [Bar, Foo, Foo, Foo]: dg-2.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_comp_test_dup() {
        let input = "
        data Foo: foo.
        define [] foo [[][Foo, Foo]]: (foo) (dup) comp-0-1-1-2.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn special_comp_test_dup1() {
        let input = "
        data Foo: foo.
        define [] foo [[a][Foo, a, a]]: (dup) (foo) comp-1-2-0-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn todo_nop_postfix_ann_vs_inf_bad() {
        let input = "
        data Foo: foo.
        define [] foo [Foo]: dup pop foo.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_comp_test_err() {
        let input = "
        data Foo: foo.
        define [] foo [[][Foo, Foo]]: (dup) (foo) comp-1-2-0-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_comp_test_quote() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [] foo [[][Bar, Foo]]: foo quote bar quote comp-0-1-0-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn special_comp_test_quote_err() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [] foo [[][Foo, Bar]]: foo quote bar quote comp-0-1-0-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_comp_test2() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [a] id [a]:.
        define [] foo [[Foo][Bar, Foo]]: (id) (bar) comp-1-1-0-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn special_comp_test3() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [a] id [a]:.
        define [] foo [[][Bar]]: (bar) (id) comp-0-1-1-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn special_comp_of() {
        let input = "
        define [] foo [[a][a, a, a]]: (dup) (dup) comp-1-2-1-2.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn special_comp_of2() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [a] id [a]:.
        define [] foo [[a][Bar, a, a]]: (dup) (bar) comp-1-2-0-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn special_comp_nei() {
        let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [] foo []: (id) comp.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_comp_nop1() {
        let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [] foo []: foo comp.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_comp_nop2() {
        let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [] foo []: foo (id) comp.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_comp_nop3() {
        let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [] foo []: (id) foo comp.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_exec() {
        let input = "
        data Foo: foo.
        define [] foo [Foo, Foo, Foo, Foo]: foo (dup dup dup) exec-1-4.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn special_exec_nei() {
        let input = "
        data Foo: foo.
        define [] foo [Foo, Foo, Foo, Foo]: (dup dup dup) exec.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn special_exec_nop() {
        let input = "
        data Foo: foo.
        define [] foo [Foo, Foo, Foo, Foo]: foo exec.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_err());
    }

    #[test]
    fn prelude_name_lookup_false_positive() {
        let input = "
        define [a] foo-1 [a]:.
        define [b] foo [b]: foo-1.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn nat_list_sum_test() {
        // stateful typechecker exec can infer that the poly is an optype
        let input = "
        data Nat:
          zero,
          [Nat] suc.

        define [Nat, Nat] natsum [Nat]:
          case { zero { },
                 suc { natsum suc },
               }.

        data List a:
          empty,
          [a, List a] cons.

        define [] nop []:.

        define [[a][b], List a] map [List b]:
          br-1
          case { empty { pop empty },
                 cons { br-2 dg-1 dup br-2 map br-2 exec-1-1 cons },
               }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }

    #[test]
    fn nat_list_sum_test2() {
        // stateful typechecker exec cannot infer that the poly is an optype
        let input = "
        data Nat:
          zero,
          [Nat] suc.

        define [Nat, Nat] natsum [Nat]:
          case { zero { },
                 suc { natsum suc },
               }.

        data List a:
          empty,
          [a, List a] cons.

        define [] nop []:.

        define [[a][b], List a] map [List b]:
          br-1
          case { empty { pop empty },
                 cons { dg-2 dup dg-2 br-1 exec-1-1 br-2 map dg-1 cons },
               }.
        ";
        let module = parse(&input).unwrap();
        let inferred = Inference::new(&module).typecheck();
        println!("{:?}", inferred);
        assert!(inferred.is_ok());
    }
}
