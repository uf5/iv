use std::collections::HashMap;
use std::collections::HashSet;

use crate::iv::types::*;

pub enum InferenceError {
    UnificationError(Type, Type),
    OccursCheckError(String, Type),
    UnknownOp(String),
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

#[derive(Clone)]
struct Schema<T> {
    pub vars: HashSet<String>,
    pub t: T,
}

impl<T> Typeable for Schema<T>
where
    T: Typeable,
{
    fn ftv(&self) -> HashSet<String> {
        let mut vs = self.t.ftv();
        for v in self.vars.iter() {
            vs.remove(v);
        }
        vs
    }

    fn apply(&self, subst: &Subst) -> Self {
        let subst_no_vars = subst
            .clone()
            .into_iter()
            .filter(|(k, _)| !self.vars.contains(k))
            .collect();
        Schema {
            vars: self.vars.clone(),
            t: self.t.apply(&subst_no_vars),
        }
    }
}

#[derive(Clone)]
struct TypeEnv {
    pub schemas: HashMap<String, Schema<Type>>,
}

impl Typeable for TypeEnv {
    fn ftv(&self) -> HashSet<String> {
        self.schemas.values().flat_map(Typeable::ftv).collect()
    }

    fn apply(&self, subst: &Subst) -> Self {
        let schemas = self
            .schemas
            .iter()
            .map(|(v, t)| (v.to_owned(), t.apply(subst)))
            .collect();
        TypeEnv { schemas }
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv {
            schemas: HashMap::new(),
        }
    }

    pub fn generalize<T>(&self, t: &T) -> Schema<T>
    where
        T: Typeable + Clone,
    {
        let vars = t.ftv().difference(&self.ftv()).cloned().collect();
        Schema { vars, t: t.clone() }
    }

    pub fn remove(&self, v: &str) -> TypeEnv {
        let mut new_env = self.clone();
        new_env.schemas.remove(v);
        new_env
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

    pub fn infer() -> Err<()> {
        todo!()
    }

    fn gen_name(&mut self) -> Type {
        let name = format!("gen_{}", self.counter);
        self.counter += 1;
        Type::Poly(name)
    }

    fn instantiate(&mut self, scm: &Schema<Type>) -> Type {
        let Schema { vars, t } = scm;
        let new_var_subst = vars
            .iter()
            .map(|v| (v.to_owned(), self.gen_name()))
            .collect();
        t.apply(&new_var_subst)
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
                Ok(compose(&s1, &s2))
            }
            (Type::Op(_o1), Type::Op(_o2)) => todo!(),
            (_, _) => Err(InferenceError::UnificationError(t1.clone(), t2.clone())),
        }
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

    fn ti_op(&mut self, e: &TypeEnv, op: &Op) -> Err<(Subst, OpType)> {
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
            Op::Case(hash_map) => todo!(),
        }
    }

    fn overflow_chain(&mut self, t1: &OpType, t2: &OpType) -> Err<(Subst, OpType)> {
        todo!()
    }

    fn ti(&mut self, e: &TypeEnv, ops: &[Op]) -> Err<(Subst, OpType)> {
        match ops {
            [] => Ok((Subst::new(), OpType::empty())),
            [o, os @ ..] => {
                let (s1, t1) = self.ti_op(e, o)?;
                let e1 = e.apply(&s1);
                let (s2, t2) = self.ti(&e1, os)?;
                let (s3, t3) = self.overflow_chain(&t1, &t2)?;
                let s = compose(&s3, &compose(&s2, &s1));
                let t = t3.apply(&s);
                Ok((s, t))
            }
        }
    }
}
