use std::collections::HashMap;
use std::collections::HashSet;

use crate::iv::types::*;

pub enum InferenceError {
    UnificationError(Type, Type),
    OccursCheckError,
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
        let new_var_subst: Subst = vars
            .iter()
            .map(|v| (v.to_owned(), self.gen_name()))
            .collect();
        t.apply(&new_var_subst)
    }
}
