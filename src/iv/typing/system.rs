use super::super::types::*;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug)]
pub enum InferenceError {
    UnificationError(Type, Type),
    OccursCheckError(String, Type),
    UnknownOp(String),
}

#[derive(Debug)]
struct Schema {
    vars: HashSet<String>,
    t: Type,
}

type Subs = HashMap<String, Type>;

fn compose(s1: Subs, s2: Subs) -> Subs {
    let mut result: HashMap<_, _> = s2.into_iter().map(|(k, v)| (k, v.apply(&s1))).collect();
    result.extend(s1);
    result
}

trait Typeable {
    fn free_poly(&self) -> HashSet<String>;
    fn apply(&self, subs: &Subs) -> Self;
}

impl Typeable for Type {
    fn free_poly(&self) -> HashSet<String> {
        match self {
            Type::Poly(v) => HashSet::from([v.clone()]),
            Type::Mono(_) => HashSet::new(),
            Type::Op(op) => op.free_poly(),
            Type::App(t1, t2) => {
                let mut vs = t1.free_poly();
                vs.extend(t2.free_poly());
                vs
            }
        }
    }

    fn apply(&self, subs: &Subs) -> Self {
        match self {
            Type::Poly(v) => match subs.get(v) {
                Some(t) => t.clone(),
                None => self.clone(),
            },
            Type::Mono(_) => self.clone(),
            Type::Op(op) => Type::Op(op.apply(subs)),
            Type::App(t1, t2) => Type::App(Box::new(t1.apply(subs)), Box::new(t2.apply(subs))),
        }
    }
}

impl Typeable for OpType {
    fn free_poly(&self) -> HashSet<String> {
        self.pre
            .iter()
            .chain(self.post.iter())
            .flat_map(|t| t.free_poly())
            .collect()
    }

    fn apply(&self, subs: &Subs) -> Self {
        let pre = self.pre.iter().map(|t| t.apply(subs)).collect();
        let post = self.post.iter().map(|t| t.apply(subs)).collect();
        OpType { pre, post }
    }
}

impl Typeable for Schema {
    fn free_poly(&self) -> HashSet<String> {
        self.t.free_poly().difference(&self.vars).cloned().collect()
    }

    fn apply(&self, subs: &Subs) -> Self {
        let subs_diff_vars = subs
            .clone()
            .into_iter()
            .filter(|(k, _)| !self.vars.contains(k))
            .collect();
        Schema {
            vars: self.vars.clone(),
            t: self.t.apply(&subs_diff_vars),
        }
    }
}

struct Gamma(HashMap<String, Schema>);

impl Typeable for Gamma {
    fn free_poly(&self) -> HashSet<String> {
        self.0.values().flat_map(|s| s.free_poly()).collect()
    }

    fn apply(&self, subs: &Subs) -> Self {
        Gamma(
            self.0
                .iter()
                .map(|(k, v)| (k.clone(), v.apply(subs)))
                .collect(),
        )
    }
}

impl Gamma {
    pub fn remove(&mut self, v: &str) {
        self.0.remove(v);
    }

    pub fn generalize(&self, t: &Type) -> Schema {
        let vars: HashSet<String> = t
            .free_poly()
            .difference(&self.free_poly())
            .cloned()
            .collect();
        Schema { vars, t: t.clone() }
    }
}

struct Inference<'m> {
    counter: usize,
    module: &'m Module,
}

impl<'m> Inference<'m> {
    pub fn new(module: &'m Module) -> Self {
        Inference { counter: 1, module }
    }

    fn new_var(&mut self) -> Type {
        let var = format!("gen_{}", self.counter);
        self.counter += 1;
        Type::Poly(var)
    }

    pub fn instantiate(&mut self, scm: &Schema) -> Type {
        let n_vs_ss: HashMap<_, _> = scm
            .vars
            .iter()
            .map(|v| (v.to_owned(), self.new_var()))
            .collect();
        scm.t.apply(&n_vs_ss)
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<Subs, InferenceError> {
        match (t1, t2) {
            (Type::Mono(n1), Type::Mono(n2)) if n1 == n2 => Ok(Subs::new()),
            (Type::Poly(v1), Type::Poly(v2)) if v1 == v2 => Ok(Subs::new()),
            (Type::Poly(v), t) | (t, Type::Poly(v)) if t.free_poly().contains(v) => {
                Err(InferenceError::OccursCheckError(v.clone(), t.clone()))
            }
            (Type::Poly(v), t) | (t, Type::Poly(v)) => Ok(Subs::from([(v.clone(), t.clone())])),
            (
                Type::Op(OpType {
                    pre: pre1,
                    post: post1,
                }),
                Type::Op(OpType {
                    pre: pre2,
                    post: post2,
                }),
            ) => {
                let s_pre = pre1
                    .iter()
                    .zip(pre2.iter())
                    .try_fold(Subs::new(), |s, (t1, t2)| {
                        let s1 = self.unify(t1, t2)?;
                        Ok(compose(s, s1))
                    })?;
                post1
                    .iter()
                    .zip(post2.iter())
                    .try_fold(s_pre, |s, (t1, t2)| {
                        let s1 = self.unify(t1, t2)?;
                        Ok(compose(s, s1))
                    })
            }
            (Type::App(a1, a2), Type::App(b1, b2)) => {
                let s1 = self.unify(a1, b1)?;
                let s2 = self.unify(&a2.apply(&s1), &b2.apply(&s1))?;
                Ok(compose(s1, s2))
            }
            (t1, t2) => Err(InferenceError::UnificationError(t1.clone(), t2.clone())),
        }
    }
}
