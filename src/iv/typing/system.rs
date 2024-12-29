use super::super::types::*;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug)]
pub enum InferenceError {
    UnificationError(Type, Type),
    OccursCheckError(String, Type),
    UnknownOp(String),
    ChainError,
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

    fn instantiate(&mut self, scm: &Schema) -> Type {
        let n_vs_ss: HashMap<_, _> = scm
            .vars
            .iter()
            .map(|v| (v.to_owned(), self.new_var()))
            .collect();
        scm.t.apply(&n_vs_ss)
    }

    fn unify(&mut self, t1: &Type, t2: &Type) -> Result<Subs, InferenceError> {
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
                if (pre1.len() != pre2.len()) || (post1.len() != post2.len()) {
                    return Err(InferenceError::UnificationError(t1.clone(), t2.clone()));
                }
                let s_pre =
                    pre1.iter()
                        .zip(pre2.iter())
                        .try_fold(Subs::new(), |s_acc, (t1, t2)| {
                            let s1 = self.unify(t1, t2)?;
                            Ok(compose(s_acc, s1))
                        })?;
                post1
                    .iter()
                    .zip(post2.iter())
                    .try_fold(s_pre, |s_acc, (t1, t2)| {
                        let s1 = self.unify(t1, t2)?;
                        Ok(compose(s_acc, s1))
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

    fn infer_literal(&self, lit: &Literal) -> OpType {
        match lit {
            Literal::Int(_) => OpType {
                pre: vec![],
                post: vec![Type::Mono("Int".to_owned())],
            },
        }
    }

    fn infer_op(&mut self, gamma: &Gamma, op: &Op) -> Result<(Subs, OpType), InferenceError> {
        match op {
            Op::Literal(lit) => Ok((Subs::new(), self.infer_literal(lit))),
            _ => todo!(),
        }
    }

    fn overflow_chain(
        &mut self,
        t1: &OpType,
        t2: &OpType,
    ) -> Result<(Subs, OpType), InferenceError> {
        let OpType {
            pre: alpha,
            post: beta_gamma,
        } = t1;
        let OpType {
            pre: beta,
            post: delta,
        } = t2;
        // ensure that |beta_gamma| >= beta
        if beta_gamma.len() < beta.len() {
            return Err(InferenceError::ChainError);
        }
        // unify prefixes
        let s = beta_gamma
            .iter()
            .zip(beta.iter())
            .try_fold(Subs::new(), |s_acc, (t1, t2)| {
                Ok(compose(s_acc, self.unify(t1, t2)?))
            })?;
        // remainder after prefx unification
        let gamma: Vec<Type> = beta_gamma.iter().skip(beta.len()).cloned().collect();
        // apply substitutions to the rest of the types
        let alpha: Vec<Type> = alpha.iter().map(|t| t.apply(&s)).collect();
        let delta_gamma = delta
            .iter()
            .chain(gamma.iter())
            .map(|t| t.apply(&s))
            .collect();
        // return the chained optype
        Ok((
            s,
            OpType {
                pre: alpha,
                post: delta_gamma,
            },
        ))
    }

    fn underflow_chain(
        &mut self,
        t1: &OpType,
        t2: &OpType,
    ) -> Result<(Subs, OpType), InferenceError> {
        todo!()
    }

    fn chain(&mut self, t1: &OpType, t2: &OpType) -> Result<(Subs, OpType), InferenceError> {
        self.overflow_chain(t1, t2)
    }

    fn infer(&mut self, gamma: &Gamma, ops: &[Op]) -> Result<(Subs, OpType), InferenceError> {
        match ops {
            [] => Ok((
                Subs::new(),
                OpType {
                    pre: vec![],
                    post: vec![],
                },
            )),
            [o, os @ ..] => {
                let (s1, t1) = self.infer_op(gamma, o)?;
                let gamma1 = gamma.apply(&s1);
                let (s2, t2) = self.infer(&gamma1, os)?;
                let t1 = t1.apply(&s2);
                let (ss, tt) = self.chain(&t1, &t2)?;
                Ok((compose(compose(ss, s2), s1), tt))
            }
        }
    }
}
