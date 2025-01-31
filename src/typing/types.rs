#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Mono(String),
    Poly(String),
    Op(OpType),
    App(Box<Type>, Box<Type>),
}

impl Type {
    pub fn mono_tuple() -> Self {
        Self::Mono("Tuple".to_owned())
    }

    pub fn mono_unit() -> Self {
        Self::Mono("Unit".to_owned())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpType {
    pub pre: Vec<Type>,
    pub post: Vec<Type>,
}

impl OpType {
    pub fn empty() -> Self {
        OpType {
            pre: vec![],
            post: vec![],
        }
    }
}
