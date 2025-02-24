#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Mono(String),
    Poly(String),
    Op(OpType),
    App(Box<Type>, Box<Type>),
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

    pub fn augment(&mut self, t: Type) {
        self.pre.push(t.clone());
        self.post.push(t.clone());
    }
}
