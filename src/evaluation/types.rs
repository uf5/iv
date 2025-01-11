use crate::types::*;

#[derive(Debug)]
pub enum EvaluatorError {
    NoMain,
    MainIsAConstructor,
}

#[derive(PartialEq, Eq)]
pub struct Value<'m> {
    pub data_def: &'m DataDef,
    pub constr_name: String,
    pub args: Vec<Value<'m>>,
}

impl<'m> std::fmt::Debug for Value<'m> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(&self.constr_name)
            .field("args", &self.args)
            .finish()
    }
}
