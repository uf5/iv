use crate::syntax::ast;
use crate::typing::types::*;
use std::collections::HashMap;

#[derive(Debug)]
pub struct TypedModule<'m> {
    pub ast_module: &'m ast::Module,
    pub data_defs: HashMap<&'m str, TypedDataDef<'m>>,
    pub op_defs: HashMap<&'m str, TypedOpDef<'m>>,
}

#[derive(Debug)]
pub struct TypedDataDef<'m> {
    pub ast_data_def: &'m ast::DataDef,
}

pub type StackDescr = Vec<Type>;

#[derive(Debug)]
pub struct StackDescrOp<'m> {
    /// complete stack before op exec
    pub pre: StackDescr,
    /// complete stack after op exec
    pub post: StackDescr,
    /// op
    pub op: &'m ast::Op,
    /// op type signature
    pub op_type: OpType,
}

#[derive(Debug)]
pub struct TypedOpDef<'m> {
    pub ast_op_def: &'m ast::OpDef,
    pub typed_body: StackDescrOp<'m>,
}
