use super::ast::*;
use std::collections::HashMap;

/// This struct's sole purpose is to avoid the O(n) constructor
/// information lookup by generating maps associating the constructor
/// name with the data def and the constructor info
pub struct ModuleConstrMaps<'m> {
    pub constr_to_data_map: HashMap<&'m str, (&'m String, &'m DataDef)>,
    pub constr_to_constr_map: HashMap<&'m str, &'m DataConstr>,
}

impl<'m> ModuleConstrMaps<'m> {
    pub fn new(module: &'m Module) -> Self {
        let mut constr_to_data_map = HashMap::new();
        let mut constr_to_constr_map = HashMap::new();
        for data_pair @ (_data_name, data_def) in module.data_defs.iter() {
            for (constr_name, constr_def) in data_def.constrs.iter() {
                constr_to_data_map.insert(constr_name.as_str(), data_pair);
                constr_to_constr_map.insert(constr_name.as_str(), constr_def);
            }
        }
        ModuleConstrMaps {
            constr_to_data_map,
            constr_to_constr_map,
        }
    }
}
