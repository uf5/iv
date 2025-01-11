use super::types::*;
use crate::types::*;

pub struct Evaluator<'m> {
    module: &'m Module,
    pub stack: Vec<Value<'m>>,
}

impl<'m> Evaluator<'m> {
    pub fn new(module: &'m Module) -> Self {
        Evaluator {
            module,
            stack: vec![],
        }
    }

    pub fn eval_main(&mut self) -> Result<(), EvaluatorError> {
        let Some(main_op_def) = self.module.op_defs.get("main") else {
            return Err(EvaluatorError::NoMain);
        };
        let Body::Body(main_body) = &main_op_def.body else {
            return Err(EvaluatorError::MainIsAConstructor);
        };
        Ok(self.eval_sentence(main_body))
    }

    fn eval_sentence(&mut self, ops: &[Op]) {
        for op in ops.iter() {
            self.eval(op);
        }
    }

    fn eval(&mut self, op: &Op) {
        match op {
            Op::Literal(_) => todo!("no literals yet"),
            Op::Name(op_name) => {
                if op_name == "trace" {
                    println!("tracing: {:?}", self.stack);
                    return;
                }
                let Some(op_def) = self.module.op_defs.get(op_name) else {
                    panic!(
                        "type checker seems to have missed an undefined operator: {}",
                        op_name
                    )
                };
                match &op_def.body {
                    Body::Body(ops) => self.eval_sentence(ops),
                    Body::Constructor(data_name) => {
                        let constr_name = op_name;
                        let data_def = self.module.data_defs.get(data_name).expect(&format!(
                            "type checker seems to have missed an undefined data def: {}",
                            data_name
                        ));
                        let args = op_def
                            .ann
                            .pre
                            .iter()
                            .map(|_| {
                                self.stack.pop().expect(
                                    "type checker seems to have missed a stack underflow error",
                                )
                            })
                            .collect();
                        let value = Value {
                            data_def,
                            constr_name: constr_name.clone(),
                            args,
                        };
                        self.stack.push(value);
                    }
                }
            }
            Op::Case(head_arm, rest_arms) => {
                let matched_value = self
                    .stack
                    .pop()
                    .expect("type checker seems to have missed a stack underflow error");
                let matching_arm = vec![head_arm]
                    .into_iter()
                    .chain(rest_arms.iter())
                    .find(|arm| &arm.constr == &matched_value.constr_name)
                    .expect(&format!(
                        "type checker seems to have missed an unknown constructor: {}",
                        &matched_value.constr_name
                    ));
                self.stack.extend(matched_value.args.into_iter().rev());
                self.eval_sentence(&matching_arm.body);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::evaluation::evaluator::*;
    use crate::syntax::parse;

    #[test]
    fn empty() {
        let input = "
        define [] main []:.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main().unwrap();
        assert_eq!(evaluator.stack, vec![]);
    }

    #[test]
    fn foo_bar_baz() {
        let input = "
        data Foo: foo, bar, baz.
        define [] main [Foo, Foo, Foo]: foo bar baz.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main().unwrap();
        let data_def = module.data_defs.get("Foo").unwrap();
        assert_eq!(
            evaluator.stack,
            vec![
                Value {
                    data_def,
                    constr_name: "foo".to_owned(),
                    args: vec![]
                },
                Value {
                    data_def,
                    constr_name: "bar".to_owned(),
                    args: vec![]
                },
                Value {
                    data_def,
                    constr_name: "baz".to_owned(),
                    args: vec![]
                },
            ]
        );
    }

    #[test]
    fn peano_3() {
        let input = "
        data Nat: zero, [Nat] suc.
        define [] main [Nat]: zero suc suc suc.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main().unwrap();
        let data_def = module.data_defs.get("Nat").unwrap();
        assert_eq!(
            evaluator.stack,
            vec![Value {
                data_def,
                constr_name: "suc".to_owned(),
                args: vec![Value {
                    data_def,
                    constr_name: "suc".to_owned(),
                    args: vec![Value {
                        data_def,
                        constr_name: "suc".to_owned(),
                        args: vec![Value {
                            data_def,
                            constr_name: "zero".to_owned(),
                            args: vec![]
                        }]
                    }]
                }]
            }]
        );
    }

    #[test]
    fn peano_add() {
        let input = "
        data Nat: zero, [Nat] suc.
        define [Nat, Nat] natadd [Nat]:
            case { zero { trace }, suc { trace natadd suc } }.
        define [] main [Nat]: zero suc zero suc suc natadd.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main().unwrap();
        let data_def = module.data_defs.get("Nat").unwrap();
        assert_eq!(
            evaluator.stack,
            vec![Value {
                data_def,
                constr_name: "suc".to_owned(),
                args: vec![Value {
                    data_def,
                    constr_name: "suc".to_owned(),
                    args: vec![Value {
                        data_def,
                        constr_name: "suc".to_owned(),
                        args: vec![Value {
                            data_def,
                            constr_name: "zero".to_owned(),
                            args: vec![]
                        }]
                    }]
                }]
            }]
        );
    }

    #[test]
    fn case_destructuring_order() {
        let input = "
        data Foo: foo, bar, baz.
        data X: [Foo, Foo, Foo] x.
        define [] main [Foo, Foo, Foo]: foo bar baz x case { x {} }.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main().unwrap();
        let data_def = module.data_defs.get("Foo").unwrap();
        assert_eq!(
            evaluator.stack,
            vec![
                Value {
                    data_def,
                    constr_name: "foo".to_owned(),
                    args: vec![]
                },
                Value {
                    data_def,
                    constr_name: "bar".to_owned(),
                    args: vec![]
                },
                Value {
                    data_def,
                    constr_name: "baz".to_owned(),
                    args: vec![]
                },
            ]
        );
    }
}
