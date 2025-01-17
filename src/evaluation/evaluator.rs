use super::types::*;
use crate::syntax::ast::*;

pub struct Evaluator<'m> {
    module: &'m Module,

    pub stack: Vec<Value>,
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
        Ok(self.eval_sentence(&main_op_def.body))
    }

    fn eval_sentence(&mut self, ops: &[Op]) {
        for op in ops.iter() {
            self.eval(op);
        }
    }

    fn eval(&mut self, op: &Op) {
        match op {
            Op::Literal { .. } => todo!("no literals yet"),
            Op::Name { value: op_name, .. } => {
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
                self.eval_sentence(&op_def.body);
            }
            Op::Case {
                head_arm,
                arms: rest_arms,
                ..
            } => {
                let Value::User { constr_name, args } =
                    self.stack.pop().expect("stack underflow error")
                else {
                    panic!("matching a quote value")
                };
                let matching_arm = vec![head_arm]
                    .into_iter()
                    .chain(rest_arms.iter())
                    .find(|arm| &arm.constr == &constr_name)
                    .expect(&format!("unknown constructor: {}", &constr_name));
                self.stack.extend(args.into_iter().rev());
                self.eval_sentence(&matching_arm.body);
            }
            Op::Quote { value: ops, .. } => self.stack.push(Value::Quote { ops: ops.clone() }),
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
        assert!(matches!(evaluator.stack[..], []))
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
        assert!(matches!(
            evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 },
                Value::User { constr_name: ref name2, args: ref args2 },
                Value::User { constr_name: ref name3, args: ref args3 },
            ] if name1 == "foo" && args1.is_empty() &&
                 name2 == "bar" && args2.is_empty() &&
                 name3 == "baz" && args3.is_empty()
        ));
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
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 }
            ] if name1 == "suc" && matches!(
                &args1[..],
                [
                    Value::User { constr_name: ref name2, args: ref args2 }
                ] if name2 == "suc" && matches!(
                    &args2[..],
                    [
                        Value::User { constr_name: ref name3, args: ref args3 }
                    ] if name3 == "suc" && matches!(
                        &args3[..],
                        [
                            Value::User { constr_name: ref name4, args: ref args4 }
                        ] if name4 == "zero" && args4.is_empty()
                    )
                )
            )
        ));
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
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User {
                    constr_name: ref name1,
                    args: ref args1
                }
            ] if name1 == "suc" && matches!(
                &args1[..],
                [
                    Value::User {
                        constr_name: ref name2,
                        args: ref args2
                    }
                ] if name2 == "suc" && matches!(
                    &args2[..],
                    [
                        Value::User {
                            constr_name: ref name3,
                            args: ref args3
                        }
                    ] if name3 == "suc" && matches!(
                        &args3[..],
                        [
                            Value::User {
                                constr_name: ref name4,
                                args: ref args4
                            }
                        ] if name4 == "zero" && args4.is_empty()
                    )
                )
            )
        ));
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
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 },
                Value::User { constr_name: ref name2, args: ref args2 },
                Value::User { constr_name: ref name3, args: ref args3 },
            ] if name1 == "foo" && args1.is_empty() &&
                 name2 == "bar" && args2.is_empty() &&
                 name3 == "baz" && args3.is_empty()
        ));
    }
}
