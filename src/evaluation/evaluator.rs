use super::types::*;
use crate::syntax::{ast::*, module_wrapper::ModuleConstrMaps};

fn parse_parametric<const N: usize>(prefix: &str, s: &str) -> Option<[usize; N]> {
    let rest = s.strip_prefix(prefix)?;
    rest.split('-')
        .map(str::parse)
        .collect::<Result<Vec<_>, _>>()
        .ok()?
        .try_into()
        .ok()
}

pub struct Evaluator<'m> {
    module: &'m Module,
    constr_maps: ModuleConstrMaps<'m>,
    pub stack: Vec<Value>,
}

impl<'m> Evaluator<'m> {
    pub fn new(module: &'m Module) -> Self {
        let constr_maps = ModuleConstrMaps::new(module);
        Evaluator {
            module,
            constr_maps,
            stack: vec![],
        }
    }

    pub fn eval_main(&mut self) {
        let main_op_def = self.module.op_defs.get("main").expect("no main");
        self.eval_sentence(&main_op_def.body);
    }

    fn eval_sentence(&mut self, ops: &[Op]) {
        for op in ops.iter() {
            self.eval(op);
        }
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().expect("underflow error")
    }

    fn eval(&mut self, op: &Op) {
        match op {
            Op::Ann { value, .. } => self.eval(value),
            Op::Literal { .. } => unimplemented!("literals"),
            Op::Name { value: op_name, .. } => {
                if let Some([n]) = parse_parametric("br-", op_name) {
                    let buried = self.pop();
                    self.stack.insert(self.stack.len() - n, buried);
                } else if let Some([n]) = parse_parametric("dg-", op_name) {
                    let digged = self.stack.remove(self.stack.len() - n - 1);
                    self.stack.push(digged);
                } else if let Some([_, _]) = parse_parametric("exec-", op_name) {
                    let Value::Quote { ops } = self.pop() else {
                        panic!("topmost is not an op")
                    };
                    self.eval_sentence(&ops);
                } else if op_name == "pop" {
                    self.pop();
                } else if op_name == "trace" {
                    println!("tracing: {:?}", self.stack);
                } else if let Some(op_def) = self.module.op_defs.get(op_name) {
                    self.eval_sentence(&op_def.body);
                } else if let Some(constr_def) =
                    self.constr_maps.constr_to_constr_map.get(op_name.as_str())
                {
                    let args = constr_def.params.iter().map(|_| self.pop()).collect();
                    self.stack.push(Value::User {
                        constr_name: op_name.to_owned(),
                        args,
                    });
                } else {
                    panic!("unknown operator: {}", op_name);
                }
            }
            Op::Case {
                head_arm,
                arms: rest_arms,
                ..
            } => {
                let Value::User { constr_name, args } = self.pop() else {
                    panic!("matching a quote value")
                };
                let matching_arm = vec![head_arm]
                    .into_iter()
                    .chain(rest_arms.iter())
                    .find(|arm| arm.constr == constr_name)
                    .unwrap_or_else(|| panic!("unknown constructor: {}", &constr_name));
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
        evaluator.eval_main();
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
        evaluator.eval_main();
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
        evaluator.eval_main();
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
        evaluator.eval_main();
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
        evaluator.eval_main();
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

    #[test]
    fn bury_test() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [] main [Bar, Bar, Foo]: bar bar foo br-2.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main();
        println!("{:?}", evaluator.stack);
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 },
                Value::User { constr_name: ref name2, args: ref args2 },
                Value::User { constr_name: ref name3, args: ref args3 },
            ] if name1 == "foo" && args1.is_empty() &&
                 name2 == "bar" && args2.is_empty() &&
                 name3 == "bar" && args3.is_empty()
        ));
    }

    #[test]
    fn bury_test2() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [] main [Bar, Foo, Bar]: bar bar foo br-1.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main();
        println!("{:?}", evaluator.stack);
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 },
                Value::User { constr_name: ref name2, args: ref args2 },
                Value::User { constr_name: ref name3, args: ref args3 },
            ] if name1 == "bar" && args1.is_empty() &&
                 name2 == "foo" && args2.is_empty() &&
                 name3 == "bar" && args3.is_empty()
        ));
    }

    #[test]
    fn dig_test() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [] main [Bar, Bar, Foo]: foo bar bar dg-2.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main();
        println!("{:?}", evaluator.stack);
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 },
                Value::User { constr_name: ref name2, args: ref args2 },
                Value::User { constr_name: ref name3, args: ref args3 },
            ] if name1 == "bar" && args1.is_empty() &&
                 name2 == "bar" && args2.is_empty() &&
                 name3 == "foo" && args3.is_empty()
        ));
    }

    #[test]
    fn dig_test2() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [] main [Bar, Bar, Foo]: bar foo bar dg-1.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main();
        println!("{:?}", evaluator.stack);
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 },
                Value::User { constr_name: ref name2, args: ref args2 },
                Value::User { constr_name: ref name3, args: ref args3 },
            ] if name1 == "bar" && args1.is_empty() &&
                 name2 == "bar" && args2.is_empty() &&
                 name3 == "foo" && args3.is_empty()
        ));
    }

    #[test]
    fn exec_test() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [Foo, Bar] foobar [Bar, Bar, Bar]:
          case { foo { } } case { bar { } } bar bar bar.
        define [] main [Bar, Bar, Bar]: bar foo (foobar) exec-2-3.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main();
        println!("{:?}", evaluator.stack);
        assert!(matches!(
            &evaluator.stack[..],
            [
                Value::User { constr_name: ref name1, args: ref args1 },
                Value::User { constr_name: ref name2, args: ref args2 },
                Value::User { constr_name: ref name3, args: ref args3 },
            ] if name1 == "bar" && args1.is_empty() &&
                 name2 == "bar" && args2.is_empty() &&
                 name3 == "bar" && args3.is_empty()
        ));
    }

    #[test]
    fn pop_test() {
        let input = "
        data Foo: foo.
        data Bar: bar.
        define [] main []: bar foo pop pop.
        ";
        let module = parse(&input).unwrap();
        let mut evaluator = Evaluator::new(&module);
        evaluator.eval_main();
        println!("{:?}", evaluator.stack);
        assert!(matches!(&evaluator.stack[..], []));
    }
}
