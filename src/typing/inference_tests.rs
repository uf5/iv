use crate::syntax::parse;
use crate::typing::inference::*;

#[test]
fn sanity() {
    let input = "
        define [a, a] nocadd [a]: 1 2 3.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn subst_int_ann_vs_inf() {
    let input = "
        data Alpha:.
        define [a, a] nocadd [a]:.
        define [Alpha, Alpha] intadd [Alpha]: nocadd.";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn ann_ss_pre() {
    let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [a, Alpha] intadd [Alpha]: nocadd.";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn ann_ss_post() {
    let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [Alpha, a] intadd [Alpha]: nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn ann_ss_double() {
    let input = "
        data Alpha: alpha.
        define [a, a] nocadd [a]:.
        define [a, a] intadd [Alpha]: nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn ann_ss_trans_stack() {
    let input = "
        data Alpha: alpha.
        data Beta: beta.
        define [a] nocdup [a, a]:.
        define [Alpha] intadd [Beta, Beta]: nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn ann_ss_trans_stack_ok() {
    let input = "
        data Alpha:. data Beta:.
        data Gamma:. define [a, b, c] nocfoobar [c, b, a]:.
        define [Alpha, Beta, Gamma] intadd [Gamma, Beta, Apha]: nocfoobar.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn uf_triple_add_ok() {
    let input = "
        define [a, a] nocadd [a]:.
        define [a, a, a] tripleadd [a]: nocadd nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn uf_triple_add_ok_spec() {
    let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Alpha] tripleadd [Alpha]: nocadd nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn uf_triple_add_ok_err1() {
    let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Alpha] tripleadd [a]: nocadd nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn uf_triple_add_ok_err2() {
    let input = "
        data Alpha:. data Beta:. define [a, a] nocadd [a]:.
        define [Alpha, Alpha, Beta] tripleadd [Alpha]: nocadd nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn of_triple1() {
    let input = "
        data Alpha:. data Beta:.
        define [a] nocdup [a, a]:.
        define [a] tripledup [a, a, a]: nocdup nocdup.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn op_triple2() {
    let input = "
        data Alpha:. data Beta:.
        define [a, a] nocadd [a]:.
        define [a] nocdup [a, a]:.
        define [a] tripledup [a, a, a]: nocdup nocdup nocadd nocdup.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn int_add_uf_chain() {
    let input = "
        data Alpha: alpha. define [a, a] nocadd [a]:.
        define [Alpha] alphainc [Alpha]: alpha nocadd.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn int_add_datapoly() {
    let input = "
        data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either Alpha b]: alpha left.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_ok());
}

#[test]
fn int_add_datapoly_err() {
    let input = "
        data Alpha: alpha.
        data Either a b: [a] left, [b] right.
        define [] inteithertest [Either a Alpha]: alpha left.
        ";
    let module = parse(&input).unwrap();
    assert!(Inference::new(&module).typecheck().is_err());
}

#[test]
fn case_maybe_nat() {
    let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Maybe Nat] incnatmaybe [Maybe Nat]: case { just { suc just }, nothing { nothing } }.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn case_maybe_nat_add_nop_expansion_err() {
    let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { just { nocswap nocdup nocdup nocrot nocnatadd just }, nothing { nothing } }.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn case_maybe_nat_add_nop_expansion() {
    let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { just { nocswap nocdup nocrot nocnatadd just }, nothing { nothing } }.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn case_maybe_nat_add_nop_expansion_arms_swapped() {
    let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { nothing { nothing }, just { nocswap nocdup nocrot nocnatadd just } }.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn case_maybe_nat_add_nop_expansion_wrong_constr() {
    let input = "
        data Nat: zero, [Nat] suc.
        data Maybe a: nothing, [a] just.
        data Either a b: [a] left, [b] right.
        define [Nat, Nat] nocnatadd [Nat]:.
        define [a] nocdup [a, a]:.
        define [a, b, c] nocrot [c, a, b]:.
        define [a, b] nocswap [b, a]:.
        define [Maybe Nat, Nat] addnatmaybe [Maybe Nat, Nat]:
            case { just { nocswap nocdup nocrot nocnatadd just }, left { nothing } }.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn case_totality() {
    let input = "
        data Expr:
            int, float, string, add.
        define [Expr] foobar [Int]:
            case { int {1}, float {2}, string {3}, add {4}}.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn case_totality_err() {
    let input = "
        data Expr:
            int, float, string, add.
        define [Expr] foobar [Int]:
            case { int {1}, float {2}, add {4}}.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn nop_unification_test() {
    let input = "
        define [] nop []:. define [a] foobar [a]: nop.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn nop_unification_test_err() {
    let input = "
        define [a] nocnop [a]:. define [] nop []: nocnop.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn nop_unification_test_err_poly() {
    let input = "
        define [a] nocnonop [a, a]:.
        define [] nop []: nocnonop.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn nop_unification_test_err_mono() {
    let input = "
        data Alpha: alpha.
        data Beta: beta.
        define [Alpha] nocnonop [Beta]:.
        define [] nop []: nocnonop.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn nop_unification_test_complex() {
    let input = "
        data Maybe a: [a] just, nothing.
        data Nat: [Nat] suc, zero.
        define [Maybe Nat] natnop [Maybe Nat]:.
        define [Maybe Nat, Nat] foobar [Maybe Nat, Nat]: natnop.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn op_quote_test() {
    let input = "
        define [] foobar [[][Int, Int, Int]]: (1 2 3).
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn prelude_br_test() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [Bar, Foo, Foo, Foo] foobar [Foo, Foo, Foo, Bar]: br-3.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn prelude_br_test_err() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [Bar, Foo, Foo, Foo] foobar [Foo, Foo, Foo, Bar]: br-2.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn prelude_dg_test() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [Foo, Foo, Foo, Bar] foobar [Bar, Foo, Foo, Foo]: dg-3.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn prelude_dg_test_err() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [Foo, Foo, Foo, Bar] foobar [Bar, Foo, Foo, Foo]: dg-2.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn special_comp_test_dup() {
    let input = "
        data Foo: foo.
        define [] foo [[][Foo, Foo]]: (foo) (dup) comp-0-1-1-2.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_test_dup1() {
    let input = "
        data Foo: foo.
        define [] foo [[a][Foo, a, a]]: (dup) (foo) comp-1-2-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn todo_nop_postfix_ann_vs_inf_bad() {
    let input = "
        data Foo: foo.
        define [] foo [Foo]: dup pop foo.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn special_comp_test_err() {
    let input = "
        data Foo: foo.
        define [] foo [[][Foo, Foo]]: (dup) (foo) comp-1-2-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn special_comp_test_quote() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [] foo [[][Bar, Foo]]: foo quote bar quote comp-0-1-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_test_quote_err() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [] foo [[][Foo, Bar]]: foo quote bar quote comp-0-1-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn special_comp_test2() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [a] id [a]:.
        define [] foo [[Foo][Bar, Foo]]: (id) (bar) comp-1-1-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_test3() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [a] id [a]:.
        define [] foo [[][Bar]]: (bar) (id) comp-0-1-1-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_of() {
    let input = "
        define [] foo [[a][a, a, a]]: (dup) (dup) comp-1-2-1-2.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_of2() {
    let input = "
        data Foo: foo.
        data Bar: bar.
        define [a] id [a]:.
        define [] foo [[a][Bar, a, a]]: (dup) (bar) comp-1-2-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_nei() {
    let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [[a][a]] foo [[a][a]]: (id) comp-1-1-1-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_nop1() {
    let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [[a][a]] foobar [[a][Foo, a]]: (foo) comp-1-1-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_comp_nop2() {
    let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [] foobar []: foo (id) comp-0-1-1-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn special_comp_nop3() {
    let input = "
        data Foo: foo.
        define [a] id [a]:.
        define [] foo []: (id) foobar comp-1-1-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn special_exec() {
    let input = "
        data Foo: foo.
        define [] foo [Foo, Foo, Foo, Foo]: foo (dup dup dup) exec-1-4.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_exec_nei() {
    let input = "
        data Foo: foo.
        define [Foo] foo [Foo, Foo, Foo, Foo]: (dup dup dup) exec-1-4.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn special_exec_nop() {
    let input = "
        data Foo: foo.
        define [] foo [Foo, Foo, Foo, Foo]: foo exec-0-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_err());
}

#[test]
fn prelude_name_lookup_false_positive() {
    let input = "
        define [a] foo-1 [a]:.
        define [b] foo [b]: foo-1.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn nat_list_sum_test() {
    // stateful typechecker exec can infer that the poly is an optype
    let input = "
        data Nat:
          zero,
          [Nat] suc.

        define [Nat, Nat] natsum [Nat]:
          case { zero { },
                 suc { natsum suc },
               }.

        data List a:
          empty,
          [a, List a] cons.

        define [] nop []:.

        define [[a][b], List a] map [List b]:
          br-1
          case { empty { pop empty },
                 cons { br-2 dg-1 dup br-2 map br-2 exec-1-1 cons },
               }.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn nat_list_sum_test2() {
    // stateful typechecker exec cannot infer that the poly is an optype
    let input = "
        data Nat:
          zero,
          [Nat] suc.

        define [Nat, Nat] natsum [Nat]:
          case { zero { },
                 suc { natsum suc },
               }.

        data List a:
          empty,
          [a, List a] cons.

        define [] nop []:.

        define [[a][b], List a] map [List b]:
          br-1
          case { empty { pop empty },
                 cons { dg-2 dup dg-2 br-1 exec-1-1 br-2 map dg-1 cons },
               }.
        ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn nested_case() {
    let input = "
            data Nat: zero, [Nat] suc.
            data Maybe a: nothing, [a] just.
            define [Maybe Nat] nestedcase [Maybe Nat]:
              case { just { case { zero { nothing }, suc { suc just } } }, nothing { nothing } }.
            ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}

#[test]
fn mut_rec_data() {
    let input = "
            data Foo: [Bar] foo.
            data Bar: [Foo] bar.
            ";
    let module = parse(&input).unwrap();
    let inferred = Inference::new(&module).typecheck();
    println!("{:?}", inferred);
    assert!(inferred.is_ok());
}
