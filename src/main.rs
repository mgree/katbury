use std::{num::ParseFloatError, str::FromStr, time::Duration};

use egg::*;

use clap::Parser;

fn try_parse_secs(s: &str) -> Result<Duration, ParseFloatError> {
    let f = f32::from_str(s)?;
    Ok(Duration::from_secs_f32(f))
}

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Term to rewrite
    #[clap(value_parser)]
    terms: Vec<String>,

    #[clap(long, default_value = "5.0", parse(try_from_str = try_parse_secs))]
    time_limit: Duration,

    #[clap(long, default_value_t = 30)]
    iter_limit: usize,

    #[clap(long, default_value_t = 10_000)]
    node_limit: usize,

    #[clap(long, action)]
    explanations: bool,
}

fn main() {
    let args = Args::parse();

    let mut runner = Runner::default()
        .with_time_limit(args.time_limit)
        .with_iter_limit(args.iter_limit);

    runner = if args.explanations {
        runner.with_explanations_enabled()
    } else {
        runner
    };

    for s in args.terms {
        let term: RecExpr<KAT> = s.parse().unwrap();
        runner = runner.with_expr(&term);
    }

    let runner = runner.run(&rules());

    let extractor = Extractor::new(&runner.egraph, AstSize);

    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    runner.print_report();
    println!("best result: {}", best_expr);
}

define_language! {
    enum KAT {
        "0" = Zero,
        "1" = One,
        "not" = Not(Id),
        "or" = Or([Id; 2]),
        "and" = And([Id; 2]),
        "test" = Test(Id),
        "par" = Par([Id; 2]),
        "seq" = Seq([Id; 2]),
        "star" = Star(Id),
        Var(Symbol),
    }
}

/// Here's the intended grammar of KAT in s-expressions:
/// 
/// tests   a,b,c ::= 0 | 1 | (not a) | (or a b) | (and a b)
/// actions p,q,r ::= (test a) | (par p q) | (seq p q) | (star p)
#[rustfmt::skip]
fn rules() -> Vec<Rewrite<KAT, ()>> {
    vec![
        // bidirctional rules
        // which of these do we really want to be bidirectional?
        rewrite!("ka-seq-assoc"; "(seq ?p (seq ?q ?r))" <=> "(seq (seq ?p ?q) ?r)"),
        rewrite!("ka-dist-l"; "(seq ?p (par ?q ?r))" <=> "(par (seq ?p ?q) (seq ?p ?r))"),
        rewrite!("ka-dist-r"; "(seq (par ?p ?q) ?r)" <=> "(par (seq ?p ?r) (seq ?q ?r))"),
        rewrite!("ka-unroll-l"; "(par (test 1) (seq ?p (star ?p)))" <=> "(star ?p)"),
        rewrite!("ka-unroll-r"; "(par (test 1) (seq (star ?p) ?p))" <=> "(star ?p)"),
        // boolean algebra (copy of ka laws, not bothering with * laws)
        rewrite!("ba-and-assoc"; "(and ?a (and ?b ?c))" <=> "(and (and ?a ?b) ?c)"),
        rewrite!("ba-dist-l"; "(and ?a (or ?b ?c))" <=> "(and (or ?a ?b) (or ?a ?c))"),
        rewrite!("ba-dist-r"; "(and (or ?a ?b) ?c)" <=> "(and (or ?a ?c) (or ?b ?c))"),
        // boolean algebra (ba laws)
        rewrite!("ba-or-dist"; "(or ?a (and ?b ?c))" <=> "(and (or ?a ?b) (or ?a ?c))"),
        // test congruence
        rewrite!("ba-sub-ka-par"; "(test (or ?a ?b))" <=> "(par (test ?a) (test ?b))"),
        rewrite!("ba-sub-ka-seq"; "(test (and ?a ?b))" <=> "(seq (test ?a) (test ?b))"),

        vec![rewrite!("ka-par-assoc"; "(par ?p (par ?q ?r))" => "(par (par ?p ?q) ?r)"),
             rewrite!("ka-par-comm"; "(par ?p ?q)" => "(par ?q ?p)"),
             rewrite!("ka-par-zero"; "(par ?p (test 0))" => "?p"),
             rewrite!("ka-par-idem"; "(par ?p ?p)" => "?p"),
             rewrite!("ka-seq-one"; "(seq (test 1) ?p)" => "?p"),
             rewrite!("ka-one-seq"; "(seq ?p (test 1))" => "?p"),
             rewrite!("ka-seq-zero"; "(seq (test 0) ?p)" => "(test 0)"),
             rewrite!("ka-zero-seq"; "(seq ?p (test 0))" => "(test 0)"),
             // KA-LFP-L     q + pr <= r implies p*q <= r
             multi_rewrite!("ka-lfp-l"; "?r = (par (par ?q (seq ?p ?r)) ?r)" => "?r = (par (seq (star ?p) ?q) ?r)"),
             // KA-LFP-R     p + qr <= q implies pr* <= q
             multi_rewrite!("ka-lfp-r"; "?q = (par (par ?p (seq ?q ?r)) ?q)" => "?q = (par (seq ?p (star ?r)) ?q)"),
             // boolean algebra (copies of ka laws)
             rewrite!("ba-or-assoc"; "(or ?a (or ?b ?c))" => "(or (or ?a ?b) ?c)"),
             rewrite!("ba-or-comm"; "(or ?a ?b)" => "(or ?b ?a)"),
             rewrite!("ba-or-zero"; "(or ?a 0)" => "?a"),
             rewrite!("ba-or-idem"; "(or ?a ?a)" => "?a"),
             rewrite!("ba-and-one"; "(and 1 ?a)" => "?a"),
             rewrite!("ba-one-and"; "(and ?a 1)" => "?a"),
             rewrite!("ba-and-zero"; "(and 0 ?a)" => "0"),
             rewrite!("ba-zero-and"; "(and ?a 0)" => "0"),
             // boolean algebra (ba laws)
             rewrite!("ba-or-one"; "(or ?a 1)" => "1"),
             rewrite!("ba-excl-mid"; "(or ?a (not ?a))" => "1"),
             rewrite!("ba-and-comm"; "(and ?a ?b)" => "(and ?b ?a)"),
             rewrite!("ba-contra"; "(and ?a (not ?a))" => "0"),
             rewrite!("ba-and-idem"; "(and ?a ?a)" => "?a"),
             // KAT proof requires invention
             rewrite!("not-zero"; "(not 0)" => "1"),
             rewrite!("not-one"; "(not 1)" => "0"),
             // saving ourselves trouble
             multi_rewrite!("ka-le-le"; "?r = (par ?q ?r), ?q = (par ?q ?r)" => "?r = ?q"),
        ],
    ].concat()
}

egg::test_fn! { not_zero, rules(),
    "(test (not 0))" =>
    "(test 1)",
}

egg::test_fn! { not_one, rules(),
    "(test (not 1))" =>
    "(test 0)",
}

egg::test_fn! { #[ignore] double_neg, rules(),
  "(test (not (not a)))" =>
  "(test a)"
}

egg::test_fn! { one_le_star, rules(),
  "(par (test 1) (star p))" =>
  "(star p)"
}

egg::test_fn! { star_test, rules(),
  "(star (test alpha))" =>
  "(star (test alpha))",
  "(par (test 1) (seq (test alpha) (star (test alpha))))",
  "(test 1)"
}

egg::test_fn! { #[ignore] star_star, rules(),
  "(star (star pi))" =>
  "(star pi)"
}

egg::test_fn! {#[ignore] denesting, rules(),
  runner = Runner::new(Default::default())
    .with_time_limit(Duration::from_secs(30))
    .with_iter_limit(100)
    .with_node_limit(100_000)
    .with_explanations_enabled(),
  "(star (par p q))" =>
  "(star (par p q))",
  "(seq (star p) (star (seq q (star p))))"
}

egg::test_fn! {#[ignore] denesting_swap, rules(),
    runner = Runner::new(Default::default())
    .with_time_limit(Duration::from_secs(30))
    .with_iter_limit(100)
    .with_node_limit(100_000)
    .with_explanations_enabled(),
  "(seq (star p) (star (seq q (star p))))" =>
  "(star (par p q))"
}

egg::test_fn! {#[ignore] denesting_swap_bogus, rules(),
    runner = Runner::new(Default::default())
    .with_time_limit(Duration::from_secs(30))
    .with_iter_limit(100)
    .with_node_limit(100_000)
    .with_explanations_enabled(),
  "(seq (star p) (star (seq q (star p))))" =>
  "(par (star p) q)"
}

egg::test_fn! {#[ignore] denesting_l, rules(),
  runner = Runner::new(Default::default())
            .with_time_limit(Duration::from_secs(30))
            .with_iter_limit(100)
            .with_node_limit(100_000)
            .with_explanations_enabled(),
  "(par (star (par p q)) (seq (star p) (star (seq q (star p)))))" =>
  "(seq (star p) (star (seq q (star p)))))"
}

// 1 + (p+q) \cdot p^*\cdot(q \cdot p^*)^*
// \le
// p^* \cdot (q \cdot p^*)^*
egg::test_fn! { denest_l_unrolled, rules(),
  runner = Runner::new(Default::default())
            .with_time_limit(Duration::from_secs(30))
            .with_iter_limit(100)
            .with_node_limit(100_000)
            .with_explanations_enabled(),
  "(par (par (test 1) (seq (par p q) (seq (star p) (star (seq q (star p)))))) (seq (star p) (star (seq q (star p)))))" =>
  "(seq (star p) (star (seq q (star p))))"
}

egg::test_fn! { denesting_l_a, rules(),
  "(par (test 1) (seq (star p) (star (seq q (star p)))))" =>
  "(seq (star p) (star (seq q (star p))))"
}

egg::test_fn! { denest_l_b, rules(),
  "(par (seq p (seq (star p) (star (seq q (star p))))) (seq (star p) (star (seq q (star p)))))" =>
  "(seq (star p) (star (seq q (star p))))"
}

egg::test_fn! { denest_l_c1, rules(),
  "(par (seq q (seq (star p) (star (seq q (star p))))) (star (seq q (star p))))" =>
  "(star (seq q (star p))))"
}

egg::test_fn! { denest_l_c2, rules(),
  "(par (star (seq q (star p))) (seq (star p) (star (seq q (star p)))))" =>
  "(seq (star p) (star (seq q (star p))))"
}

egg::test_fn! { denest_l_c, rules(),
  "(par (seq q (seq (star p) (star (seq q (star p))))) (star (seq q (star p))))" =>
  "(star (seq q (star p))))"
}

egg::test_fn! { #[ignore] denesting_r, rules(),
  "(par (star (par p q)) (seq (star p) (star (seq q (star p)))))" =>
  "(star (par p q))"
}

egg::test_fn! { #[ignore] sliding_ltr, rules(),
  "(seq p (star (seq q p)))" =>
  "(seq (star (seq p q)) p)"
}

egg::test_fn! { #[ignore] sliding_rtl, rules(),
  "(seq (star (seq p q)) p)" =>
  "(seq p (star (seq q p)))"
}

egg::test_fn! { star_star_le_star, rules(),
  "(par (star (star pi)) (star pi))" =>
  "(star pi)"
}

egg::test_fn! { star_le_star_star, rules(),
  "(par (star (star pi)) (star pi))" => "(star (star pi))"  
}