use egg::*;

fn main() {
    println!("Hello, world!");
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
        rewrite!("ka-dist-l"; "(seq ?p (par ?q ?r))" <=> "(seq (par ?p ?q) (par ?p ?r))"),
        rewrite!("ka-dist-r"; "(seq (par ?p ?q) ?r)" <=> "(seq (par ?p ?r) (par ?q ?r))"),
        rewrite!("ka-unroll-l"; "(par (test 1) (seq ?p (star ?p)))" <=> "(star ?p)"),
        rewrite!("ka-unroll-r"; "(par (test 1) (seq (star ?p) ?p))" <=> "(star ?p)"),
        // boolean algebra (copy of ka laws, not bothering with * laws)
        rewrite!("ba-and-assoc"; "(and ?a (and ?b ?c))" <=> "(and (and ?a ?b) ?c)"),
        rewrite!("ba-dist-l"; "(and ?a (or ?b ?c))" <=> "(and (or ?a ?b) (or ?a ?c))"),
        rewrite!("ba-dist-r"; "(and (or ?a ?b) ?c)" <=> "(and (or ?a ?c) (or ?b ?c))"),
        // boolean algebra (ba laws)
        rewrite!("ba-plus-dist"; "(or ?a (and ?b ?c))" <=> "(and (or ?a ?b) (or ?a ?c))"),
        // test congruence
        rewrite!("ba-sub-ka-zero"; "(test 0)" <=> "0"),
        rewrite!("ba-sub-ka-one"; "(test 1)" <=> "1"),
        rewrite!("ba-sub-ka-par"; "(test (or ?a ?b))" <=> "(par (test ?a) (test ?b))"),
        rewrite!("ba-sub-ka-seq"; "(test (and ?a ?b))" <=> "(seq (test ?a) (test ?b))"),

        vec![rewrite!("ka-plus-assoc"; "(par ?p (par ?q ?r))" => "(par (par ?p ?q) ?r)"),
             rewrite!("ka-plus-comm"; "(par ?p ?q)" => "(par ?q ?p)"),
             rewrite!("ka-plus-zero"; "(par ?p 0)" => "?p"),
             rewrite!("ka-plus-idem"; "(par ?p ?p)" => "?p"),
             rewrite!("ka-seq-one"; "(seq (test 1) ?p)" => "?p"),
             rewrite!("ka-one-seq"; "(seq ?p (test 1))" => "?p"),
             rewrite!("ka-seq-zero"; "(seq (test 0) ?p)" => "(test 0)"),
             rewrite!("ka-zero-seq"; "(seq ?p (test 0))" => "(test 0)"),
             // KA-LFP-L     q + pr <= r implies p*q <= r
             multi_rewrite!("ka-lfp-l"; "?r = (par (par ?q (seq ?p ?r)) ?r)" => "?r = (par (seq (star ?p) ?q) ?r)"),
             // KA-LFP-R     p + qr <= q implies pr* <= q
             multi_rewrite!("ka-lfp-r"; "?q = (par (par ?p (seq ?q ?r)) ?q)" => "?q = (par (seq ?p (star ?r)) ?q)"),
             // boolean algebra (copies of ka laws)
             rewrite!("ba-plus-assoc"; "(or ?a (or ?b ?r))" => "(or (or ?a ?b) ?r)"),
             rewrite!("ba-plus-comm"; "(or ?a ?b)" => "(or ?b ?a)"),
             rewrite!("ba-plus-zero"; "(or ?a 0)" => "?a"),
             rewrite!("ba-plus-idem"; "(or ?a ?a)" => "?a"),
             rewrite!("ba-and-one"; "(and 1 ?a)" => "?a"),
             rewrite!("ba-one-and"; "(and ?a 1)" => "?a"),
             rewrite!("ba-and-zero"; "(and 0 ?a)" => "0"),
             rewrite!("ba-zero-and"; "(and ?a 0)" => "0"),
             // boolean algebra (ba laws)
             rewrite!("ba-plus-one"; "(or ?a 1)" => "1"),
             rewrite!("ba-excl-mid"; "(or ?a (not ?a))" => "1"),
             rewrite!("ba-seq-comm"; "(and ?a ?b)" => "(and ?b ?a)"),
             rewrite!("ba-contra"; "(and ?a (not ?a))" => "0"),
             rewrite!("ba-seq-idem"; "(and ?a ?a)" => "?a"),
        ],
    ].concat()
}

egg::test_fn! { star_test, rules(),
  "(star (test alpha))" => 
  "(star (test alpha))", 
  "(par (test 1) (seq (test alpha) (star (test alpha))))",
  "(test 1)" }
