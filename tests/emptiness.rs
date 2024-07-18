use derivre::{Regex, RegexAst, RegexBuilder};

fn mk_and(a: &str, b: &str) -> Regex {
    let mut bld = RegexBuilder::new();
    let a = RegexAst::ExprRef(bld.mk_regex(a).unwrap());
    let b = RegexAst::ExprRef(bld.mk_regex(b).unwrap());
    let r = bld.mk(&RegexAst::And(vec![a, b])).unwrap();
    bld.to_regex(r)
}

#[test]
fn test_relevance() {
    let mut r = mk_and(r"[a-z]*X", r"[a-z]*Y");
    assert!(r.initial_state().is_dead());

    let mut r = mk_and(r"[a-z]*X", r"[a-b]*X");
    assert!(!r.initial_state().is_dead());
}
