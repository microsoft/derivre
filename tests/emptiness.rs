use derivre::{Regex, RegexAst, RegexBuilder};

fn mk_and(a: &str, b: &str) -> Regex {
    let mut bld = RegexBuilder::new();
    let a = RegexAst::ExprRef(bld.mk_regex(a).unwrap());
    let b = RegexAst::ExprRef(bld.mk_regex(b).unwrap());
    let r = bld.mk(&RegexAst::And(vec![a, b])).unwrap();
    bld.to_regex(r)
}

fn check_empty(a: &str, b: &str) {
    let mut r = mk_and(a, b);
    assert!(r.initial_state().is_dead());

    let mut r = Regex::new(a).unwrap();
    assert!(!r.initial_state().is_dead());

    let mut r = Regex::new(b).unwrap();
    assert!(!r.initial_state().is_dead());
}

fn check_non_empty(a: &str, b: &str) {
    let mut r = mk_and(a, b);
    assert!(!r.initial_state().is_dead());
}

#[test]
fn test_relevance() {
    check_non_empty(r"[a-z]*X", r"[a-b]*X");
    check_empty(r"[a-z]*X", r"[a-z]*Y");
    check_empty(r"[a-z]+X", r"[a-z]+Y");
    check_non_empty(r"[a-z]+X", r"[a-z]+[XY]");
    check_non_empty(r"[a-z]+X", r"[a-z]+q*X");
}
