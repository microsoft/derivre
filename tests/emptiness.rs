use derivre::{Regex, RegexAst, RegexBuilder};

fn mk_and(a: &str, b: &str) -> Regex {
    let mut bld = RegexBuilder::new();
    let a = RegexAst::ExprRef(bld.mk_regex(a).unwrap());
    let b = RegexAst::ExprRef(bld.mk_regex(b).unwrap());
    let r = bld.mk(&RegexAst::And(vec![a, b])).unwrap();
    bld.to_regex(r)
}

fn mk_contained_in(small: &str, big: &str) -> Regex {
    let mut bld = RegexBuilder::new();
    let small = RegexAst::ExprRef(bld.mk_regex(small).unwrap());
    let big = RegexAst::ExprRef(bld.mk_regex(big).unwrap());
    let r = bld.mk(&small.contained_in(&big)).unwrap();
    bld.to_regex(r)
}

fn check_empty(a: &str, b: &str) {
    let mut r = mk_and(a, b);
    assert!(r.always_empty());

    let mut r = Regex::new(a).unwrap();
    assert!(!r.always_empty());

    let mut r = Regex::new(b).unwrap();
    assert!(!r.always_empty());
}

fn check_non_empty(a: &str, b: &str) {
    let mut r = mk_and(a, b);
    assert!(!r.always_empty());
}

fn check_contains(small: &str, big: &str) {
    let mut r = mk_contained_in(small, big);
    if !r.always_empty() {
        panic!("{} is not contained in {}", small, big);
    }

    let mut r = mk_contained_in(big, small);
    if r.always_empty() {
        panic!("{} is contained in {}", big, small);
    }
}

fn check_not_contains(small: &str, big: &str) {
    let mut r = mk_contained_in(small, big);
    if r.always_empty() {
        panic!("{} is contained in {}", small, big);
    }
    let mut r = mk_contained_in(big, small);
    if r.always_empty() {
        panic!("{} is contained in {}", big, small);
    }
}

#[test]
fn test_relevance() {
    check_non_empty(r"[a-z]*X", r"[a-b]*X");
    check_empty(r"[a-z]*X", r"[a-z]*Y");
    check_empty(r"[a-z]+X", r"[a-z]+Y");
    check_non_empty(r"[a-z]+X", r"[a-z]+[XY]");
    check_non_empty(r"[a-z]+X", r"[a-z]+q*X");
}

#[test]
fn test_contains() {
    check_contains(r"[a-b]", r"[a-z]");
    check_contains(r"[a-b]*", r"[a-z]*");
    check_contains(r"[a-b]+", r"[a-z]+");
    check_contains(r"aX", r"[a-z]X");
    check_contains(r"aX", r"[a-z]*X");
    check_contains(r"[a-b]*X", r"[a-z]*X");

    let json_str = r#"(\\([\"\\\/bfnrt]|u[a-fA-F0-9]{4})|[^\"\\\x00-\x1F\x7F])*"#;
    check_contains(r"[a-z]+", &json_str);
    check_contains(r"[a-z\u{0080}-\u{FFFF}]+", &json_str);
    check_contains(r"[a-zA-Z\u{0080}-\u{10FFFF}]+", &json_str);
    check_contains(r" [a-zA-Z\u{0080}-\u{10FFFF}]*", &json_str);

    check_not_contains(r"[\\a-z\u{0080}-\u{FFFF}]+", &json_str);
    check_not_contains(r#"["a-z\u{0080}-\u{FFFF}]+"#, &json_str);
    check_not_contains(r#"[\na-z\u{0080}-\u{FFFF}]+"#, &json_str);
    check_not_contains(r"[\\a-z]+", &json_str);
}
