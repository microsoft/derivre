use derivre::{Regex, RegexAst, RegexBuilder};

fn mk_and(a: &str, b: &str) -> Regex {
    let mut bld = RegexBuilder::new();
    let a = RegexAst::ExprRef(bld.mk_regex(a).unwrap());
    let b = RegexAst::ExprRef(bld.mk_regex(b).unwrap());
    let r = bld.mk(&RegexAst::And(vec![a, b])).unwrap();
    bld.to_regex(r)
}

fn is_contained_in(small: &str, big: &str) -> bool {
    RegexBuilder::new()
        // .unicode(false)
        // .utf8(false)
        .is_contained_in(small, big)
        .unwrap()
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
    println!("{} in {}", small, big);
    if !is_contained_in(small, big) {
        panic!("{} is not contained in {}", small, big);
    }

    if is_contained_in(big, small) {
        panic!("{} is contained in {}", big, small);
    }
}

fn check_not_contains(small: &str, big: &str) {
    if is_contained_in(small, big) {
        panic!("{} is contained in {}", small, big);
    }
    if is_contained_in(big, small) {
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

    // doesn't seem exponential
    check_empty(r".*A.{135}", r".*B.{135}");
    check_non_empty(r".*A.{135}", r".*B.{134}");
    check_empty(r".*A.{135}", r"[B-Z]+");
    check_non_empty(r".*A.{135}", r"[A-Z]+");
}

/*

*/

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

    check_contains(r"[Bb]*B[Bb]{4}", r"[BQb]*B[Bb]{4}");
    check_contains(r"[B]*B[Bb]", r"[BC]*B[Bb]");

    check_contains(r"[aA]{0,1}A", r"[abA]{0,1}A");
    check_contains(r".*A.{15}", r".+");
    // exponential
    check_contains(r".*A.{10}", r".*[AB].{10}");
}
