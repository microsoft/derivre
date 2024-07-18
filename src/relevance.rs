use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, ExprRef, ExprSet};

// This is map (ByteSet => RegExp); ByteSet is Expr::Byte or Expr::ByteSet,
// and expresses the condition; RegExp is the derivative under that condition.
// Conditions can be overlapping, but should not repeat.
type SymRes = Vec<(ExprRef, ExprRef)>;

#[derive(Clone)]
pub struct RelevanceCache {
    relevance_cache: HashMap<ExprRef, bool>,
    sym_deriv: HashMap<ExprRef, SymRes>,
}

fn swap_each<A: Copy>(v: &mut Vec<(A, A)>) {
    for i in 0..v.len() {
        v[i] = (v[i].1, v[i].0);
    }
}

fn group_by_first<A: PartialEq + Ord + Copy, B: Ord + Copy>(
    mut s: Vec<(A, B)>,
    mut f: impl FnMut(Vec<B>) -> B,
) -> Vec<(A, B)> {
    s.sort_unstable();
    let mut by_set = vec![];
    let mut i = 0;
    while i < s.len() {
        let mut j = i + 1;
        while j < s.len() && s[i].0 == s[j].0 {
            j += 1;
        }
        let len = j - i;
        if len == 1 {
            by_set.push(s[i]);
        } else {
            by_set.push((s[i].0, f(s[i..j].iter().map(|(_, x)| *x).collect())))
        }
        i = j;
    }
    by_set
}

fn simplify(exprs: &mut ExprSet, s: SymRes) -> SymRes {
    let mut s = group_by_first(s, |args| exprs.mk_or(args));
    swap_each(&mut s);
    let mut s = group_by_first(s, |args| exprs.mk_byte_set_or(&args));
    swap_each(&mut s);
    s
}

impl RelevanceCache {
    pub fn new() -> Self {
        RelevanceCache {
            relevance_cache: HashMap::default(),
            sym_deriv: HashMap::default(),
        }
    }

    pub fn num_bytes(&self) -> usize {
        self.relevance_cache.len() * 3 * std::mem::size_of::<isize>()
    }

    fn deriv(&mut self, exprs: &mut ExprSet, e: ExprRef) -> SymRes {
        exprs.map(
            e,
            &mut self.sym_deriv,
            |e| e,
            |exprs, mut deriv, e| match exprs.get(e) {
                Expr::EmptyString => vec![],
                Expr::NoMatch => vec![],
                Expr::Byte(_) => vec![(e, ExprRef::EMPTY_STRING)],
                Expr::ByteSet(_) => vec![(e, ExprRef::EMPTY_STRING)],

                // just unwrap lookaheads
                Expr::Lookahead(_, _, _) => deriv.pop().unwrap(),

                Expr::And(_, _) => {
                    let mut acc = deriv.pop().unwrap();
                    while let Some(other) = deriv.pop() {
                        let mut new_acc = vec![];
                        for (b0, r0) in &acc {
                            for (b1, r1) in &other {
                                let b = exprs.mk_byte_set_and(*b0, *b1);
                                if b != ExprRef::NO_MATCH {
                                    let r = exprs.mk_and(vec![*r0, *r1]);
                                    if r != ExprRef::NO_MATCH {
                                        new_acc.push((b, r));
                                    }
                                }
                            }
                        }
                        acc = new_acc;
                    }
                    simplify(exprs, acc)
                }

                Expr::Or(_, _) => simplify(exprs, deriv.into_iter().flatten().collect()),

                Expr::Not(_, _) => {
                    let tmp = deriv[0]
                        .iter()
                        .map(|(b, r)| (exprs.mk_byte_set_not(*b), exprs.mk_not(*r)))
                        .collect();
                    simplify(exprs, tmp)
                }

                Expr::Repeat(_, e, min, max) => {
                    let max = if max == u32::MAX {
                        u32::MAX
                    } else {
                        max.saturating_sub(1)
                    };
                    let tail = exprs.mk_repeat(e, min.saturating_sub(1), max);
                    let tmp = deriv[0]
                        .iter()
                        .map(|(b, r)| (*b, exprs.mk_concat(vec![*r, tail])))
                        .collect();
                    simplify(exprs, tmp)
                }
                Expr::Concat(_, args) => {
                    let mut or_branches = vec![];
                    let args = args.to_vec();
                    for i in 0..args.len() {
                        let nullable = exprs.is_nullable(args[i]);
                        or_branches.extend(deriv[i].iter().map(|(b, r)| {
                            let mut cc = vec![*r];
                            cc.extend_from_slice(&args[i + 1..]);
                            (*b, exprs.mk_concat(cc))
                        }));
                        if nullable {
                            break;
                        }
                    }
                    simplify(exprs, or_branches)
                }
            },
        )
    }

    pub fn is_relevant(&mut self, exprs: &mut ExprSet, top_expr: ExprRef) -> bool {
        if exprs.is_positive(top_expr) {
            return true;
        }
        if let Some(r) = self.relevance_cache.get(&top_expr) {
            return *r;
        }

        // TODO limit by size somehow...

        let mut pending = HashSet::new();
        let mut front_wave = vec![top_expr];
        pending.insert(top_expr);

        loop {
            let mut d = vec![];
            for e in &front_wave {
                d.extend_from_slice(&self.deriv(exprs, *e));
            }

            front_wave.clear();
            for (_, r) in &d {
                if !pending.contains(r) {
                    if exprs.is_positive(*r) {
                        self.relevance_cache.insert(top_expr, true);
                        return true;
                    }
                    pending.insert(*r);
                    front_wave.push(*r);
                }
            }

            if front_wave.is_empty() {
                self.relevance_cache.insert(top_expr, false);
                return false;
            }
        }
    }
}
