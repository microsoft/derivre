use std::{
    collections::{HashMap, HashSet},
    usize,
};

use anyhow::Result;

use crate::ast::{Expr, ExprRef, ExprSet};

// This is map (ByteSet => RegExp); ByteSet is Expr::Byte or Expr::ByteSet,
// and expresses the condition; RegExp is the derivative under that condition.
// Conditions can be overlapping, but should not repeat.
//
// deriv(R) = [(S0,C0),...,(Sn,Cn)]
//   means that
// deriv(byte, R) = Ca | Cb ... when byte ∈ Sa and byte ∈ Sb[byte]
// There is an implicit Sn+1 = Σ \ ⋃Si with Cn+1 = NO_MATCH
type SymRes = Vec<(ExprRef, ExprRef)>;

const DEBUG: bool = true;
macro_rules! debug {
    ($($arg:tt)*) => {
        if DEBUG {
            eprint!("  ");
            eprintln!($($arg)*);
        }
    };
}

#[derive(Clone)]
pub struct RelevanceCache {
    relevance_cache: HashMap<ExprRef, bool>,
    sym_deriv: HashMap<ExprRef, SymRes>,
    max_fuel: u64,
    cost_limit: u64,
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
    exprs.pay(s.len());
    let mut s = group_by_first(s, |args| exprs.mk_or(args));
    swap_each(&mut s);
    let mut s = group_by_first(s, |args| exprs.mk_byte_set_or(&args));
    swap_each(&mut s);
    s
}

fn make_disjoint(exprs: &mut ExprSet, inp: &SymRes) -> SymRes {
    // invariant: bytesets in res are all disjoint
    let mut res: SymRes = vec![];
    'input: for (mut a, av) in inp {
        let av = *av;
        // only iterate over items from previous step
        // for each previous item, intersect it with the current item
        // and store the results if any
        let len0 = res.len();
        for idx in 0..len0 {
            let (b, bv) = res[idx];

            // we've got lucky - direct match
            if a == b {
                res[idx] = (a, exprs.mk_or(vec![av, bv]));
                continue 'input;
            }

            let a_and_b = exprs.mk_byte_set_and(a, b);
            if a_and_b == ExprRef::NO_MATCH {
                // this item doesn't intersect with the current one
                continue;
            }

            // replace previous b with a&b -> av|ab
            res[idx] = (a_and_b, exprs.mk_or(vec![av, bv]));
            let b_sub_a = exprs.mk_byte_set_sub(b, a);
            if b_sub_a != ExprRef::NO_MATCH {
                // also add b-a -> bv (if non-empty)
                res.push((b_sub_a, bv));
            }

            // a&b was already handled - remove from a
            a = exprs.mk_byte_set_sub(a, a_and_b);
            if a == ExprRef::NO_MATCH {
                continue 'input;
            }
        }

        assert!(a != ExprRef::NO_MATCH);
        // store the left-overs
        res.push((a, av));
    }

    res
}

impl RelevanceCache {
    pub fn new() -> Self {
        RelevanceCache {
            relevance_cache: HashMap::default(),
            sym_deriv: HashMap::default(),
            cost_limit: u64::MAX,
            max_fuel: u64::MAX,
        }
    }

    pub fn num_bytes(&self) -> usize {
        self.relevance_cache.len() * 3 * std::mem::size_of::<isize>()
    }

    fn deriv(&mut self, exprs: &mut ExprSet, e: ExprRef) -> SymRes {
        exprs.map(
            e,
            &mut self.sym_deriv,
            true,
            |e| e,
            |exprs, mut deriv, e| {
                let r = match exprs.get(e) {
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
                                        debug!(
                                            "  and: {} & {}",
                                            exprs.expr_to_string(*r0),
                                            exprs.expr_to_string(*r1)
                                        );
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
                        let inner_deriv = make_disjoint(exprs, &deriv[0]);
                        debug!(
                            "  disjoint: ==> {:?}",
                            inner_deriv
                                .iter()
                                .map(|(b, r)| (exprs.expr_to_string(*b), exprs.expr_to_string(*r)))
                                .collect::<Vec<_>>()
                        );
                        let mut negated_deriv = inner_deriv
                            .iter()
                            .map(|(b, r)| (*b, exprs.mk_not(*r)))
                            .collect::<Vec<_>>();
                        let left_over = exprs.mk_byte_set_neg_or(
                            &deriv[0].iter().map(|(b, _)| *b).collect::<Vec<_>>(),
                        );
                        if left_over != ExprRef::NO_MATCH {
                            negated_deriv.push((left_over, ExprRef::ANY_BYTE_STRING));
                        }
                        simplify(exprs, negated_deriv)
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
                            if !nullable {
                                break;
                            }
                        }
                        simplify(exprs, or_branches)
                    }
                };
                exprs.pay(r.len());
                debug!(
                    "deriv: {:?} -> {:?}",
                    exprs.expr_to_string(e),
                    r.iter()
                        .map(|(b, r)| (exprs.expr_to_string(*b), exprs.expr_to_string(*r)))
                        .collect::<Vec<_>>()
                );
                r
            },
        )
    }

    pub fn is_non_empty(&mut self, exprs: &mut ExprSet, top_expr: ExprRef) -> bool {
        self.is_non_empty_limited(exprs, top_expr, u64::MAX)
            .unwrap()
    }

    // check if
    //   small ⊆ Prefixes((main & ~except) suffix)
    fn except_keywords(
        &mut self,
        exprs: &mut ExprSet,
        small: ExprRef,
        main: ExprRef,
        except: ExprRef,
        _suffix: ExprRef,
    ) -> Option<bool> {
        match (exprs.get(small), exprs.get(main)) {
            (Expr::Repeat(_, small_ch, _, small_high), Expr::Repeat(_, main_ch, _, main_high))
                if small_high <= main_high && 2 < main_high =>
            {
                if !or_branches(exprs, &[except])
                    .iter()
                    .all(|c| simple_length(exprs, *c).unwrap_or(usize::MAX) < main_high as usize)
                {
                    println!(" -> len, nonempty");
                    return None;
                }

                println!(
                    "check {} in {}",
                    exprs.expr_to_string(small_ch),
                    exprs.expr_to_string(main_ch)
                );

                if !self.check_contains(exprs, small_ch, main_ch) {
                    println!(" -> rec, nonempty");
                    return None;
                } else {
                    println!(" -> rec, empty");
                }

                println!(" -> empty");
                return Some(true);
            }
            _ => {
                println!(" -> no repeat");
                None
            }
        }
    }

    fn check_contains(&mut self, exprs: &mut ExprSet, small: ExprRef, big: ExprRef) -> bool {
        if small == big {
            return true;
        }
        let cont = exprs.mk_contains(small, big);
        self.is_non_empty_inner(exprs, cont).unwrap_or(true) == false
    }

    fn quick_empty(&mut self, exprs: &mut ExprSet, top_expr: ExprRef) -> Option<bool> {
        println!("checking empty: {}", exprs.expr_to_string(top_expr));

        if let Some((small, b)) = a_and_not_b(exprs, top_expr) {
            if small == b {
                println!(" -> eq, empty");
                return Some(true);
            }
            match exprs.get(b) {
                Expr::Not(_, big) => { // PRTODO
                    // we're checking small ⊆ big, which is
                    //   small & ~prefixes(big) = empty
                    if let Some((main, except)) = a_and_not_b(exprs, big) {
                        // here, big = main & ~except
                        match (exprs.get(main), exprs.get(except)) {
                            (Expr::Concat(_, [main, suff0]), Expr::Concat(_, [except, suff2]))
                                if suff0 == suff2 =>
                            {
                                return self.except_keywords(exprs, small, *main, *except, *suff0);
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }

        println!(" -> no match");
        return None;
    }

    pub fn is_non_empty_limited(
        &mut self,
        exprs: &mut ExprSet,
        top_expr: ExprRef,
        max_fuel: u64,
    ) -> Result<bool> {
        self.max_fuel = max_fuel;
        self.cost_limit = exprs.cost().saturating_add(max_fuel);
        self.is_non_empty_inner(exprs, top_expr)
    }

    fn is_non_empty_inner(&mut self, exprs: &mut ExprSet, top_expr: ExprRef) -> Result<bool> {
        if exprs.is_positive(top_expr) {
            return Ok(true);
        }
        if let Some(r) = self.relevance_cache.get(&top_expr) {
            return Ok(*r);
        }

        if let Some(_r) = self.quick_empty(exprs, top_expr) {
            //self.relevance_cache.insert(top_expr, !r);
            //return Ok(!r);
        }

        // if A=>[B,C] is in makes_relevant, then if A is marked relevant, so should B and C
        let mut makes_relevant: HashMap<ExprRef, Vec<ExprRef>> = HashMap::default();
        let mut pending = HashSet::new();
        let mut front_wave = vec![top_expr];
        pending.insert(top_expr);

        debug!("\nstart relevance: {}", exprs.expr_to_string(top_expr));

        loop {
            debug!("wave: {:?}", front_wave);
            // println!("wave: {}", front_wave.len());
            let mut new_wave = vec![];
            for e in &front_wave {
                let dr = self.deriv(exprs, *e);
                exprs.pay(dr.len());
                for (_, r) in dr {
                    if exprs.is_positive(r) || self.relevance_cache.get(&r) == Some(&true) {
                        debug!(
                            "  -> found relevant: {} pos={}",
                            exprs.expr_to_string(r),
                            exprs.is_positive(r)
                        );
                        let mut mark_relevant = vec![*e];
                        while let Some(e) = mark_relevant.pop() {
                            if self.relevance_cache.contains_key(&e) {
                                continue;
                            }
                            self.relevance_cache.insert(e, true);
                            if let Some(lst) = makes_relevant.get(&e) {
                                mark_relevant.extend_from_slice(lst);
                            }
                        }
                        assert!(self.relevance_cache[&top_expr] == true);
                        debug!("relevant: {:?}", top_expr);
                        // println!("cost: {}", exprs.cost() - c0);
                        return Ok(true);
                    }

                    makes_relevant.entry(r).or_insert_with(Vec::new).push(*e);

                    if !pending.contains(&r) {
                        // println!("  add {}", exprs.expr_to_string(r));
                        debug!("  add: {:?}", r);
                        pending.insert(r);
                        new_wave.push(r);
                    }
                }
            }

            front_wave = new_wave;

            if front_wave.is_empty() {
                debug!("irrelevant: {:?}", top_expr);
                for e in pending {
                    self.relevance_cache.insert(e, false);
                }
                assert!(self.relevance_cache[&top_expr] == false);
                // println!("cost: {}", exprs.cost() - c0);
                return Ok(false);
            }

            anyhow::ensure!(
                exprs.cost() <= self.cost_limit,
                "maximum relevance check fuel {} exceeded",
                self.max_fuel
            );
        }
    }
}

fn a_and_not_b(exprs: &ExprSet, e: ExprRef) -> Option<(ExprRef, ExprRef)> {
    match exprs.get(e) {
        Expr::And(_, [a1, a2]) => match (exprs.get(*a1), exprs.get(*a2)) {
            (Expr::Not(_, a), _) => Some((*a2, a)),
            (_, Expr::Not(_, a)) => Some((*a1, a)),
            _ => None,
        },
        _ => None,
    }
}

fn or_branches<'a>(exprs: &'a ExprSet, e: &'a [ExprRef]) -> &'a [ExprRef] {
    assert!(e.len() == 1);
    match exprs.get(e[0]) {
        Expr::Or(_, args) => args,
        _ => e,
    }
}

fn simple_length(exprs: &ExprSet, e: ExprRef) -> Option<usize> {
    match exprs.get(e) {
        Expr::ByteSet(_) | Expr::Byte(_) => Some(1),
        Expr::EmptyString => Some(0),
        Expr::Concat(_, args) => {
            let mut sum = 0;
            for a in args {
                if let Some(l) = simple_length(exprs, *a) {
                    sum += l;
                } else {
                    return None;
                }
            }
            Some(sum)
        }
        _ => None,
    }
}
