use std::hash::Hash;

use crate::HashMap;

use crate::{
    ast::{byteset_contains, byteset_set, Expr, ExprSet},
    ExprRef,
};

pub struct ByteCompressor {
    pub mapping: Vec<u8>,
    pub alphabet_size: usize,
    bytesets: Vec<Vec<u32>>,
    map_cache: HashMap<ExprRef, ExprRef>,
}

const INVALID_MAPPING: u8 = 0xff;

impl ByteCompressor {
    pub fn new() -> Self {
        ByteCompressor {
            mapping: Vec::new(),
            alphabet_size: 0,
            bytesets: Vec::new(),
            map_cache: HashMap::default(),
        }
    }

    fn map_expr(&mut self, trg: &mut ExprSet, exprset: &ExprSet, e: ExprRef) -> ExprRef {
        let mut todo = vec![e];

        while let Some(e) = todo.pop() {
            if self.map_cache.contains_key(&e) {
                continue;
            }

            let mut retry = false;
            let mut args = Vec::new();

            for c in exprset.get_args(e) {
                if let Some(&r) = self.map_cache.get(c) {
                    args.push(r);
                } else {
                    if !retry {
                        retry = true;
                        todo.push(e)
                    }
                    todo.push(*c);
                }
            }

            if retry {
                continue;
            }

            let r = match exprset.get(e) {
                Expr::Byte(b) => trg.mk_byte(self.mapping[b as usize]),
                Expr::ByteSet(bs) => {
                    let mut new_bs = vec![0u32; trg.alphabet_words()];
                    for b in 0..exprset.alphabet_size() {
                        if byteset_contains(bs, b) {
                            let m = self.mapping[b as usize] as usize;
                            byteset_set(&mut new_bs, m);
                        }
                    }
                    trg.mk_byte_set(&new_bs)
                }
                Expr::EmptyString => ExprRef::EMPTY_STRING,
                Expr::NoMatch => ExprRef::NO_MATCH,
                Expr::Lookahead(_, _, x) => trg.mk_lookahead(args[0], x),
                Expr::Not(_, _) => trg.mk_not(args[0]),
                Expr::Repeat(_, _, x, y) => trg.mk_repeat(args[0], x, y),
                Expr::RemainderIs {
                    divisor,
                    remainder,
                    scale,
                    fractional_part,
                } => trg.mk_remainder_is(divisor, remainder, scale, fractional_part),
                Expr::ByteConcat(_, bytes, _) => trg.mk_byte_concat(
                    &bytes
                        .iter()
                        .map(|b| self.mapping[*b as usize])
                        .collect::<Vec<_>>(),
                    args[0],
                ),
                Expr::Concat(_, _) => trg.mk_concat(args[0], args[1]),
                Expr::Or(_, _) => trg.mk_or(&mut args),
                Expr::And(_, _) => trg.mk_and(&mut args),
            };
            self.map_cache.insert(e, r);
        }

        self.map_cache[&e]
    }

    fn add_single_byte(&mut self, b: u8) {
        if self.mapping[b as usize] == INVALID_MAPPING {
            self.mapping[b as usize] = self.alphabet_size as u8;
            self.alphabet_size += 1;
        }
    }

    pub fn compress(&mut self, exprset: &ExprSet, rx_list: &[ExprRef]) -> (ExprSet, Vec<ExprRef>) {
        self.mapping = vec![INVALID_MAPPING; exprset.alphabet_size()];

        let mut todo = rx_list.to_vec();
        let mut visited = vec![false; exprset.len()];
        while let Some(e) = todo.pop() {
            if visited[e.as_usize()] {
                continue;
            }
            visited[e.as_usize()] = true;
            todo.extend_from_slice(exprset.get_args(e));
            match exprset.get(e) {
                Expr::Byte(b) => self.add_single_byte(b),
                Expr::ByteConcat(_, bytes, _) => {
                    for b in bytes {
                        self.add_single_byte(*b);
                    }
                }
                Expr::ByteSet(bs) => self.bytesets.push(bs.to_vec()),
                Expr::RemainderIs { scale, .. } => {
                    for b in exprset.digits {
                        self.add_single_byte(b);
                    }
                    // if scale==0 then it will only match integers
                    // and we don't need to distinguish the dot
                    if scale > 0 {
                        self.add_single_byte(exprset.digit_dot);
                    }
                }
                _ => {}
            }
        }

        let num = self.bytesets.len();
        if num <= 64 {
            self.compress_bytesets(|_| 0u64, |v, idx| *v |= 1 << idx);
        } else {
            self.compress_bytesets(
                |size| vec![0u32; (size + 31) / 32],
                |v, idx| v[idx / 32] |= 1 << (idx % 32),
            );
        }

        let mut trg = ExprSet::new(self.alphabet_size);
        // this disables Or->Trie conversion; the input should be already optimized this way
        trg.disable_optimizations();
        for digit in 0..trg.digits.len() {
            trg.digits[digit] = self.mapping[exprset.digits[digit] as usize];
        }
        trg.digit_dot = self.mapping[exprset.digit_dot as usize];
        let res_exprs: Vec<ExprRef> = rx_list
            .iter()
            .map(|&e| self.map_expr(&mut trg, exprset, e))
            .collect();
        (trg, res_exprs)
    }

    #[inline(always)]
    fn compress_bytesets<T: Eq + Hash>(
        &mut self,
        alloc: impl Fn(usize) -> T,
        set_true: impl Fn(&mut T, usize),
    ) {
        let mut byte_mapping = HashMap::default();
        for b in 0..self.mapping.len() {
            if self.mapping[b] == INVALID_MAPPING {
                let mut v = alloc(self.bytesets.len());
                for (idx, bs) in self.bytesets.iter().enumerate() {
                    if byteset_contains(bs, b) {
                        set_true(&mut v, idx);
                    }
                }
                if byte_mapping.contains_key(&v) {
                    self.mapping[b] = *byte_mapping.get(&v).unwrap();
                } else {
                    self.mapping[b] = self.alphabet_size as u8;
                    self.alphabet_size += 1;
                    byte_mapping.insert(v, self.mapping[b as usize]);
                }
            }
        }
    }
}
