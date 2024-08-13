use std::{fmt::Debug, vec};

use anyhow::{ensure, Result};
use regex_syntax::ParserBuilder;

use crate::{
    ast::{
        byteset_256, byteset_clear, byteset_contains, byteset_from_range, byteset_set, Expr,
        ExprSet,
    },
    mapper::map_ast,
    pp::{byte_to_string, byteset_to_string},
    ExprRef, Regex,
};

#[derive(Clone)]
pub struct RegexBuilder {
    parser_builder: ParserBuilder,
    exprset: ExprSet,
}

#[derive(Clone, Debug)]
pub struct JsonQuoteOptions {
    /// Which escapes to allow (after \).
    /// Represents a set of bytes. Allowed bytes:
    /// n, r, b, t, f, \, ", u
    pub allowed_escapes: String,
}

impl Default for JsonQuoteOptions {
    fn default() -> Self {
        Self::simple()
    }
}

impl JsonQuoteOptions {
    pub fn bare() -> Self {
        Self {
            // only \n, \", \\ - probably best match for training data
            allowed_escapes: "n\\\"".to_string(),
        }
    }

    pub fn simple() -> Self {
        Self {
            // \uXXXX, \f, \b not allowed
            allowed_escapes: "nrt\\\"".to_string(),
        }
    }

    pub fn no_unicode() -> Self {
        Self {
            // \uXXXX not allowed
            allowed_escapes: "nrbtf\\\"".to_string(),
        }
    }

    pub fn with_unicode() -> Self {
        Self {
            // allow \uXXXX
            allowed_escapes: "nrbtf\\\"u".to_string(),
        }
    }

    pub fn is_allowed(&self, b: u8) -> bool {
        self.allowed_escapes.as_bytes().contains(&b)
    }

    pub fn set_if_allowed(&self, bs: &mut [u32], b: u8) {
        if self.is_allowed(b) {
            byteset_set(bs, b as usize);
        }
    }
}

#[derive(Clone)]
pub enum RegexAst {
    /// Intersection of the regexes
    And(Vec<RegexAst>),
    /// Union of the regexes
    Or(Vec<RegexAst>),
    /// Concatenation of the regexes
    Concat(Vec<RegexAst>),
    /// Matches the regex; should be at the end of the main regex.
    /// The length of the lookahead can be recovered from the engine.
    LookAhead(Box<RegexAst>),
    /// Matches everything the regex doesn't match.
    /// Can lead to invalid utf8.
    Not(Box<RegexAst>),
    /// Repeat the regex at least min times, at most max times
    /// u32::MAX means infinity
    Repeat(Box<RegexAst>, u32, u32),
    /// Matches the empty string. Same as Concat([]).
    EmptyString,
    /// Matches nothing. Same as Or([]).
    NoMatch,
    /// Compile the regex using the regex_syntax crate
    Regex(String),
    /// Matches this string only
    Literal(String),
    /// Matches this string of bytes only. Can lead to invalid utf8.
    ByteLiteral(Vec<u8>),
    /// Matches this byte only. If byte is not in 0..127, it may lead to invalid utf8
    Byte(u8),
    /// Matches any byte in the set, expressed as bitset.
    /// Can lead to invalid utf8 if the set is not a subset of 0..127
    ByteSet(Vec<u32>),
    /// Reference previously built regex
    ExprRef(ExprRef),
}

impl RegexAst {
    pub fn get_args(&self) -> &[RegexAst] {
        match self {
            RegexAst::And(asts) | RegexAst::Or(asts) | RegexAst::Concat(asts) => asts,
            RegexAst::LookAhead(ast) | RegexAst::Not(ast) | RegexAst::Repeat(ast, _, _) => {
                std::slice::from_ref(ast)
            }
            RegexAst::EmptyString
            | RegexAst::NoMatch
            | RegexAst::Regex(_)
            | RegexAst::Literal(_)
            | RegexAst::ByteLiteral(_)
            | RegexAst::ExprRef(_)
            | RegexAst::Byte(_)
            | RegexAst::ByteSet(_) => &[],
        }
    }

    pub fn tag(&self) -> &'static str {
        match self {
            RegexAst::And(_) => "And",
            RegexAst::Or(_) => "Or",
            RegexAst::Concat(_) => "Concat",
            RegexAst::LookAhead(_) => "LookAhead",
            RegexAst::Not(_) => "Not",
            RegexAst::EmptyString => "EmptyString",
            RegexAst::NoMatch => "NoMatch",
            RegexAst::Regex(_) => "Regex",
            RegexAst::Literal(_) => "Literal",
            RegexAst::ByteLiteral(_) => "ByteLiteral",
            RegexAst::ExprRef(_) => "ExprRef",
            RegexAst::Repeat(_, _, _) => "Repeat",
            RegexAst::Byte(_) => "Byte",
            RegexAst::ByteSet(_) => "ByteSet",
        }
    }

    pub fn write_to_str(&self, dst: &mut String, max_len: usize) {
        let mut todo = vec![Some(self)];
        while let Some(ast) = todo.pop() {
            if dst.len() >= max_len {
                dst.push_str("...");
                break;
            }
            if ast.is_none() {
                dst.push_str(")");
                continue;
            }
            let ast = ast.unwrap();
            dst.push_str(" (");
            dst.push_str(ast.tag());
            todo.push(None);
            match ast {
                RegexAst::And(_)
                | RegexAst::Or(_)
                | RegexAst::Concat(_)
                | RegexAst::LookAhead(_)
                | RegexAst::Not(_) => {}
                RegexAst::Byte(b) => {
                    dst.push_str(" ");
                    dst.push_str(&byte_to_string(*b));
                }
                RegexAst::ByteSet(bs) => {
                    dst.push_str(" ");
                    if bs.len() == 256 / 32 {
                        dst.push_str(&byteset_to_string(&bs));
                    } else {
                        dst.push_str(&format!("invalid byteset len: {}", bs.len()))
                    }
                }
                RegexAst::Regex(s) | RegexAst::Literal(s) => {
                    dst.push_str(&format!(" {:?}", s));
                }
                RegexAst::ByteLiteral(s) => {
                    dst.push_str(&format!(" {:?}", String::from_utf8_lossy(&s)));
                }
                RegexAst::ExprRef(r) => {
                    dst.push_str(&format!(" {:?}", r));
                }
                RegexAst::Repeat(_, min, max) => {
                    dst.push_str(&format!("{{{},{}}} ", min, max));
                }
                RegexAst::EmptyString | RegexAst::NoMatch => {}
            }
            for c in ast.get_args().iter().rev() {
                todo.push(Some(c));
            }
        }
    }
}

impl Debug for RegexAst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.write_to_str(&mut s, 100);
        write!(f, "{}", s)
    }
}

impl RegexBuilder {
    pub fn new() -> Self {
        Self {
            parser_builder: ParserBuilder::new(),
            exprset: ExprSet::new(256),
        }
    }

    pub fn to_regex(&self, r: ExprRef) -> Regex {
        Regex::new_with_exprset(&self.exprset, r)
    }

    pub fn exprset(&self) -> &ExprSet {
        &self.exprset
    }

    pub fn json_quote(&mut self, e: ExprRef, options: &JsonQuoteOptions) -> Result<ExprRef> {
        // returns Some(X) iff b should quoted as \X
        fn quote(b: u8) -> Option<u8> {
            match b {
                b'\\' => Some(b'\\'),
                b'"' => Some(b'"'),
                0x08 => Some(b'b'),
                0x0C => Some(b'f'),
                b'\n' => Some(b'n'),
                b'\r' => Some(b'r'),
                b'\t' => Some(b't'),
                _ => None,
            }
        }

        // byteset of all possible single-char quotes
        fn single_quote_byteset(include_nl: bool, options: &JsonQuoteOptions) -> Vec<u32> {
            let mut quoted_bs = byteset_256();
            for c in b"\"\\bfrt" {
                options.set_if_allowed(&mut quoted_bs, *c);
            }
            if include_nl {
                options.set_if_allowed(&mut quoted_bs, b'n');
            }
            quoted_bs
        }

        // all hex digits, including A or not
        fn hex_byteset(include_nl: bool) -> Vec<u32> {
            let mut hex_bs = byteset_256();
            for c in b"0123456789bcdefBCDEF" {
                byteset_set(&mut hex_bs, *c as usize);
            }
            if include_nl {
                byteset_set(&mut hex_bs, b'A' as usize);
                byteset_set(&mut hex_bs, b'a' as usize);
            }
            hex_bs
        }

        // all control characters, including \n or not
        fn quote_all_ctrl(
            exprset: &mut ExprSet,
            include_nl: bool,
            options: &JsonQuoteOptions,
        ) -> ExprRef {
            let upref = exprset.mk_literal("u00");
            let backslash = exprset.mk_byte(b'\\');
            let single_quote = exprset.mk_byte_set(&single_quote_byteset(include_nl, options));
            let u0000 = if !options.is_allowed(b'u') {
                ExprRef::NO_MATCH
            } else if include_nl {
                let hex0 = exprset.mk_byte_set(&byteset_from_range(b'0', b'1'));
                let hex1 = exprset.mk_byte_set(&hex_byteset(include_nl));
                exprset.mk_concat(vec![upref, hex0, hex1])
            } else {
                let n0 = exprset.mk_byte(b'0');
                let n1 = exprset.mk_byte(b'1');
                let hex0 = exprset.mk_byte_set(&hex_byteset(false));
                let hex0 = exprset.mk_concat(vec![n0, hex0]);
                let hex1 = exprset.mk_byte_set(&hex_byteset(true));
                let hex1 = exprset.mk_concat(vec![n1, hex1]);
                let hex01 = exprset.mk_or(vec![hex0, hex1]);
                exprset.mk_concat(vec![upref, hex01])
            };

            let u_or_single = exprset.mk_or(vec![u0000, single_quote]);
            exprset.mk_concat(vec![backslash, u_or_single])
        }

        fn quote_byteset(
            exprset: &mut ExprSet,
            bs: Vec<u32>,
            options: &JsonQuoteOptions,
        ) -> ExprRef {
            let upref = exprset.mk_literal("u00");
            let backslash = exprset.mk_byte(b'\\');

            let quoted = if bs[0] == 0xffff_ffff & !(1 << 10) {
                // everything except for \n
                quote_all_ctrl(exprset, false, options)
            } else if bs[0] == 0xffff_ffff {
                // everything
                quote_all_ctrl(exprset, true, options)
            } else {
                let mut quoted_bs = byteset_256();
                let mut other_bytes = vec![];
                for b in 0..32 {
                    if byteset_contains(&bs, b) {
                        if let Some(q) = quote(b as u8) {
                            options.set_if_allowed(&mut quoted_bs, q);
                        }
                        if options.is_allowed(b'u') {
                            let other = exprset.mk_literal(&format!("{:02x}", b));
                            other_bytes.push(other);
                            let other = exprset.mk_literal(&format!("{:02X}", b));
                            other_bytes.push(other);
                        }
                    }
                }

                let quoted_bs = exprset.mk_byte_set(&quoted_bs);
                let other_bytes = exprset.mk_or(other_bytes);
                let other_bytes = exprset.mk_concat(vec![upref, other_bytes]);

                let quoted_or_other = exprset.mk_or(vec![quoted_bs, other_bytes]);
                exprset.mk_concat(vec![backslash, quoted_or_other])
            };

            let mut bs_without_ctrl = bs;
            bs_without_ctrl[0] = 0;
            let mut alts = vec![quoted];
            if byteset_contains(&bs_without_ctrl, b'\\' as usize) {
                if options.is_allowed(b'\\') {
                    alts.push(exprset.mk_literal("\\\\"));
                }
                byteset_clear(&mut bs_without_ctrl, b'\\' as usize);
            }
            if byteset_contains(&bs_without_ctrl, b'"' as usize) {
                if options.is_allowed(b'"') {
                    alts.push(exprset.mk_literal("\\\""));
                }
                byteset_clear(&mut bs_without_ctrl, b'"' as usize);
            }
            let bs_without_ctrl = exprset.mk_byte_set(&bs_without_ctrl);
            alts.push(bs_without_ctrl);
            exprset.mk_or(alts)
        }

        let mut error = "";

        let r = self.exprset.simple_map(e, |exprset, args, e| -> ExprRef {
            match exprset.get(e) {
                Expr::EmptyString => ExprRef::EMPTY_STRING,
                Expr::NoMatch => ExprRef::NO_MATCH,
                Expr::ByteSet(bs) => {
                    // if the range doesn't allow any of the characters below 0x20,
                    // we don't need to quote
                    let bs = bs.to_vec();
                    if bs[0] == 0
                        && !byteset_contains(&bs, b'\\' as usize)
                        && !byteset_contains(&bs, b'"' as usize)
                    {
                        exprset.mk_byte_set(&bs)
                    } else {
                        quote_byteset(exprset, bs, &options)
                    }
                }
                Expr::Byte(b) => {
                    if b < 0x20 {
                        quote_byteset(exprset, byteset_from_range(b, b), &options)
                    } else {
                        exprset.mk_byte(b)
                    }
                }
                Expr::And(_, _) => {
                    if error.is_empty() {
                        error = "and";
                    }
                    exprset.mk_and(args)
                }
                Expr::Or(_, _) => exprset.mk_or(args),
                Expr::Concat(_, _) => exprset.mk_concat(args),
                Expr::Not(_, _) => {
                    if error.is_empty() {
                        error = "not";
                    }
                    exprset.mk_not(args[0])
                }
                Expr::Lookahead(_, _, _) => exprset.mk_lookahead(args[0], 0),
                Expr::Repeat(_, _, min, max) => exprset.mk_repeat(args[0], min, max),
            }
        });

        if error.is_empty() {
            Ok(r)
        } else {
            Err(anyhow::anyhow!(
                "unsupported node when JSON-quoting: {}",
                error
            ))
        }
    }

    pub fn mk_regex(&mut self, s: &str) -> Result<ExprRef> {
        let parser = self.parser_builder.build();
        self.exprset.parse_expr(parser, s)
    }

    pub fn mk(&mut self, ast: &RegexAst) -> Result<ExprRef> {
        map_ast(
            ast,
            |ast| ast.get_args(),
            |ast, new_args| {
                let r = match ast {
                    RegexAst::Regex(s) => self.mk_regex(s)?,
                    RegexAst::ExprRef(r) => {
                        ensure!(self.exprset.is_valid(*r), "invalid ref");
                        *r
                    }
                    RegexAst::And(_) => self.exprset.mk_and(new_args),
                    RegexAst::Or(_) => self.exprset.mk_or(new_args),
                    RegexAst::Concat(_) => self.exprset.mk_concat(new_args),
                    RegexAst::Not(_) => self.exprset.mk_not(new_args[0]),
                    RegexAst::LookAhead(_) => self.exprset.mk_lookahead(new_args[0], 0),
                    RegexAst::EmptyString => ExprRef::EMPTY_STRING,
                    RegexAst::NoMatch => ExprRef::NO_MATCH,
                    RegexAst::Literal(s) => self.exprset.mk_literal(s),
                    RegexAst::ByteLiteral(s) => self.exprset.mk_byte_literal(s),
                    RegexAst::Repeat(_, min, max) => {
                        self.exprset.mk_repeat(new_args[0], *min, *max)
                    }
                    RegexAst::Byte(b) => self.exprset.mk_byte(*b),
                    RegexAst::ByteSet(bs) => {
                        ensure!(
                            bs.len() == self.exprset.alphabet_words(),
                            "invalid byteset len"
                        );
                        self.exprset.mk_byte_set(bs)
                    }
                };
                Ok(r)
            },
        )
    }

    pub fn is_nullable(&self, r: ExprRef) -> bool {
        self.exprset.is_nullable(r)
    }
}

// regex flags; docs copied from regex_syntax crate
impl RegexBuilder {
    /// Enable or disable the Unicode flag (`u`) by default.
    ///
    /// By default this is **enabled**. It may alternatively be selectively
    /// disabled in the regular expression itself via the `u` flag.
    ///
    /// Note that unless `utf8` is disabled (it's enabled by default), a
    /// regular expression will fail to parse if Unicode mode is disabled and a
    /// sub-expression could possibly match invalid UTF-8.
    pub fn unicode(&mut self, unicode: bool) -> &mut Self {
        self.parser_builder.unicode(unicode);
        self
    }

    /// When disabled, translation will permit the construction of a regular
    /// expression that may match invalid UTF-8.
    ///
    /// When enabled (the default), the translator is guaranteed to produce an
    /// expression that, for non-empty matches, will only ever produce spans
    /// that are entirely valid UTF-8 (otherwise, the translator will return an
    /// error).
    pub fn utf8(&mut self, utf8: bool) -> &mut Self {
        self.parser_builder.utf8(utf8);
        self
    }

    /// Enable verbose mode in the regular expression.
    ///
    /// When enabled, verbose mode permits insignificant whitespace in many
    /// places in the regular expression, as well as comments. Comments are
    /// started using `#` and continue until the end of the line.
    ///
    /// By default, this is disabled. It may be selectively enabled in the
    /// regular expression by using the `x` flag regardless of this setting.
    pub fn ignore_whitespace(&mut self, ignore_whitespace: bool) -> &mut Self {
        self.parser_builder.ignore_whitespace(ignore_whitespace);
        self
    }

    /// Enable or disable the case insensitive flag by default.
    ///
    /// By default this is disabled. It may alternatively be selectively
    /// enabled in the regular expression itself via the `i` flag.
    pub fn case_insensitive(&mut self, case_insensitive: bool) -> &mut Self {
        self.parser_builder.case_insensitive(case_insensitive);
        self
    }

    /// Enable or disable the "dot matches any character" flag by default.
    ///
    /// By default this is disabled. It may alternatively be selectively
    /// enabled in the regular expression itself via the `s` flag.
    pub fn dot_matches_new_line(&mut self, dot_matches_new_line: bool) -> &mut Self {
        self.parser_builder
            .dot_matches_new_line(dot_matches_new_line);
        self
    }
}
