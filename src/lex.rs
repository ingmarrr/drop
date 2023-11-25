use core::f64;

use crate::{
    diagnostics::{Diagnoster, Diagnostic, DiagnosticKind, StdoutDiagnoster},
    err::{LexErr, Trace},
    tok::{Lit, Source, Tok, TokKind},
};

pub struct Lex<'a, D>
where
    D: Diagnoster,
{
    /// Source input
    pub src: &'a [u8],
    /// Current position in the input
    pub pos: usize,
    /// Current line in the input
    pub line: usize,
    /// Current column in the input
    pub col: usize,
    /// Start of the current token being processed
    /// When eventually returning the token, this will
    /// be set to `pos`.
    pub start: usize,
    /// The file name of the source input
    pub file: &'a str,
    /// The diagnostics are a global error/warning/note
    /// that is passed in to the lexer and parser as a mutable reference.
    /// The lexer and parser will add errors/warnings/notes
    /// to the diagnostics.
    pub diag: D,
}

impl<'a, D> Lex<'a, D>
where
    D: Diagnoster,
{
    pub fn new(file: &'a str, src: &'a [u8], diag: D) -> Self {
        Self {
            src,
            pos: 0,
            line: 1,
            col: 1,
            start: 0,
            file,
            diag,
        }
    }

    pub fn lex(&mut self) -> Vec<Tok<'a>> {
        if self.src.is_empty() {
            return Vec::new();
        }
        let mut toks = Vec::new();
        loop {
            let tok = match self.lx_tok() {
                Ok(tok) => tok,
                Err(trace) => {
                    self.diag.report(Diagnostic {
                        kind: DiagnosticKind::Error,
                        msg: trace.err.to_string(),
                        src: trace.src,
                    });
                    continue;
                }
            };

            if tok.kind == TokKind::Eof {
                break;
            } else if tok.kind == TokKind::Invalid {
                tilog::error!("Invalid token: {:?}", tok)
                // self.diag.report(Diagnostic {
                //     kind: DiagnosticKind::Error,
                //     msg: LexErr::InvalidToken(self.str_of(&tok.src).to_owned()).to_string(),
                //     src: tok.src,
                // });
            }
            toks.push(tok);
        }

        toks
    }

    pub fn lx_tok(&mut self) -> Result<Tok<'a>, Trace<'a, LexErr>> {
        self.consume_ws();

        let tok = self.consume().unwrap_or(b'\0');
        match tok {
            b'0' => match self.consume_if_union(b"bBoOxX") {
                Some(prefix) if Self::is_num_prefix(prefix) => {
                    let res = self.lx_prefixed_int(prefix);
                    res
                }
                _ => self.lx_int(),
            },
            b'1'..=b'9' => self.lx_int(),
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.lx_ident(),
            ch => Ok(Tok::<'a> {
                kind: TokKind::from(ch),
                src: self.src(),
                val: Lit::Char(ch),
            }),
        }
    }

    fn lx_prefixed_int(&mut self, prefix: u8) -> Result<Tok<'a>, Trace<'a, LexErr>> {
        let radix = match prefix {
            b'b' | b'B' => 2,
            b'o' | b'O' => 8,
            b'x' | b'X' => 16,
            _ => unreachable!(),
        };

        self.consume_while(|c| c.is_ascii_alphanumeric());
        let src = self.src();
        let val = &self.str_of(&src)[2..];

        let uval = match u64::from_str_radix(val, radix) {
            Ok(val) => val,
            Err(err) => {
                return Err(Trace {
                    src,
                    err: LexErr::IntegerParseErr(err),
                })
            }
        };
        Ok(Tok::<'a> {
            kind: TokKind::LitInt,
            val: match prefix {
                b'b' | b'B' => Lit::Bin(uval),
                b'o' | b'O' => Lit::Oct(uval),
                b'x' | b'X' => Lit::Hex(uval),
                _ => unreachable!(),
            },
            src,
        })
    }

    fn lx_int(&mut self) -> Result<Tok<'a>, Trace<'a, LexErr>> {
        self.consume_while(|c| c.is_ascii_digit());
        let mut is_real = if self.consume_if(b'.').is_some() {
            self.consume_while(|c| c.is_ascii_digit());
            true
        } else {
            false
        };

        if self.consume_if_union(b"eE").is_some() {
            self.consume_if_union(b"+-");
            self.consume_while(|c| c.is_ascii_digit());
            is_real = true
        };

        let src = self.src();
        if is_real {
            match self.str_of(&src).parse::<f64>() {
                Ok(val) => Ok(Tok::<'a> {
                    kind: TokKind::LitReal,
                    src,
                    val: Lit::Real(val),
                }),
                Err(err) => Err(Trace {
                    src,
                    err: LexErr::FloatParseErr(err),
                }),
            }
        } else {
            match self.str_of(&src).parse::<u64>() {
                Ok(val) => Ok(Tok::<'a> {
                    kind: TokKind::LitInt,
                    src,
                    val: Lit::Uint(val),
                }),
                Err(err) => Err(Trace {
                    src,
                    err: LexErr::IntegerParseErr(err),
                }),
            }
        }
    }

    fn lx_ident(&mut self) -> Result<Tok<'a>, Trace<'a, LexErr>> {
        self.consume_while(|c| c.is_ascii_alphanumeric() || c == b'_');
        let src = self.src();
        let st = self.str_of(&src);
        let val = Lit::String(st);

        Ok(Tok::<'a> {
            kind: TokKind::from(st),
            src,
            val,
        })
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    #[inline]
    fn consume(&mut self) -> Option<u8> {
        let c = self.src.get(self.pos).copied()?;
        if c == b'\n' {
            self.line += 1;
            self.col = 0;
        }
        self.pos += 1;
        self.col += 1;
        Some(c)
    }

    #[inline]
    #[must_use]
    #[allow(dead_code)]
    fn consume_if(&mut self, next: u8) -> Option<u8> {
        if let Some(c) = self.peek() {
            if c == next {
                return self.consume();
            }
        }
        None
    }

    #[inline]
    #[allow(dead_code)]
    fn consume_if_union(&mut self, ch: &[u8]) -> Option<u8> {
        if let Some(c) = self.peek() {
            if ch.contains(&c) {
                return self.consume();
            }
        }
        None
    }

    #[inline]
    fn consume_while(&mut self, func: impl Fn(u8) -> bool) -> &'a [u8] {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if func(c) {
                self.consume();
            } else {
                break;
            }
        }
        &self.src[start..self.pos]
    }

    fn consume_ws(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() {
                self.consume();
            } else {
                break;
            }
        }
        self.start = self.pos;
    }

    #[inline]
    #[must_use]
    pub fn src(&mut self) -> Source<'a> {
        if self.start == self.pos {
            return Source::<'a> {
                file: self.file,
                pos: self.pos,
                col: self.col,
                line: self.line,
                len: 0,
            };
        }
        let src = self.src_of(&self.src[self.start..self.pos]);
        self.start = self.pos;
        src
    }

    pub fn src_eof(&self) -> Source<'a> {
        Source::<'a> {
            file: self.file,
            pos: self.pos,
            col: self.col,
            line: self.line,
            len: 0,
        }
    }

    fn src_of(&self, buf: &'a [u8]) -> Source<'a> {
        Source::<'a> {
            file: self.file,
            pos: self.pos - buf.len(),
            col: self.col - (buf.len() % self.col),
            line: self.line,
            len: buf.len(),
        }
    }

    fn bytes_of(&self, src: &Source<'a>) -> &'a [u8] {
        &self.src[src.pos..src.pos + src.len]
    }

    fn str_of(&self, src: &Source<'a>) -> &'a str {
        std::str::from_utf8(self.bytes_of(src)).unwrap()
    }

    fn is_num_prefix(ch: u8) -> bool {
        matches!(ch, b'b' | b'B' | b'o' | b'O' | b'x' | b'X')
    }
}

impl<'a> Iterator for Lex<'a, StdoutDiagnoster> {
    type Item = Tok<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let tok = self.lx_tok().ok()?;
        if tok.kind == TokKind::Eof {
            None
        } else {
            Some(tok)
        }
    }
}

#[cfg(test)]
mod lex_public_api_tests {
    use crate::diagnostics::StdoutDiagnoster;

    use super::*;

    #[test]
    fn test_lx_new() {
        let src = b"foo";
        let diags = StdoutDiagnoster {};
        let lx = Lex::new("", src, diags);

        assert_eq!(lx.src, src);
        assert_eq!(lx.pos, 0);
        assert_eq!(lx.line, 1);
        assert_eq!(lx.col, 1);
        assert_eq!(lx.start, 0);
    }

    #[test]
    fn test_ident() {
        let src = r#"foo _foo foo_bar _ __ foo123 _123 _a1c_213klj"#;
        let diags = StdoutDiagnoster {};
        let mut lx = Lex::new("", src.as_bytes(), diags);
        let toks = lx.lex();
        for tok in toks {
            assert_eq!(tok.kind, TokKind::Ident);
        }
    }

    #[test]
    fn test_lx_symbols() {
        // Exhaustive, should catch if I add a new symbol
        let src = r#"+ - * / ; ,"#;
        let diags = StdoutDiagnoster {};
        let mut lx = Lex::new("", src.as_bytes(), diags);
        let toks = lx.lex();
        assert!(toks.len() == 6);
        assert_eq!(toks[0].kind, TokKind::Add);
        assert_eq!(toks[1].kind, TokKind::Sub);
        assert_eq!(toks[2].kind, TokKind::Mul);
        assert_eq!(toks[3].kind, TokKind::Div);
        assert_eq!(toks[4].kind, TokKind::Semi);
        assert_eq!(toks[5].kind, TokKind::Comma);
    }

    #[test]
    fn test_lx_num() {
        let src = r#"
            123 007

            0b1010 0b1111
            0o123 0o007
            0x123 0x007
            
            123.456 007.123
            0.123 0.007
            123. 007.

            123e4 007e4
            123e+4 007e+4
            123e-4 007e-4
            1.23e4 0.07e4
            1.23e+4 0.07e+4
            1.23e-4 0.07e-4
        "#;
        let diags = StdoutDiagnoster {};
        let mut lx = Lex::new("", src.as_bytes(), diags);
        let toks = lx.lex();
        for tok in toks.iter() {
            tilog::info!("tok: {:?}", tok.val);
        }
        assert!(toks.len() == 26);

        let expected = vec![
            (TokKind::LitInt, Lit::Uint(123)),
            (TokKind::LitInt, Lit::Uint(007)),
            (TokKind::LitInt, Lit::Bin(0b1010)),
            (TokKind::LitInt, Lit::Bin(0b1111)),
            (TokKind::LitInt, Lit::Oct(0o123)),
            (TokKind::LitInt, Lit::Oct(0o007)),
            (TokKind::LitInt, Lit::Hex(0x123)),
            (TokKind::LitInt, Lit::Hex(0x007)),
            (TokKind::LitReal, Lit::Real(123.456)),
            (TokKind::LitReal, Lit::Real(007.123)),
            (TokKind::LitReal, Lit::Real(0.123)),
            (TokKind::LitReal, Lit::Real(0.007)),
            (TokKind::LitReal, Lit::Real(123.0)),
            (TokKind::LitReal, Lit::Real(007.0)),
            (TokKind::LitReal, Lit::Real(123e4)),
            (TokKind::LitReal, Lit::Real(007e4)),
            (TokKind::LitReal, Lit::Real(123e4)),
            (TokKind::LitReal, Lit::Real(007e4)),
            (TokKind::LitReal, Lit::Real(123e-4)),
            (TokKind::LitReal, Lit::Real(007e-4)),
            (TokKind::LitReal, Lit::Real(1.23e4)),
            (TokKind::LitReal, Lit::Real(0.07e4)),
            (TokKind::LitReal, Lit::Real(1.23e4)),
            (TokKind::LitReal, Lit::Real(0.07e4)),
        ];

        for i in 0..expected.len() {
            assert_eq!(toks[i].kind, expected[i].0);
            assert_eq!(toks[i].val, expected[i].1);
        }
    }
}

#[cfg(test)]
mod lex_internal_tests {
    use crate::diagnostics::StdoutDiagnoster;

    fn assert_clp(lx: &super::Lex<StdoutDiagnoster>, col: usize, line: usize, pos: usize) {
        assert_eq!(lx.col, col);
        assert_eq!(lx.line, line);
        assert_eq!(lx.pos, pos);
    }

    #[test]
    fn test_lx_peek() {
        let diags = StdoutDiagnoster {};
        let mut lx = super::Lex::new("", b"foo", diags);

        assert_clp(&lx, 1, 1, 0);
        assert_eq!(lx.peek(), Some(b'f'));
        assert_clp(&lx, 1, 1, 0);
        assert_eq!(lx.consume(), Some(b'f'));

        assert_clp(&lx, 2, 1, 1);
        assert_eq!(lx.peek(), Some(b'o'));
        assert_clp(&lx, 2, 1, 1);
        assert_eq!(lx.consume(), Some(b'o'));

        assert_clp(&lx, 3, 1, 2);
        assert_eq!(lx.peek(), Some(b'o'));
        assert_clp(&lx, 3, 1, 2);
        assert_eq!(lx.consume(), Some(b'o'));

        assert_clp(&lx, 4, 1, 3);
        assert_eq!(lx.peek(), None);
        assert_clp(&lx, 4, 1, 3);
    }

    #[test]
    fn test_lx_take_ws() {
        let diags = StdoutDiagnoster {};
        let mut lx = super::Lex::new("", b"   foo", diags);

        assert_clp(&lx, 1, 1, 0);

        lx.consume_ws();
        assert_clp(&lx, 4, 1, 3);

        assert_eq!(lx.consume(), Some(b'f'));
    }

    #[test]
    fn test_lx_take() {
        let diags = StdoutDiagnoster {};
        let mut lx = super::Lex::new("", b"foo", diags);

        assert_clp(&lx, 1, 1, 0);

        assert_eq!(lx.consume(), Some(b'f'));
        assert_clp(&lx, 2, 1, 1);

        assert_eq!(lx.consume(), Some(b'o'));
        assert_clp(&lx, 3, 1, 2);

        assert_eq!(lx.consume(), Some(b'o'));
        assert_clp(&lx, 4, 1, 3);

        assert_eq!(lx.consume(), None);
    }

    #[test]
    fn test_lx_take_nl() {
        let src = b"a\nb\nc";
        let diags = StdoutDiagnoster {};
        let mut lx = super::Lex::new("", src, diags);

        assert_eq!(lx.consume(), Some(b'a'));
        assert_eq!(lx.consume(), Some(b'\n'));
        assert_clp(&lx, 1, 2, 2);

        assert_eq!(lx.consume(), Some(b'b'));
        assert_clp(&lx, 2, 2, 3);

        assert_eq!(lx.consume(), Some(b'\n'));
        assert_clp(&lx, 1, 3, 4);
    }
}
