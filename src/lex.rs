use core::f64;

use crate::{
    diagnostics::{Diagnoster, Diagnostic, DiagnosticKind},
    err::{LexErr, Trace},
    tok::{Source, TokBuf, TokIx, TokKind, Val},
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
    /// The token buffer will be built from the lexer.
    /// It will contain the values for all literals
    /// (integers, floats, strings) as well as the
    /// identifiers.
    ///
    /// This token buffer can then be passed to the different
    /// stages of the compiler (parsing, semantix analysis, codegen).
    ///
    /// It has an api for the caller to get information for any token
    /// via the `TokIx`, which is an index into its internal buffer
    /// of token infos, which then has a pointer to the corresponding
    /// array (integer, float, string, identifier) array of the token.
    /// If the token does not need to have an (at compile time) unknown
    /// value, like symbols and keywords, since we store its type in
    /// the info, we already know its value as well.
    pub buf: TokBuf<'a>,
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
            buf: TokBuf::new(if file.is_empty() { None } else { Some(file) }, src),
        }
    }

    pub fn lex(mut self) -> TokBuf<'a> {
        self.buf.push(TokKind::Sof, Source::sof(self.file), None);

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

            let kind = self.buf.kind_of(tok);
            if kind == TokKind::Eof {
                break;
            } else if kind == TokKind::Invalid {
                tilog::info!("Invalid token: {:?}", self.buf.str_of(tok))
                // self.diag.report(Diagnostic {
                //     kind: DiagnosticKind::Error,
                //     msg: LexErr::InvalidToken(self.str_of(&tok.src).to_owned()).to_string(),
                //     src: tok.src,
                // });
            }
        }

        self.buf
    }

    pub fn lx_tok(&mut self) -> Result<TokIx, Trace<'a, LexErr>> {
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

            ch => {
                let src = self.src();
                Ok(self.buf.push(TokKind::from(ch), src, Some(Val::Char(ch))))
            }
        }
    }

    fn lx_prefixed_int(&mut self, prefix: u8) -> Result<TokIx, Trace<'a, LexErr>> {
        let radix = match prefix {
            b'b' | b'B' => 2,
            b'o' | b'O' => 8,
            b'x' | b'X' => 16,
            _ => unreachable!(),
        };

        self.consume_while(|c| c.is_ascii_alphanumeric());
        let src = self.src();
        let val = &self.str_of(&src)[2..];

        let uval = u64::from_str_radix(val, radix).map_err(|err| Trace {
            src,
            err: LexErr::IntegerParseErr(err),
        })?;

        Ok(self.buf.push(TokKind::IntLit, src, Some(Val::Uint(uval))))
    }

    fn lx_int(&mut self) -> Result<TokIx, Trace<'a, LexErr>> {
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
            tilog::info!("real: {}", self.str_of(&src));
            match self.str_of(&src).parse::<f64>() {
                Ok(val) => Ok(self.buf.push(TokKind::RealLit, src, Some(Val::Real(val)))),
                Err(err) => Err(Trace {
                    src,
                    err: LexErr::FloatParseErr(err),
                }),
            }
        } else {
            match self.str_of(&src).parse::<u64>() {
                Ok(val) => Ok(self.buf.push(TokKind::IntLit, src, Some(Val::Uint(val)))),
                Err(err) => Err(Trace {
                    src,
                    err: LexErr::IntegerParseErr(err),
                }),
            }
        }
    }

    fn lx_ident(&mut self) -> Result<TokIx, Trace<'a, LexErr>> {
        self.consume_while(|c| c.is_ascii_alphanumeric() || c == b'_');
        let src = self.src();
        let st = self.str_of(&src);
        Ok(self.buf.push(TokKind::from(st), src, Some(Val::Ident(st))))
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
        let lx = Lex::new("", src.as_bytes(), diags);
        let buf = lx.lex();
        assert!(buf.infos.len() == 10);
        assert!(buf.infos[0].kind == TokKind::Sof);
        for i in 1..buf.infos.len() - 1 {
            assert_eq!(buf.infos[i].kind, TokKind::Ident);
        }
        assert!(buf.str_of(1) == "foo");
        assert!(buf.str_of(2) == "_foo");
        assert!(buf.str_of(3) == "foo_bar");
        assert!(buf.str_of(4) == "_");
        assert!(buf.str_of(5) == "__");
        assert!(buf.str_of(6) == "foo123");
        assert!(buf.str_of(7) == "_123");
        assert!(buf.str_of(8) == "_a1c_213klj");
        assert!(buf.infos[9].kind == TokKind::Eof)
    }

    #[test]
    fn test_lx_symbols() {
        // Exhaustive, should catch if I add a new symbol
        let src = r#"+ - * / ; ,"#;
        let diags = StdoutDiagnoster {};
        let lx = Lex::new("", src.as_bytes(), diags);
        let buf = lx.lex();
        let toks = buf.infos;
        assert!(toks.len() == 8);
        assert_eq!(toks[1].kind, TokKind::Add);
        assert_eq!(toks[2].kind, TokKind::Sub);
        assert_eq!(toks[3].kind, TokKind::Mul);
        assert_eq!(toks[4].kind, TokKind::Div);
        assert_eq!(toks[5].kind, TokKind::Semi);
        assert_eq!(toks[6].kind, TokKind::Comma);
        assert_eq!(toks[7].kind, TokKind::Eof);
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
        let lx = Lex::new("", src.as_bytes(), diags);
        let buf = std::rc::Rc::new(lx.lex());
        let toks = &buf.toks;
        // println!("{:#?}", buf.infos);
        assert!(toks.len() == 28);

        let expected = vec![
            (TokKind::Sof, Val::String("Placeholder".into())),
            (TokKind::IntLit, Val::Uint(123)),
            (TokKind::IntLit, Val::Uint(007)),
            (TokKind::IntLit, Val::Uint(0b1010)),
            (TokKind::IntLit, Val::Uint(0b1111)),
            (TokKind::IntLit, Val::Uint(0o123)),
            (TokKind::IntLit, Val::Uint(0o007)),
            (TokKind::IntLit, Val::Uint(0x123)),
            (TokKind::IntLit, Val::Uint(0x007)),
            (TokKind::RealLit, Val::Real(123.456)),
            (TokKind::RealLit, Val::Real(007.123)),
            (TokKind::RealLit, Val::Real(0.123)),
            (TokKind::RealLit, Val::Real(0.007)),
            (TokKind::RealLit, Val::Real(123.0)),
            (TokKind::RealLit, Val::Real(007.0)),
            (TokKind::RealLit, Val::Real(123e4)),
            (TokKind::RealLit, Val::Real(007e4)),
            (TokKind::RealLit, Val::Real(123e4)),
            (TokKind::RealLit, Val::Real(007e4)),
            (TokKind::RealLit, Val::Real(123e-4)),
            (TokKind::RealLit, Val::Real(007e-4)),
            (TokKind::RealLit, Val::Real(1.23e4)),
            (TokKind::RealLit, Val::Real(0.07e4)),
            (TokKind::RealLit, Val::Real(1.23e4)),
            (TokKind::RealLit, Val::Real(0.07e4)),
        ];

        for tok in 1..expected.len() {
            assert_eq!(buf.kind_of(tok), expected[tok].0);
            assert_eq!(buf.val_of(tok).unwrap(), expected[tok].1);
        }

        assert_eq!(buf.kind_of(27), TokKind::Eof);
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
