use crate::{
    diagnostics::Diagnoster,
    err::{SynErr, Trace},
    tok::{Tok, TokKind, Lit, Source}, ast::{self, Expr},
};

pub struct Syn<'a, D>
where
    D: Diagnoster,
{
    pub toks: Vec<Tok<'a>>,
    pub asir: Vec<ast::AsIr>,
    pub pos: usize,
    pub diag: D,
}

impl<'a, D> Syn<'a, D>
where
    D: Diagnoster,
{
    pub fn new(toks: Vec<Tok<'a>>, diag: D) -> Syn<'a, D> {
        Syn::<'a> {
            toks,
            asir: Vec::new(),
            pos: 0,
            diag,
        }
    }

    pub fn parse_all(&mut self) -> Result<(), Trace<'a, SynErr>> {
        while let Some(tok) = self.peek() {
            match tok.kind {
                TokKind::Add | TokKind::Sub | TokKind::LitInt => {
                    let ir = self.parse()?;
                    self.asir.push(ir)
                }
                TokKind::Eof => break,
                _ => return Err(Trace {
                    src: tok.src,
                    err: SynErr::InvalidToken(tok.kind.to_string()),
                }),
            }
        }
        Ok(())
    }

    pub fn parse(&mut self) -> Result<ast::AsIr, Trace<'a, SynErr>> {
        if let Some(tok) = self.peek() {
            tilog::debug!("Peek: {:?}", tok);
            match tok.kind {
                TokKind::Add | TokKind::Sub => {
                    match self.prev_ir() { 
                        Some(ast::AsIr::Expr(ex)) => {
                            tilog::debug!("Previous expr: {:?}", ex);
                            self.parse_binop()
                        }
                        e => {
                            tilog::debug!("Previous expr: {:?}", e);
                            self.parse_num_expr()
                        }
                    }
                }
                TokKind::LitInt => self.parse_num_expr(),
                TokKind::Eof => Err(Trace {
                    src: tok.src,
                    err: SynErr::Expected("Token".to_string(), "EOF".to_string()),
                }),
                _ => Err(Trace {
                    src: tok.src,
                    err: SynErr::InvalidToken(tok.kind.to_string()),
                })
            }
        } else {
            return Err(Trace {
                src: Source::eof(),
                err: SynErr::Expected("EOF".to_string(), "EOF".to_string()),
            });
        }
    }

    pub fn parse_binop(&mut self) -> Result<ast::AsIr, Trace<'a, SynErr>> {
        let ast::AsIr::Expr(lhs) = self.pop_prev_ir().unwrap();
        let op = self.assert_union(&[TokKind::Add, TokKind::Sub])?;
        let binop = match op.kind {
            TokKind::Add => ast::BinOp::Add,
            TokKind::Sub => ast::BinOp::Sub,
            _ => unreachable!(),
        };
        let expr = self.parse_num_expr()?;
        let rhs = match expr {
            ast::AsIr::Expr(ast::Expr::Lit(lit)) => lit,
            _ => unreachable!(),
        };
        

        let binexpr = ast::BinExpr {
            lhs: Box::new(lhs),
            rhs: Box::new(Expr::Lit(rhs)),
            op: binop,
        };

        Ok(ast::AsIr::Expr(ast::Expr::Bin(binexpr)))
    }

    #[rustfmt::skip]
    pub fn parse_num_expr(&mut self) -> Result<ast::AsIr, Trace<'a, SynErr>> {
        let mut expr = self.assert_union(&[
            TokKind::LitInt, 
            TokKind::Add, 
            TokKind::Sub
        ])?;

        let is_neg = TokKind::Sub == expr.kind;
        if let TokKind::Add | TokKind::Sub = expr.kind {
            expr = self.assert(TokKind::LitInt)?;
        }

        let lhs = if let Lit::Uint(val) | Lit::Bin(val) | Lit::Oct(val) | Lit::Hex(val) = expr.val {
            val
        } else {
            tilog::info!("Expected Literal Integer");
            return Err(Trace {
                src: expr.src,
                err: SynErr::InvalidToken(expr.kind.to_string()),
            });
        };

        let src = expr.src;
        let kind = expr.kind;
        let ty = self.take_if_union(&[
            TokKind::U8,
            TokKind::U16,
            TokKind::U32,
            TokKind::U64,
            TokKind::I8,
            TokKind::I16,
            TokKind::I32,
            TokKind::I64,
        ]);

        if let Some(ty) = ty {
            let ilhs = if is_neg { -(lhs as i64) } else { lhs as i64 };
            let ty = match ty.kind {
                TokKind::U8 => ast::AstLit::U8(lhs as u8),
                TokKind::U16 => ast::AstLit::U16(lhs as u16),
                TokKind::U32 => ast::AstLit::U32(lhs as u32),
                TokKind::U64 => ast::AstLit::U64(lhs),
                TokKind::I8 => ast::AstLit::I8(ilhs as i8),
                TokKind::I16 => ast::AstLit::I16(ilhs as i16),
                TokKind::I32 => ast::AstLit::I32(ilhs as i32),
                TokKind::I64 => ast::AstLit::I64(ilhs),
                _ => unreachable!(),
            };
            Ok(ast::AsIr::Expr(ast::Expr::Lit(ty)))
        } else {
            if is_neg {
                return Err(Trace {
                    src,
                    err: SynErr::UnsignedCannotBeNegative(kind.to_string()),
                });
            }
            Ok(ast::AsIr::Expr(ast::Expr::Lit(ast::AstLit::U64(lhs))))
        }
    }

    fn prev_ir(&self) -> Option<&ast::AsIr> {
        self.asir.last()
    }

    fn pop_prev_ir(&mut self) -> Option<ast::AsIr> {
        self.asir.pop()
    }

    fn peek(&self) -> Option<&Tok<'a>> {
        self.toks.get(self.pos)
    }


    fn take(&mut self) -> Option<Tok<'a>> {
        if self.pos < self.toks.len() {
            let tok = self.toks[self.pos];
            self.pos += 1;
            Some(tok)
        } else {
            None
        }
    }

    fn take_or_eof(&mut self) -> Result<&Tok<'a>, Trace<'a, SynErr>> {
        let tok = self.toks.get(self.pos);
        if let Some(tok) = tok {
            self.pos += 1;
            Ok(tok)
        } else {
            Err(Trace {
                src: Source::eof(),
                err: SynErr::Expected("EOF".to_string(), "EOF".to_string()),
            })
        }
    }

    #[allow(dead_code)]
    fn take_if(&mut self, kind: TokKind) -> Option<Tok<'a>> {
        if let Some(tok) = self.peek() {
            if tok.kind == kind {
                return self.take();
            }
        }
        None
    }

    fn take_if_union(&mut self, kinds: &[TokKind]) -> Option<Tok<'a>> {
        if let Some(tok) = self.peek() {
            if kinds.contains(&tok.kind) {
                self.take()
            } else {
                None
            }
        } else {
            None
        }
    }

    fn assert(&mut self, kind: TokKind) -> Result<&Tok<'a>, Trace<'a, SynErr>> {
        let next = self.take_or_eof()?;
        if next.kind == kind {
            Ok(next)
        } else {
            Err(Trace {
                src: next.src,
                err: SynErr::Expected(kind.to_string(), next.kind.to_string()),
            })
        }
    }

    fn assert_union(&mut self, kinds: &[TokKind]) -> Result<&Tok<'a>, Trace<'a, SynErr>> {
        let next = self.take_or_eof()?;
        if kinds.contains(&next.kind) {
            Ok(next)
        } else {
            Err(Trace {
                src: next.src,
                err: SynErr::Expected(
                    kinds
                        .iter()
                        .map(|kind| kind.to_string())
                        .collect::<Vec<String>>()
                        .join(" or "),
                    next.kind.to_string(),
                ),
            })
        }
    }
}

#[cfg(test)]
pub mod tests {

    use crate::diagnostics::StdoutDiagnoster;
    use crate::lex;
    use crate::ast::{AsIr, Expr, AstLit};
    use super::*;

    #[test]
    fn test_invalid_negation_of_unsigned() {
        let diags = StdoutDiagnoster {};
        let src = r#"
            -123
            -123u8
            -123u16
            -123u32
            -123u64
        "#;
        let lex = lex::Lex::new("", src.as_bytes(), diags);
        let toks = lex.collect();
        let diag = StdoutDiagnoster {};
        let mut syn = Syn::new(toks, diag);
        let ast = syn.parse_all();
        println!("{:#?}", ast);
        assert!(ast.is_err());
    }

    #[test]
    fn test_parse_nums() {
        let diags = StdoutDiagnoster {};
        let src = r#"
            123 

            0x123
            0b1010
            0o1234
            0x1234

            123u8
            123u16
            123u32
            123u64
            123i8
            123i16
            123i32
            123i64 

        "#;
            // -123i8
            // -123i16
            // -123i32
            // -123i64

        let lex = lex::Lex::new("", src.as_bytes(), diags);
        let toks = lex.collect();
        let diag = StdoutDiagnoster {};
        let mut syn = Syn::new(toks, diag);
        let ast = syn.parse_all();
        println!("{:#?}", ast);
        assert!(ast.is_ok());
        let ast = syn.asir;
        let expected = vec![
            AsIr::Expr(Expr::Lit(AstLit::U64(123))),
            // AsIr::Expr(Expr::Lit(AstLit::I64(-123))),
            AsIr::Expr(Expr::Lit(AstLit::U64(0x123))),
            AsIr::Expr(Expr::Lit(AstLit::U64(0b1010))),
            AsIr::Expr(Expr::Lit(AstLit::U64(0o1234))),
            AsIr::Expr(Expr::Lit(AstLit::U64(0x1234))),
            AsIr::Expr(Expr::Lit(AstLit::U8(123))),
            AsIr::Expr(Expr::Lit(AstLit::U16(123))),
            AsIr::Expr(Expr::Lit(AstLit::U32(123))),
            AsIr::Expr(Expr::Lit(AstLit::U64(123))),
            AsIr::Expr(Expr::Lit(AstLit::I8(123))),
            AsIr::Expr(Expr::Lit(AstLit::I16(123))),
            AsIr::Expr(Expr::Lit(AstLit::I32(123))),
            AsIr::Expr(Expr::Lit(AstLit::I64(123))),
            // AsIr::Expr(Expr::Lit(AstLit::I8(-123))),
            // AsIr::Expr(Expr::Lit(AstLit::I16(-123))),
            // AsIr::Expr(Expr::Lit(AstLit::I32(-123))),
            // AsIr::Expr(Expr::Lit(AstLit::I64(-123))),
        ];
        assert_eq!(ast, expected);
    }
}
