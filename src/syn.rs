use crate::{
    diagnostics::Diagnoster,
    err::{SynErr, Trace},
    tok::{TokKind, Val, Source, TokBuf, TokIx}, ast::{self, Expr},
};

pub struct Syn<'a, D>
where
    D: Diagnoster,
{
    pub toks: TokBuf<'a>,
    pub asir: Vec<ast::AsIr>,
    pub pos: usize,
    pub diag: D,
}

impl<'a, D> Syn<'a, D>
where
    D: Diagnoster,
{
    pub fn new(toks: TokBuf<'a>, diag: D) -> Syn<'a, D> {
        Syn::<'a> {
            toks,
            asir: Vec::new(),
            pos: 0,
            diag,
        }
    }
    
    pub fn parse_all(&mut self) -> Result<(), Trace<'a, SynErr>> {
        while let Some(tok) = self.peek() {
            let kind = self.toks.kind_of(tok);
            match kind {
                // TokKind::Let => self.asir.push(self.parse_let()?),
                TokKind::Add | TokKind::Sub | TokKind::IntLit => {
                    let int = self.parse_int()?;
                    self.asir.push(int)
                }
                TokKind::Eof => break,
                _ => return Err(Trace {
                    src: self.toks.src_of(tok),
                    err: SynErr::InvalidToken(kind.to_string()),
                }),
            }
        }
        Ok(())
    }

    pub fn parse_let(&mut self) -> Result<ast::AsIr, Trace<'a, SynErr>> {
        self.assert(TokKind::Let)?;
        let name = self.assert(TokKind::Ident)?;
        self.assert(TokKind::Colon)?;
        let ty = self.consume_if(TokKind::Ident);
        self.assert(TokKind::Eq);
        let expr = self.parse_expr()?;
        self.assert(TokKind::Semi)?;
        Ok(ast::AsIr::Let(ast::Let {
            name: self.toks.str_of(name).to_string(),
            ty: ty.map(|ty| self.toks.str_of(ty).to_string()),
            expr: Box::new(expr),
        }))
    }

    pub fn parse_expr(&mut self) -> Result<ast::Expr, Trace<'a, SynErr>> {
        match self.toks.kind_of(self.peek().ok_or(Trace {
            src: Source::eof(),
            err: SynErr::Expected("Token".to_string(), "EOF".to_string()),
        })?) {
            TokKind::IntLit => self.parse_num_expr().map(|ir| match ir {
                ast::AsIr::Expr(expr) => expr,
                _ => unreachable!(),
            }),
            _ => unreachable!(),
        }
    }

    pub fn parse_int(&mut self) -> Result<ast::AsIr, Trace<'a, SynErr>> {
        if let Some(tok) = self.peek() {
            let tinfo = self.toks.info_of(tok);
            tilog::debug!("Peek: {:?}", tok);
            match tinfo.kind {
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
                TokKind::IntLit => self.parse_num_expr(),
                TokKind::Eof => Err(Trace {
                    src: tinfo.src,
                    err: SynErr::Expected("Token".to_string(), "EOF".to_string()),
                }),
                _ => Err(Trace {
                    src: tinfo.src,
                    err: SynErr::InvalidToken(tinfo.kind.to_string()),
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
        let lhs = match self.pop_prev_ir().unwrap() {
            ast::AsIr::Expr(expr) => expr,
            _ => unreachable!(),
        };
        let op = self.assert_union(&[TokKind::Add, TokKind::Sub])?;
        let binop = match self.toks.kind_of(op) {
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
            TokKind::IntLit, 
            TokKind::Add, 
            TokKind::Sub
        ])?;

        let tinfo = self.toks.info_of(expr);
        let is_neg = TokKind::Sub == tinfo.kind;
        if let TokKind::Add | TokKind::Sub = tinfo.kind {
            expr = self.assert(TokKind::IntLit)?;
        }

        let lhs = if let Ok(Val::Uint(val)) = self.toks.val_of(expr) {
            val
        } else {
            tilog::info!("Expected Literal Integer");
            return Err(Trace {
                src: tinfo.src,
                err: SynErr::InvalidToken(tinfo.kind.to_string()),
            });
        };

        let src = tinfo.src;
        let kind = tinfo.kind;

        match match self.peek() {
            Some(tok) if self.toks.kind_of(tok) == TokKind::Ident => {
                match self.toks.val_of(tok) {
                    Ok(Val::Ident(val)) => {
                        let ilhs = if is_neg { -(lhs as i64) } else { lhs as i64 };
                        match val {
                            "u8" => Some(ast::AstLit::U8(lhs as u8)),
                            "u16" => Some(ast::AstLit::U16(lhs as u16)),
                            "u32" => Some(ast::AstLit::U32(lhs as u32)),
                            "u64" => Some(ast::AstLit::U64(lhs)),
                            "i8"=> Some(ast::AstLit::I8(ilhs as i8)),
                            "i16" => Some(ast::AstLit::I16(ilhs as i16)),
                            "i32" => Some(ast::AstLit::I32(ilhs as i32)),
                            "i64" => Some(ast::AstLit::I64(ilhs)),
                            _ => None
                        }
                    }
                    _ => None
                }
            },
            _ => None
        } {
            Some(lit) => Ok(ast::AsIr::Expr(ast::Expr::Lit(lit))),
            None => {
                if is_neg {
                    return Err(Trace {
                        src,
                        err: SynErr::UnsignedCannotBeNegative(kind.to_string()),
                    });
                }
                Ok(ast::AsIr::Expr(ast::Expr::Lit(ast::AstLit::U64(lhs))))
            }
        }
    }

    fn prev_ir(&self) -> Option<&ast::AsIr> {
        self.asir.last()
    }

    fn pop_prev_ir(&mut self) -> Option<ast::AsIr> {
        self.asir.pop()
    }

    fn peek(&self) -> Option<TokIx> {
        self.toks.get(self.pos)
    }


    fn consume(&mut self) -> Option<TokIx> {
        if self.pos < self.toks.len() {
            let tok = self.toks.get(self.pos).unwrap();
            self.pos += 1;
            Some(tok)
        } else {
            None
        }
    }

    fn consume_or_eof(&mut self) -> Result<TokIx, Trace<'a, SynErr>> {
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
    fn consume_if(&mut self, kind: TokKind) -> Option<TokIx> {
        if let Some(tok) = self.peek() {
            if self.toks.kind_of(tok) == kind {
                return self.consume();
            }
        }
        None
    }

    fn consume_if_union(&mut self, kinds: &[TokKind]) -> Option<TokIx> {
        if let Some(tok) = self.peek() {
            if kinds.contains(&self.toks.kind_of(tok)) {
                self.consume()
            } else {
                None
            }
        } else {
            None
        }
    }

    fn assert(&mut self, kind: TokKind) -> Result<TokIx, Trace<'a, SynErr>> {
        let next = self.consume_or_eof()?;
        let nkind = self.toks.kind_of(next);
        if  nkind == kind {
            Ok(next)
        } else {
            Err(Trace {
                src: self.toks.src_of(next),
                err: SynErr::Expected(kind.to_string(), nkind.to_string()),
            })
        }
    }

    fn assert_union(&mut self, kinds: &[TokKind]) -> Result<TokIx, Trace<'a, SynErr>> {
        let next = self.consume_or_eof()?;
        let kind = self.toks.kind_of(next);
        if kinds.contains(&kind) {
            Ok(next)
        } else {
            Err(Trace {
                src: self.toks.src_of(next),
                err: SynErr::Expected(
                    kinds.iter()
                        .map(|kind| kind.to_string())
                        .collect::<Vec<String>>()
                        .join(" or "),
                    kind.to_string(),
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
        let buf = lex.lex();
        let diag = StdoutDiagnoster {};
        let mut syn = Syn::new(buf, diag);
        let ast = syn.parse_all();
        println!("{:#?}", ast);
        assert!(ast.is_err());
    }

    // #[test]
    // fn test_parse_nums() {
    //     let diags = StdoutDiagnoster {};
    //     let src = r#"
    //         123 

    //         0x123
    //         0b1010
    //         0o1234
    //         0x1234


    //     "#;
    //         // 123u8
    //         // 123u16
    //         // 123u32
    //         // 123u64
    //         // 123i8
    //         // 123i16
    //         // 123i32
    //         // 123i64 
    //         // -123i8
    //         // -123i16
    //         // -123i32
    //         // -123i64

    //     let lex = lex::Lex::new("", src.as_bytes(), diags);
    //     let toks = lex.lex();
    //     let diag = StdoutDiagnoster {};
    //     let mut syn = Syn::new(toks, diag);
    //     let ast = syn.parse_all();
    //     println!("{:#?}", ast);
    //     assert!(ast.is_ok());
    //     let ast = syn.asir;
    //     let expected = vec![
    //         AsIr::Expr(Expr::Lit(AstLit::U64(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I64(-123))),
    //         AsIr::Expr(Expr::Lit(AstLit::U64(0x123))),
    //         AsIr::Expr(Expr::Lit(AstLit::U64(0b1010))),
    //         AsIr::Expr(Expr::Lit(AstLit::U64(0o1234))),
    //         AsIr::Expr(Expr::Lit(AstLit::U64(0x1234))),
    //         // AsIr::Expr(Expr::Lit(AstLit::U8(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::U16(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::U32(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::U64(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I8(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I16(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I32(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I64(123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I8(-123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I16(-123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I32(-123))),
    //         // AsIr::Expr(Expr::Lit(AstLit::I64(-123))),
    //     ];
    //     assert_eq!(ast, expected);
    // }
}
