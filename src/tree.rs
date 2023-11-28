use std::rc::Rc;

use crate::{
    err::{ParseErr, Trace},
    tok::{Source, TokBuf, TokIx, TokKind},
};

pub struct Cx<'a> {
    pub tree: ParseTree<'a>,
    pub toks: Rc<TokBuf<'a>>,
    pub state: Vec<ParseState>,
    pub pos: usize,
}

impl<'a> Cx<'a> {
    pub fn new(tree: ParseTree<'a>, toks: Rc<TokBuf<'a>>) -> Cx<'a> {
        Cx {
            tree,
            toks,
            state: Vec::new(),
            pos: 0,
        }
    }

    pub fn parse(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        let sof = self.assert(TokKind::Sof)?;
        self.push_leaf(NodeKind::Sof, sof, false);
        self.push_state(ParseState::DeclLoop);

        while !self.state.is_empty() {
            // We just look at the last state on the stack.
            // We dont pop it, that way until we are done with the Declaration loop,
            // which is handled by its own function and will pop the state if it is done,
            // we will keep looping.
            // This is done for every function,
            let state = self.state.last().unwrap();
            use ParseState as S;
            match state {
                S::DeclLoop => self.parse_decl_loop()?,
                S::Let => self.parse_let()?,
                S::LetEnd => self.parse_let_end()?,
                S::BindPattern => self.parse_bind_pattern(),
                S::ValPattern => self.parse_val_pattern()?,
                S::InnerValPattern => self.parse_inner_val_pattern()?,
                S::EndValPattern => self.parse_end_val_pattern()?,
                S::TypePattern => self.parse_type_pattern()?,
                S::Assign => self.parse_assign()?,

                S::Expr => self.parse_expr()?,
                S::TupleExpr => self.parse_tuple_expr()?,
                S::InnerTupleExpr => self.parse_inner_tuple_expr()?,
                S::EndTupleExpr => self.parse_end_tuple_expr()?,
                _ => break,
            }
        }

        self.push_leaf(NodeKind::Eof, self.pos, false);

        Ok(())
    }

    pub fn parse_decl_loop(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        let tok = self.toks.info_of(self.pos);
        match tok.kind {
            TokKind::Eof => self.pop_discard_state(),
            TokKind::Let => self.push_state(ParseState::Let),
            TokKind::Func => self.push_state(ParseState::Func),
            _ => {
                return Err(Trace {
                    src: tok.src.clone(),
                    err: ParseErr::Expected("let or fn".to_string(), tok.kind.to_string()),
                })
            }
        }

        Ok(())
    }

    pub fn parse_expr(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        match self.toks.kind_of(self.pos) {
            // TokKind::Ident => self.parse_var_expr()?,
            TokKind::IntLit | TokKind::RealLit | TokKind::StringLit => self.parse_lit_expr()?,
            TokKind::LPar => self.parse_tuple_expr()?,
            // TokKind::LBrace => self.parse_struct_expr()?,
            _ => {
                return Err(Trace {
                    src: self.toks.info_of(self.pos).src.clone(),
                    err: ParseErr::Expected(
                        "identifier, literal, tuple, or struct".to_string(),
                        self.toks.info_of(self.pos).kind.to_string(),
                    ),
                })
            }
        };
        Ok(())
    }

    pub fn parse_lit_expr(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        let lit = self.assert_union(&[TokKind::IntLit, TokKind::RealLit, TokKind::StringLit])?;
        self.push_leaf(NodeKind::LitExpr, lit, false);
        Ok(())
    }

    pub fn parse_tuple_expr(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        let lpar = self.assert(TokKind::LPar)?;
        self.push_leaf(NodeKind::LPar, lpar, false);
        self.push_state(ParseState::EndTupleExpr);
        self.push_state(ParseState::InnerTupleExpr);
        self.push_state(ParseState::Expr);
        Ok(())
    }

    pub fn parse_inner_tuple_expr(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        if let Some(comma) = self.consume_if(TokKind::Comma) {
            self.push_leaf(NodeKind::Comma, comma, false);
            self.push_state(ParseState::Expr);
        };
        Ok(())
    }

    pub fn parse_end_tuple_expr(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        let tok = self.toks.info_of(self.pos);
        match tok.kind {
            TokKind::RPar => {
                let rpar = self.assert(TokKind::RPar)?;
                self.push_node(NodeKind::TupleExpr, rpar, self.tree.size() - 1, false);
            }
            _ => {
                return Err(Trace {
                    src: tok.src.clone(),
                    err: ParseErr::Expected(")".to_string(), tok.kind.to_string()),
                })
            }
        };
        self.pop_discard_state();
        Ok(())
    }

    pub fn parse_assign(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        let assign = self.assert(TokKind::Eq)?;
        self.push_leaf(NodeKind::Assign, assign, false);
        self.push_state(ParseState::Expr);
        Ok(())
    }

    pub fn parse_let(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        tilog::debug!("Parsing Let");
        let let_intro = self.assert(TokKind::Let)?;
        self.push_leaf(NodeKind::LetIntroducer, let_intro, false);
        self.push_state(ParseState::LetEnd);
        self.push_state(ParseState::Expr);
        self.push_state(ParseState::Assign);
        self.push_state(ParseState::BindPattern);

        Ok(())
    }

    pub fn parse_let_end(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        let semi = self.assert(TokKind::Semi)?;
        self.push_node(NodeKind::Semi, semi, self.tree.size() - 1, false);
        Ok(())
    }

    pub fn parse_bind_pattern(&mut self) {
        self.push_state(ParseState::TypePattern);
        self.push_state(ParseState::ValPattern);
    }

    pub fn parse_val_pattern(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        match self.toks.kind_of(self.pos) {
            TokKind::Ident => {
                let name = self.assert(TokKind::Ident)?;
                self.push_leaf(NodeKind::Name, name, false);
            }
            TokKind::LPar | TokKind::LBrace => self.parse_destruct()?,
            _ => {
                return Err(Trace {
                    src: self.toks.info_of(self.pos).src.clone(),
                    err: ParseErr::Expected(
                        "identifier, tuple pattern, or struct pattern".to_string(),
                        self.toks.info_of(self.pos).kind.to_string(),
                    ),
                })
            }
        }
        Ok(())
    }

    pub fn parse_destruct(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        let tok = self.toks.info_of(self.pos);
        match tok.kind {
            TokKind::LPar => {
                let lpar = self.assert(TokKind::LPar)?;
                self.push_leaf(NodeKind::LPar, lpar, false);
            }
            TokKind::LBrace => {
                let lbrace = self.assert(TokKind::LBrace)?;
                self.push_leaf(NodeKind::LBrace, lbrace, false);
            }
            _ => {
                return Err(Trace {
                    src: tok.src.clone(),
                    err: ParseErr::Expected("( or {".to_string(), tok.kind.to_string()),
                })
            }
        };
        self.push_state(ParseState::EndValPattern);
        self.push_state(ParseState::InnerValPattern);
        self.push_state(ParseState::ValPattern);
        Ok(())
    }

    pub fn parse_inner_val_pattern(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        if let Some(comma) = self.consume_if(TokKind::Comma) {
            self.push_leaf(NodeKind::Comma, comma, false);
            self.push_state(ParseState::InnerValPattern);
            self.push_state(ParseState::ValPattern);
        };
        Ok(())
    }

    pub fn parse_end_val_pattern(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        let tok = self.toks.info_of(self.pos);
        match tok.kind {
            TokKind::RPar => {
                let rpar = self.assert(TokKind::RPar)?;
                self.push_node(NodeKind::TupleLit, rpar, self.tree.size() - 1, false);
            }
            TokKind::RBrace => {
                let rbrace = self.assert(TokKind::RBrace)?;
                self.push_node(NodeKind::StructLit, rbrace, self.tree.size() - 1, false);
            }
            _ => {
                return Err(Trace {
                    src: tok.src.clone(),
                    err: ParseErr::Expected(") or }".to_string(), tok.kind.to_string()),
                })
            }
        };
        self.pop_discard_state();
        Ok(())
    }

    pub fn parse_type_pattern(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        self.pop_discard_state();
        let maybe_colon = self.consume_if(TokKind::Colon);
        if let Some(colon) = maybe_colon {
            self.push_node(NodeKind::PatBind, colon, self.tree.size() - 1, false);
            self.pop_discard_state();
        }

        tilog::info!("TYPE {}", self.toks.kind_of(self.pos));
        match self.toks.kind_of(self.pos) {
            TokKind::Ident
            | TokKind::SignedIntTypeLit
            | TokKind::UnsignedIntTypeLit
            | TokKind::FloatTypeLit => {
                let ty = self.assert(self.toks.kind_of(self.pos))?;
                self.push_leaf(NodeKind::Name, ty, false);
            }
            TokKind::LPar | TokKind::LBrace => self.parse_structured_type()?,
            _ => {
                return Err(Trace {
                    src: self.toks.info_of(self.pos).src.clone(),
                    err: ParseErr::Expected(
                        "identifier, tuple type, or struct type".to_string(),
                        self.toks.info_of(self.pos).kind.to_string(),
                    ),
                })
            }
        }
        Ok(())
    }

    pub fn parse_structured_type(&mut self) -> Result<(), Trace<'a, ParseErr>> {
        let tok = self.toks.info_of(self.pos);
        match tok.kind {
            TokKind::LPar => {
                let lpar = self.assert(TokKind::LPar)?;
                self.push_leaf(NodeKind::LPar, lpar, false);
            }
            TokKind::LBrace => {
                let lbrace = self.assert(TokKind::LBrace)?;
                self.push_leaf(NodeKind::LBrace, lbrace, false);
            }
            _ => {
                return Err(Trace {
                    src: tok.src.clone(),
                    err: ParseErr::Expected("( or {".to_string(), tok.kind.to_string()),
                })
            }
        };

        self.push_state(ParseState::EndTypePattern);
        self.push_state(ParseState::TypePattern);
        Ok(())
    }

    pub fn push_node(&mut self, kind: NodeKind, tok: TokIx, subtree_start: usize, is_err: bool) {
        self.tree.push(Node {
            kind,
            tok,
            subtree_size: self.tree.size() - subtree_start + 1,
            is_err,
        });
        if is_err {
            self.tree.has_errs = true;
        }
    }

    pub fn push_leaf(&mut self, kind: NodeKind, tok: TokIx, is_err: bool) {
        self.tree.push(Node {
            kind,
            tok,
            subtree_size: 0,
            is_err,
        });
        if is_err {
            self.tree.has_errs = true;
        }
    }

    pub fn push_state(&mut self, state: ParseState) {
        self.state.push(state);
        assert!(self.state.len() < 1 << 20, "Probably an infinite loop");
    }

    pub fn pop_state(&mut self) -> Option<ParseState> {
        self.state.pop()
    }

    pub fn pop_discard_state(&mut self) {
        self.state.pop();
    }

    pub fn pop_state_if(&mut self, state: ParseState) -> bool {
        match self.state.last() {
            Some(st) if st == &state => {
                self.state.pop();
                true
            }
            _ => false,
        }
    }

    pub fn consume(&mut self) -> TokIx {
        tilog::debug!("Consume {}", self.toks.kind_of(self.pos));
        self.pos += 1;
        self.pos - 1
    }

    pub fn consume_if(&mut self, kind: TokKind) -> Option<TokIx> {
        match self.toks.try_info_of(self.pos) {
            Some(tok) if tok.kind == kind => Some(self.consume()),
            _ => None,
        }
    }
    pub fn assert(&mut self, kind: TokKind) -> Result<TokIx, Trace<'a, ParseErr>> {
        let res = match self.toks.try_info_of(self.pos) {
            Some(tok) if tok.kind == kind => Ok(self.consume()),
            Some(tok) => Err(Trace {
                src: tok.src,
                err: ParseErr::Expected(kind.to_string(), tok.kind.to_string()),
            }),
            None => Err(Trace {
                src: Source::eof(),
                err: ParseErr::Expected(kind.to_string(), "EOF".to_string()),
            }),
        };
        match res {
            Ok(_) => tilog::success!("Assert {}", kind),
            Err(ref trace) => tilog::error!("Assert {}: {}", kind, trace.err),
        }
        res
    }

    pub fn assert_union(&mut self, kinds: &[TokKind]) -> Result<TokIx, Trace<'a, ParseErr>> {
        let res = match self.toks.try_info_of(self.pos) {
            Some(tok) if kinds.contains(&tok.kind) => Ok(self.consume()),
            Some(tok) => Err(Trace {
                src: tok.src,
                err: ParseErr::Expected(
                    kinds
                        .iter()
                        .map(|k| k.to_string())
                        .collect::<Vec<_>>()
                        .join(" or "),
                    tok.kind.to_string(),
                ),
            }),
            None => Err(Trace {
                src: Source::eof(),
                err: ParseErr::Expected(
                    kinds
                        .iter()
                        .map(|k| k.to_string())
                        .collect::<Vec<_>>()
                        .join(" or "),
                    "EOF".to_string(),
                ),
            }),
        };
        match res {
            Ok(_) => tilog::success!(
                "Assert {}",
                kinds
                    .iter()
                    .map(|k| k.to_string())
                    .collect::<Vec<_>>()
                    .join(" or ")
            ),
            Err(ref trace) => tilog::error!(
                "Assert {}: {}",
                kinds
                    .iter()
                    .map(|k| k.to_string())
                    .collect::<Vec<_>>()
                    .join(" or "),
                trace.err
            ),
        }
        res
    }

    pub fn move_tree(self) -> ParseTree<'a> {
        self.tree
    }
}

pub struct ParseTree<'a> {
    pub nodes: Vec<Node>,
    pub toks: Rc<TokBuf<'a>>,
    pub has_errs: bool,
}

impl<'a> ParseTree<'a> {
    pub fn new(toks: Rc<TokBuf<'a>>) -> ParseTree<'a> {
        ParseTree {
            nodes: Vec::new(),
            toks,
            has_errs: false,
        }
    }

    pub fn push(&mut self, node: Node) -> NodeIx {
        let ix = self.nodes.len();
        self.nodes.push(node);
        ix
    }

    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    pub fn print(&self) {
        let indent = 0;
        let mut iter = self.nodes.iter();
        while let Some(node) = iter.next() {
            let mut indent = indent;
            while indent > 0 {
                print!("  ");
                indent -= 1;
            }
            println!("{:?}", node.kind);
        }
    }
}

pub type NodeIx = usize;

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Node {
    pub kind: NodeKind,
    pub tok: TokIx,
    pub subtree_size: usize,
    pub is_err: bool,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum NodeKind {
    // Introducers
    LetIntroducer,
    // Could be either a
    // - tuple type -- `(i32, f64, bool)`
    // - tuple expression -- `(1, 2, 3)`
    LPar,
    // Could be either a
    // - struct type -- `{x: i32, y: f64, z: bool}`
    // - struct expression -- `{x: 1, y: 2, z: 3}`
    // - block start -- `{...}`
    LBrace,

    // Terminators
    Semi,

    // Seperators
    Comma,
    Pipe,

    // Pattern Bindings
    PatBind, // ... : ...
    Assign,  // ... = ...

    // Expressions
    Name,
    VarExpr,
    LitExpr,
    TupleExpr,

    // Literals
    TupleLit,
    StructLit,

    Sof,
    Eof,
}

pub struct State {
    ps: ParseState,
    /// The outer precedence deals with how the expression
    /// should interact with others around it.
    outer_prec: Precedence,
    /// While the inner precedence defines how
    inner_prec: Precedence,
    is_err: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ParseState {
    DeclLoop,

    /// The bind pattern is used to describe the combination
    /// of a pattern binded to a type. This is not specific to
    /// let or function parameters. It is simply the left and
    /// right side of a colon.
    /// E.g. `x: i64 int or `(x, y, z): (i32, f64, bool) or `{x, y, z}: {x: i32, y: f64, z: bool}`
    BindPattern,
    /// The value pattern is used to describe the state of parsing the value
    /// pattern of a binding. It is the left hand side of the bind pattern.
    /// E.g. `x: ..` or `(x, y, z): ..` or `{x, y, z}: ..`
    ValPattern,
    /// The type pattern is used to describe the state of parsing the type
    /// pattern of a binding. It is the right hand side of the bind pattern.
    /// but slightly different in the way it is parsed.
    /// E.g. `..: (i32, f64)` or `..: {x: i32, y: f64}`
    TypePattern,
    /// The inner value pattern describes the state of the parser, when
    /// we have entered a value pattern and now need to figure out wether
    /// to close the pattern or continue looking for more patterns.
    /// E.g. `(x ...`, we dont need to check the next characters to determine
    /// wether to continue, in case of a commma for example `(x,` we know that
    /// we have more patterns to parse, pop the `,` and push the ValPattern state onto the stack.
    /// If we find a closing terminator, we pop it and push the EndValPattern state onto the stack.
    /// It handles both the tuple and struct patterns.
    InnerValPattern,
    /// The end of a bind pattern is the end of a binding pattern.
    /// It can either be the end of a let statement, or the end of a function signature.
    /// Let statements can be either `let _: <type> = ...` or `let _ := ...`
    EndBindPattern,
    /// The end of a value pattern means the closing terminator of either a tuple
    /// or a struct destructuring.
    /// E.g. `...)` or `...}`.
    EndValPattern,
    /// The same as the end value pattern just for types.
    EndTypePattern,

    /// The assign state is simply the action of
    /// assigning and expression to a binding (let, reassignment, etc.)
    Assign,

    /// Expressions
    Expr,

    TupleExpr,
    InnerTupleExpr,
    EndTupleExpr,

    Let,
    LetIntroducer,
    LetPattern,
    LetExpr,
    LetEnd,

    Func,
    FnIntroducer,
    FnNameAndParams,
    FnNameAndParamsEnd,
    FnType,
    FnTypeEnd,
    FnSignatureEnd,
    FnDeclEnd,
}

pub enum Precedence {
    Lowest,
    Assign, // .. = ..

    Dor, // .. || ..

    Dand, // .. && ..

    // Comparison operators
    Deq, // .. == ..
    Neq, // .. != ..
    Lt,  // .. <  ..
    Gt,  // .. >  ..
    Leq, // .. <= ..
    Geq, // .. >= ..

    // Numeric operators
    Add, // .. + ..
    Sub, // .. - ..
    Or,  // .. | ..
    Xor, // .. ^ ..

    // Higher precednece numeric operators
    Mul, // .. * ..
    Div, // .. / ..
    Rem, // .. % ..
    Shl, // .. << ..
    Shr, // .. >> ..
    And, // .. & ..

    // Unary operators
    Prefix,
    Postfix,

    // Absence of a precedence means that the operator is not allowed.
    Highest,
}

impl Precedence {
    pub fn as_usize(&self) -> usize {
        match self {
            Precedence::Lowest => 0,
            Precedence::Assign => 1,
            Precedence::Dor => 2,
            Precedence::Dand => 3,
            Precedence::Deq
            | Precedence::Neq
            | Precedence::Lt
            | Precedence::Gt
            | Precedence::Leq
            | Precedence::Geq => 4,
            Precedence::Add | Precedence::Sub | Precedence::Or | Precedence::Xor => 5,
            Precedence::Mul
            | Precedence::Div
            | Precedence::Rem
            | Precedence::Shl
            | Precedence::Shr
            | Precedence::And => 6,
            Precedence::Prefix | Precedence::Postfix => 7,
            Precedence::Highest => 8,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::diagnostics::StdoutDiagnoster;

    fn init_log() {
        tilog::init_logger(
            tilog::Config::default()
                .with_level(tilog::Level::Debug)
                .with_emoji(true),
        );
    }

    #[test]
    fn test_simple_pat_bind() {
        init_log();
        let src = "let x: i32 = 1;";
        println!("{}", src);
        let lex = crate::lex::Lex::new("", src.as_bytes(), StdoutDiagnoster {});
        let toks = std::rc::Rc::new(lex.lex());
        let tree = crate::tree::ParseTree::new(toks.clone());
        let mut cx = crate::tree::Cx::new(tree, toks.clone());
        cx.tree.print();
        let res = cx.parse();
        println!("{:?}", res);
        assert!(res.is_ok());
    }

    #[test]
    fn test_val_pattern() {
        tilog::init_logger(
            tilog::Config::default()
                .with_level(tilog::Level::Debug)
                .with_emoji(true),
        );
        let src = "let (x, y, z): (i32, f64, bool) = (1, 2, 3)";
        println!("{}", src);
        let lex = crate::lex::Lex::new("", src.as_bytes(), StdoutDiagnoster {});
        let toks = std::rc::Rc::new(lex.lex());
        let tree = crate::tree::ParseTree::new(toks.clone());
        let mut cx = crate::tree::Cx::new(tree, toks.clone());
        cx.tree.print();
        let res = cx.parse();
        println!("{:?}", res);
        assert!(res.is_ok());
        let tree = cx.move_tree();
        let mut iter = tree.nodes.iter();
        for node in iter.by_ref() {
            println!("{:?}", node);
        }

        assert!(false)
    }
}
