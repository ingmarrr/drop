use crate::tok::TokKind;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AsIr {
    Expr(Expr),
    Let(Let),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Let {
    pub name: String,
    pub ty: Option<String>,
    pub expr: Box<Expr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Bin(BinExpr),
    Lit(AstLit),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BinExpr {
    pub lhs: Box<Expr>,
    pub op: BinOp,
    pub rhs: Box<Expr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum BinOp {
    Add,
    Sub,
}

impl From<TokKind> for BinOp {
    fn from(value: TokKind) -> Self {
        match value {
            TokKind::Add => Self::Add,
            TokKind::Sub => Self::Sub,
            _ => panic!("Invalid token kind: {:?}", value),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstLit {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    // U128(u128),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    // I128(i128),
    String(String),
}

// impl<'a> From<tok::Lit<'a>> for AstLit {
//     fn from(value: tok::Lit<'a>) -> Self {
//         match value {
//             tok::Lit::String(val) => Self::String(val.to_string()),
//             tok::Lit::Char(val) => Self::U8(val),
//             tok::Lit::U8(val) => Self::U8(val),
//             tok::Lit::U16(val) => Self::U16(val),
//             tok::Lit::U32(val) => Self::U32(val),
//             tok::Lit::U64(val) => Self::U64(val),
//             tok::Lit::I8(val) => Self::I8(val),
//             tok::Lit::I16(val) => Self::I16(val),
//             tok::Lit::I32(val) => Self::I32(val),
//             tok::Lit::I64(val) => Self::I64(val),
//             tok::Lit::Bin(val) => Self::U64(val),
//             _ => unimplemented!(),
//         }
//     }
// }

pub enum Partial {
    Initiator(Initiator),
    Name(String),
    TypeAssign(),
}

pub enum Initiator {
    Let,
    Const,
    Mut,
    Fn,
    Struct,
    Type,
}
