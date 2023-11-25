#[rustfmt::skip]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokKind {
    Ident,
    // Number Types
    LitInt,
    LitReal,
    LitChar,
    LitString,

    // Keywords
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,

    // Operators
    Add, // +
    Sub, // -
    Mul, // *
    Div, // /

    // Terminators/Seperators
    Semi, // ;
    Comma,// ,

    // Keywords
    Eof,
    Invalid,
}

impl From<u8> for TokKind {
    fn from(value: u8) -> Self {
        match value {
            b'+' => TokKind::Add,
            b'-' => TokKind::Sub,
            b'*' => TokKind::Mul,
            b'/' => TokKind::Div,
            b'\0' => TokKind::Eof,
            b';' => TokKind::Semi,
            b',' => TokKind::Comma,
            _ => TokKind::Invalid,
        }
    }
}

impl TokKind {
    #[rustfmt::skip]
    pub fn is_symbol(&self) -> bool {
        matches!(self,
            TokKind::Add
            | TokKind::Sub
            | TokKind::Mul
            | TokKind::Div
            | TokKind::Semi
            | TokKind::Comma
        )
    }
}

/// Source information for a token.
///
/// `file` -> is the name of the file the token was found in.
/// `pos`  -> is the byte offset of the token in the file.
/// `line` -> is the line number of the token in the file.
/// `col`  -> is the column number of the token in the file.
/// `len`  -> is the length of the token in bytes.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Source<'a> {
    pub file: &'a str,
    pub pos: usize,
    pub line: usize,
    pub col: usize,
    pub len: usize,
}

impl<'a> Source<'a> {
    pub fn eof() -> Self {
        Self {
            file: "",
            pos: 0,
            line: 0,
            col: 0,
            len: 0,
        }
    }
}

impl<'a> Source<'a> {
    pub fn try_merge_all(sources: &[Self]) -> Option<Self> {
        let mut iter = sources.iter();
        let mut merged = *iter.next()?;
        for source in iter {
            merged = merged.try_merge(source)?;
        }
        Some(merged)
    }

    #[rustfmt::skip]
    pub fn try_merge(&self, other: &Self) -> Option<Self> {
        if self.file == other.file && self.pos + self.len == other.pos {
            let file = self.file;
            let pos = self.pos;
            let line = self.line;
            let col = self.col;
            let len = self.len + other.len;
            Some(Self { file, pos, line, col, len })
        } else {
            None
        }
    }

    #[rustfmt::skip]
    pub fn merge(&self, other: &Self) -> Self {
        let file = self.file;
        let pos = self.pos;
        let line = self.line;
        let col = self.col;
        let len = self.len + other.len;
        Self { file, pos, line, col, len }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Tok<'a> {
    pub kind: TokKind,
    pub src: Source<'a>,
    pub val: Lit<'a>,
}

impl std::fmt::Display for TokKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokKind::Ident => write!(f, "Ident"),

            // Number Types
            TokKind::LitInt => write!(f, "Literal Int"),
            TokKind::LitReal => write!(f, "Literal Real"),
            TokKind::LitChar => write!(f, "Literal Char"),
            TokKind::LitString => write!(f, "Literal String"),

            // Keywords
            TokKind::U8 => write!(f, "U8"),
            TokKind::U16 => write!(f, "U16"),
            TokKind::U32 => write!(f, "U32"),
            TokKind::U64 => write!(f, "U64"),
            TokKind::I8 => write!(f, "I8"),
            TokKind::I16 => write!(f, "I16"),
            TokKind::I32 => write!(f, "I32"),
            TokKind::I64 => write!(f, "I64"),

            // Operators
            TokKind::Add => write!(f, "Add"),
            TokKind::Sub => write!(f, "Sub"),
            TokKind::Mul => write!(f, "Mul"),
            TokKind::Div => write!(f, "Div"),

            // Terminators/Seperators
            TokKind::Semi => write!(f, "Semi"),
            TokKind::Comma => write!(f, "Comma"),

            TokKind::Eof => write!(f, "Eof"),
            TokKind::Invalid => write!(f, "Invalid"),
        }
    }
}

impl From<&str> for TokKind {
    fn from(value: &str) -> Self {
        match value {
            "u8" => TokKind::U8,
            "u16" => TokKind::U16,
            "u32" => TokKind::U32,
            "u64" => TokKind::U64,
            "i8" => TokKind::I8,
            "i16" => TokKind::I16,
            "i32" => TokKind::I32,
            "i64" => TokKind::I64,
            _ => TokKind::Ident,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Lit<'a> {
    String(&'a str),
    Char(u8),
    // U8(u8),
    // U16(u16),
    // U32(u32),
    Uint(u64),
    // I8(i8),
    // I16(i16),
    // I32(i32),
    // I64(i64),
    Bin(u64),
    Oct(u64),
    Hex(u64),
    Real(f64),
}
