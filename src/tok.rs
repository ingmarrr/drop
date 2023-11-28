pub type TokIx = usize;

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
#[derive(Debug)]
pub struct TokBuf<'a> {
    pub file: Option<&'a str>,
    pub src: &'a [u8],
    pub toks: Vec<TokIx>,
    pub infos: Vec<Tok<'a>>,
    pub ints: Vec<u64>,
    pub reals: Vec<f64>,
    pub strs: Vec<&'a str>,
    pub idents: Vec<&'a str>,
}

impl<'a> TokBuf<'a> {
    pub fn new(file: Option<&'a str>, src: &'a [u8]) -> TokBuf<'a> {
        TokBuf::<'a> {
            file,
            src,
            toks: Vec::new(),
            infos: Vec::new(),
            ints: Vec::new(),
            reals: Vec::new(),
            strs: Vec::new(),
            idents: Vec::new(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = TokIx> + '_ {
        self.toks.iter().copied()
    }

    pub fn push(&mut self, kind: TokKind, src: Source<'a>, val: Option<Val<'a>>) -> TokIx {
        let ix = self.infos.len();
        let ptr = val.map(|lit| match lit {
            Val::Ident(val) => self.push_ident(val),
            Val::String(val) => self.push_str(val),
            Val::Char(val) => self.push_int(val as u64),
            Val::Uint(val) => self.push_int(val),
            Val::Real(val) => self.push_real(val),
        });
        let tok = Tok { kind, src, ptr };
        self.infos.push(tok);
        self.toks.push(ix);
        ix
    }

    pub fn get(&self, ix: usize) -> Option<TokIx> {
        self.toks.get(ix).copied()
    }

    pub fn len(&self) -> usize {
        self.toks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.toks.is_empty()
    }

    pub fn info_of(&self, ix: TokIx) -> Tok<'a> {
        self.infos.get(ix).copied().unwrap()
    }

    pub fn try_info_of(&self, ix: TokIx) -> Option<Tok<'a>> {
        self.infos.get(ix).copied()
    }

    pub fn kind_of(&self, ix: TokIx) -> TokKind {
        self.infos.get(ix).map(|tok| tok.kind).unwrap()
    }

    pub fn try_kind_of(&self, ix: TokIx) -> Option<TokKind> {
        self.infos.get(ix).map(|tok| tok.kind)
    }

    pub fn src_of(&self, ix: TokIx) -> Source<'a> {
        self.infos.get(ix).map(|tok| tok.src).unwrap()
    }

    pub fn try_src_of(&self, ix: TokIx) -> Option<Source<'a>> {
        self.infos.get(ix).map(|tok| tok.src)
    }

    #[rustfmt::skip]
    pub fn val_of(&self, ix: TokIx) -> Result<Val<'a>, String> {
        let tok = self.info_of(ix);
        println!("tok: {:?}", tok);
        match tok.ptr {
            Some(ptr) => match tok.kind {
                TokKind::IntLit => Ok(Val::Uint(self.ints[ptr])),
                TokKind::RealLit => Ok(Val::Real(self.reals[ptr])),
                TokKind::CharLit => Ok(Val::Char(self.ints[ptr] as u8)),
                TokKind::StringLit => Ok(Val::String(self.strs[ptr])),
                TokKind::Ident => Ok(Val::Ident(self.idents[ptr])),
                _ => unreachable!(),
            },
            None => Err(tok.kind.to_string())
        }
    }

    pub fn try_val_of(&self, ix: TokIx) -> Option<Val<'a>> {
        self.infos.get(ix).and_then(|tok| match tok.ptr {
            Some(ptr) => match tok.kind {
                TokKind::IntLit => Some(Val::Uint(self.ints[ptr])),
                TokKind::RealLit => Some(Val::Real(self.reals[ptr])),
                TokKind::CharLit => Some(Val::Char(self.ints[ptr] as u8)),
                TokKind::StringLit => Some(Val::String(self.strs[ptr])),
                _ => None,
            },
            None => None,
        })
    }

    pub fn str_of(&self, ix: TokIx) -> &'a str {
        let info = self.info_of(ix);
        let src_buf = &self.src[info.src.pos..info.src.pos + info.src.len];
        std::str::from_utf8(src_buf).unwrap()
    }

    fn push_int(&mut self, val: u64) -> usize {
        self.ints.push(val);
        self.ints.len() - 1
    }

    fn push_real(&mut self, val: f64) -> usize {
        self.reals.push(val);
        self.reals.len() - 1
    }

    fn push_str(&mut self, val: &'a str) -> usize {
        self.strs.push(val);
        self.strs.len() - 1
    }

    fn push_ident(&mut self, val: &'a str) -> usize {
        self.idents.push(val);
        self.idents.len() - 1
    }
}

#[rustfmt::skip]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokKind {
    Ident,
    // Literals
    IntLit,     // Integer: 123
    RealLit,    // Real: 123.456
    CharLit,    // Character: 'a'
    StringLit,  // String: "Hello World"
    SignedIntTypeLit, // Integer Type: i8, i16, i32, i64, isize
    UnsignedIntTypeLit, // Integer Type: u8, u16, u32, u64, usize
    FloatTypeLit, // Real Type: f32, f64


    // Keywords
    Let,        // let
    Type,       // type
    Func,         // fn

    // Operators
    Add,   // +
    Sub,   // -
    Mul,   // *
    Div,   // /
    Eq,    // =

    // Double Operators
    Deq,   // ==
    Neq,   // !=

    // Openers
    LPar,       // (
    LBrace,     // {
    LBrack,     // [

    // Closers
    RPar,       // )
    RBrace,     // }
    RBrack,     // ]

    // Terminators/Seperators
    Semi,  // ;
    Comma, // ,
    Colon, // :

    Sof,
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
            b':' => TokKind::Colon,
            b'=' => TokKind::Eq,
            b'(' => TokKind::LPar,
            b')' => TokKind::RPar,
            b'{' => TokKind::LBrace,
            b'}' => TokKind::RBrace,
            b'[' => TokKind::LBrack,
            b']' => TokKind::RBrack,
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
    pub fn sof(file: &'a str) -> Self {
        Self {
            file,
            pos: 0,
            line: 0,
            col: 0,
            len: 0,
        }
    }

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
    pub ptr: Option<usize>, // pub val: Lit<'a>,
}

impl std::fmt::Display for TokKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokKind::Ident => write!(f, "Ident"),

            // Number Types
            TokKind::IntLit => write!(f, "IntLiteral"),
            TokKind::RealLit => write!(f, "RealLiteral"),
            TokKind::CharLit => write!(f, "CharLiteral"),
            TokKind::StringLit => write!(f, "StringLiteral"),
            TokKind::SignedIntTypeLit => write!(f, "SignedIntTypeLiteral"),
            TokKind::UnsignedIntTypeLit => write!(f, "UnsignedIntTypeLiteral"),
            TokKind::FloatTypeLit => write!(f, "FloatTypeLiteral"),

            // Keywords
            TokKind::Let => write!(f, "Let"),
            TokKind::Type => write!(f, "Type"),
            TokKind::Func => write!(f, "Function"),

            // Operators
            TokKind::Add => write!(f, "Add"),
            TokKind::Sub => write!(f, "Sub"),
            TokKind::Mul => write!(f, "Mul"),
            TokKind::Div => write!(f, "Div"),
            TokKind::Eq => write!(f, "Equals"),

            TokKind::Deq => write!(f, "DoubleEquals"),
            TokKind::Neq => write!(f, "NotEquals"),

            // Terminators/Seperators
            TokKind::Semi => write!(f, "Semi"),
            TokKind::Comma => write!(f, "Comma"),
            TokKind::Colon => write!(f, "Colon"),

            TokKind::Sof => write!(f, "StartOfFile"),
            TokKind::Eof => write!(f, "EndOfFile"),
            TokKind::Invalid => write!(f, "Invalid"),

            TokKind::LPar => write!(f, "LeftParenthesis"),
            TokKind::LBrace => write!(f, "LeftBrace"),
            TokKind::LBrack => write!(f, "LeftBracket"),
            TokKind::RPar => write!(f, "RightParenthesis"),
            TokKind::RBrace => write!(f, "RightBrace"),
            TokKind::RBrack => write!(f, "RightBracket"),
        }
    }
}

impl From<&str> for TokKind {
    fn from(value: &str) -> Self {
        match value {
            "let" => TokKind::Let,
            "type" => TokKind::Type,
            "func" => TokKind::Func,
            _ => TokKind::Ident,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Val<'a> {
    Ident(&'a str),
    String(&'a str),
    Char(u8),
    Uint(u64),
    Real(f64),
}
