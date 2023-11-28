use crate::tok;

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum LexErr {
    #[error("Lex Error: Invalid character: {0}")]
    InvalidChar(char),

    #[error("Lex Error: Integer will overflow: {0}")]
    IntegerOverflow(String),

    #[error(transparent)]
    IntegerParseErr(#[from] std::num::ParseIntError),

    #[error(transparent)]
    FloatParseErr(#[from] std::num::ParseFloatError),

    #[error(transparent)]
    Utf8Err(#[from] std::str::Utf8Error),
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum ParseErr {
    #[error("Parse Error: Expected {0}, found {1}")]
    Expected(String, String),

    #[error("Parse Error: Invalid Token: {0}")]
    InvalidToken(String),

    #[error(transparent)]
    LexErr(#[from] LexErr),
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum SynErr {
    #[error("Syntax Error: Expected {0}, found {1}")]
    Expected(String, String),

    #[error("Syntax Error: Invalid Token: {0}")]
    InvalidToken(String),

    #[error("Syntax Error: Unsigned integer cannot be negative: {0}")]
    UnsignedCannotBeNegative(String),

    #[error(transparent)]
    LexErr(#[from] LexErr),
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum GenErr {
    #[error("Invalid instruction: {0}")]
    InvalidInstr(String),

    #[error("Invalid operand: {0}")]
    InvalidOperand(String),

    #[error("Invalid register: {0}")]
    InvalidReg(String),

    #[error("Invalid immediate: {0}")]
    InvalidImm(String),

    #[error("Invalid memory: {0}")]
    InvalidMem(String),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Trace<'a, E>
where
    E: std::error::Error,
{
    pub src: tok::Source<'a>,
    pub err: E,
}

impl<'a> From<Trace<'a, LexErr>> for Trace<'a, SynErr> {
    fn from(trace: Trace<'a, LexErr>) -> Self {
        Self {
            src: trace.src,
            err: trace.err.into(),
        }
    }
}

impl std::fmt::Display for Trace<'_, LexErr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let line = self.src.line;
        let col = self.src.col;
        let file = self.src.file;
        let err = self.err.to_string();

        write!(f, "LexErr: {}:{}:{}: {}", file, line, col, err)
    }
}

impl std::fmt::Display for Trace<'_, SynErr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let line = self.src.line;
        let col = self.src.col;
        let file = self.src.file;
        let err = self.err.to_string();

        write!(f, "Syntax Error: {}:{}:{}: {}", file, line, col, err)
    }
}
