use crate::tok::Source;
use termion::color;

pub trait Diagnoster {
    fn report(&mut self, diag: Diagnostic<'_>);
}

pub struct StdoutDiagnoster {}

impl Diagnoster for StdoutDiagnoster {
    fn report(&mut self, diag: Diagnostic<'_>) {
        let kind = match diag.kind {
            DiagnosticKind::Note => "note",
            DiagnosticKind::Warning => "warning",
            DiagnosticKind::Error => "error",
        };
        use DiagnosticKind as DK;
        let color = match diag.kind {
            DK::Note => color::Fg(color::Blue).to_string(),
            DK::Warning => color::Fg(color::Yellow).to_string(),
            DK::Error => color::Fg(color::Red).to_string(),
        };
        println!(
            "{}{}{} -> {}:{}:{}: {}",
            color,
            kind,
            color::Fg(color::Reset),
            diag.src.file,
            diag.src.line,
            diag.src.col,
            diag.msg
        );
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum DiagnosticKind {
    Note,
    Warning,
    Error,
}

pub struct Diagnostic<'a> {
    pub kind: DiagnosticKind,
    pub msg: String,
    pub src: Source<'a>,
}
