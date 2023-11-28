pub mod asm;
pub mod ast;
pub mod diagnostics;
pub mod err;
pub mod ir;
pub mod lex;
pub mod repl;
pub mod run;
pub mod syn;
pub mod tok;
pub mod tree;

use std::io::Write;

pub use repl::repl;
pub use run::run;

pub fn assemble(name: &str) -> std::io::Result<std::process::ExitStatus> {
    std::process::Command::new("as")
        .arg(&format!("{}.s", name))
        .arg("-o")
        .arg(&format!("{}.o", name))
        .spawn()
        .expect("Failed to run 'as'")
        .wait()
}

pub fn xrun() -> std::io::Result<std::process::Output> {
    std::process::Command::new("xcrun")
        .args(["-sdk", "macosx", "--show-sdk-path"])
        .output()
}

pub fn link(name: &str) -> std::io::Result<std::process::ExitStatus> {
    let syslibroot = std::str::from_utf8(&xrun().unwrap().stdout)
        .unwrap()
        .trim_end()
        .to_string();
    std::process::Command::new("ld")
        .args([
            "-e",
            "_main",
            "-l",
            "System",
            "-syslibroot",
            &syslibroot,
            "-o",
            name,
            &format!("{}.o", name),
        ])
        .spawn()
        .expect("Failed to run 'ld'")
        .wait()
}

pub fn execute(name: &str) -> std::io::Result<std::process::ExitStatus> {
    let as_status = assemble(name)?;
    if !as_status.success() {
        return Ok(as_status);
    }
    let ld_status = link(name)?;
    if !ld_status.success() {
        return Ok(ld_status);
    }

    std::process::Command::new(format!("./{}", name))
        .spawn()
        .expect("Failed to run './a.out'")
        .wait()
}

pub fn save(name: &str, content: &str) -> std::io::Result<()> {
    let mut file = std::fs::File::create(format!("{}.s", name))?;
    file.write_all(content.as_bytes())?;
    Ok(())
}
