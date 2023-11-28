use std::io::Write;

use crate::{
    asm::AsmGen,
    diagnostics::StdoutDiagnoster,
    ir::{AstParser, Func},
    lex::Lex,
    syn::Syn,
};

pub fn repl() {
    tilog::init_logger(
        tilog::Config::default()
            .with_level(tilog::Level::Debug)
            .with_emoji(true),
    );
    tilog::info!("Starting REPL");

    loop {
        print!("> ");
        std::io::stdout().flush().unwrap();

        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();

        let lexer = Lex::new("", input.as_bytes(), StdoutDiagnoster {});
        let toks = lexer.lex();
        let mut parser = Syn::new(toks, StdoutDiagnoster {});
        let ast = parser.parse_all();
        if let Err(e) = ast {
            tilog::error!("{}", e);
            continue;
        }
        let asir = parser.asir;
        let mut irgen = AstParser::new(asir, StdoutDiagnoster {});
        let (mut instrs, data) = match irgen.gen_all() {
            Ok(()) => (irgen.instrs, irgen.data),
            Err(e) => {
                tilog::error!("{}", e);
                continue;
            }
        };
        instrs.extend(vec![
            crate::ir::Instr::Mov {
                rd: crate::ir::Reg::X(0),
                op: crate::ir::Operand::Imm(69),
            },
            crate::ir::Instr::Mov {
                rd: crate::ir::Reg::X(16),
                op: crate::ir::Operand::Imm(1),
            },
            crate::ir::Instr::Sys {
                op: crate::ir::Operand::Imm(0),
            },
        ]);
        let mut asmgen = AsmGen::new(
            vec![Func {
                name: "_main".into(),
                instrs,
                is_global: true,
                align: 2,
            }],
            data,
        );
        let asm = asmgen.gen();
        tilog::info!("{}", asm);
        let res = crate::save("main", &asm);
        if let Err(e) = res {
            tilog::error!("{}", e);
            continue;
        }
        let execres = crate::execute("main");
        if let Err(e) = execres {
            tilog::error!("{}", e);
            continue;
        } else {
            tilog::info!("Program exited with status: {}", execres.unwrap());
        }

        // let mut compiler = Compiler::new(&mut parser);
        // let mut vm = VM::new(&mut compiler);

        // match vm.run() {
        //     Ok(_) => {}
        //     Err(e) => {
        //         tilog::error!("{}", e);
        //     }
        // }
    }
}
