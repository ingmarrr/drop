use crate::ir::{Const, DataItem, Func, Instr, Mem, Reg};

pub struct AsmGen {
    pub funcs: Vec<Func>,
    pub ir_data: Vec<DataItem>,
    pub instrs: Vec<String>,
    pub regs: Vec<Reg>,
    pub mems: Vec<Mem>,
    pub stack: Vec<Mem>,
    pub stack_size: u64,
    pub label_count: i64,
}

impl AsmGen {
    pub fn new(funcs: Vec<Func>, ir_data: Vec<DataItem>) -> AsmGen {
        AsmGen {
            funcs,
            ir_data,
            instrs: Vec::new(),
            regs: Vec::new(),
            mems: Vec::new(),
            stack: Vec::new(),
            stack_size: 0,
            label_count: 0,
        }
    }

    pub fn gen(&mut self) -> String {
        let data = self.gen_data();
        let main = self.gen_funcs();
        format!("{}{}", data, main)
    }

    pub fn gen_exit(&self) -> String {
        r#"
    mov X16, #1
    svc #0
"#
        .to_string()
    }

    pub fn gen_funcs(&self) -> String {
        if self.funcs.is_empty() {
            return String::new();
        }

        let mut buf = ".text".to_string();
        for func in self.funcs.iter() {
            let locality = if func.is_global { ".global " } else { "" };
            buf.push_str(&format!(
                "\n{}{}\n.align {}\n{}",
                locality,
                func.name,
                func.align,
                self.gen_instrs(func)
            ));
        }
        buf
    }

    pub fn gen_instrs(&self, func: &Func) -> String {
        let mut buf = format!("{}:\n", func.name);

        for instr in func.instrs.iter() {
            match instr {
                Instr::Add { rd, rn, op } => {
                    buf.push_str(&format!("    add X{}, X{}, {}\n", rd, rn, op))
                }
                Instr::Sub { rd, rn, op } => {
                    buf.push_str(&format!("    sub X{}, X{}, {}\n", rd, rn, op))
                }
                Instr::Mov { rd, op } => buf.push_str(&format!("    mov X{}, {}\n", rd, op)),
                Instr::Sys { op } => buf.push_str(&format!("    svc {}\n", op)),
            }
        }
        buf
    }

    pub fn gen_data(&mut self) -> String {
        if self.ir_data.is_empty() {
            return String::new();
        }

        let mut buf = ".data\n".to_string();
        for data in self.ir_data.iter() {
            buf.push_str(&format!("L{}:\n", data.label));
            match data.val {
                Const::AsciiString(ref val) => {
                    buf.push_str(&format!("    .ascii \"{}\"\n", val));
                }
                Const::NtString(ref val) => {
                    buf.push_str(&format!("    .asciz \"{}\"\n", val));
                }
                Const::Bytes(ref val) => {
                    let str_val = val
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<String>>()
                        .join(", ");
                    buf.push_str(&format!("    .byte {}\n", str_val));
                }
                Const::HalfWords(ref val) => {
                    let str_val = val
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<String>>()
                        .join(", ");
                    buf.push_str(&format!("    .hword {}\n", str_val));
                }
                Const::Words(ref val) => {
                    let str_val = val
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<String>>()
                        .join(", ");
                    buf.push_str(&format!("    .word {}\n", str_val));
                }
                Const::DoubleWords(ref val) => {
                    let str_val = val
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<String>>()
                        .join(", ");
                    buf.push_str(&format!("    .dword {}\n", str_val));
                }
                Const::Floats(ref val) => {
                    let str_val = val
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<String>>()
                        .join(", ");
                    buf.push_str(&format!("    .float {}\n", str_val));
                }
                Const::Doubles(ref val) => {
                    let str_val = val
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<String>>()
                        .join(", ");
                    buf.push_str(&format!("    .double {}\n", str_val));
                }
            }
        }
        buf
    }

    pub fn gen_label(&mut self) -> String {
        self.label_count += 1;
        format!(".L{}", self.label_count)
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::Operand;

    use super::*;

    #[test]
    fn test_asm_gen_empty() {
        let asm_gen = AsmGen::new(Vec::new(), Vec::new());
        let main = asm_gen.gen_funcs();
        assert_eq!(main, "");
    }

    #[test]
    fn test_asm_add() {
        let mut asm_gen = AsmGen::new(
            vec![Func {
                name: "_main".to_string(),
                instrs: vec![Instr::Add {
                    rd: Reg::X(0),
                    rn: Reg::X(1),
                    op: Operand::Imm(2),
                }],
                is_global: true,
                align: 2,
            }],
            Vec::new(),
        );
        let main = asm_gen.gen();
        assert_eq!(
            main,
            r#".text
.global _main
.align 2
_main:
    add X0, X1, #2
"#
        );
    }

    #[test]
    fn test_asm_sub() {
        let mut asm_gen = AsmGen::new(
            vec![Func {
                name: "_main".to_string(),
                instrs: vec![Instr::Sub {
                    rd: Reg::X(0),
                    rn: Reg::X(1),
                    op: Operand::Imm(2),
                }],
                is_global: true,
                align: 2,
            }],
            Vec::new(),
        );
        let main = asm_gen.gen();
        assert_eq!(
            main,
            r#".text
.global _main
.align 2
_main:
    sub X0, X1, #2
"#
        );
    }

    #[test]
    fn test_exit() {
        let mut asm = AsmGen::new(
            vec![Func {
                name: "_main".to_string(),
                instrs: vec![
                    Instr::Mov {
                        rd: Reg::X(16),
                        op: Operand::Imm(1),
                    },
                    Instr::Mov {
                        rd: Reg::X(0),
                        op: Operand::Imm(69),
                    },
                    Instr::Sys {
                        op: Operand::Imm(0),
                    },
                ],
                is_global: true,
                align: 2,
            }],
            Vec::new(),
        );

        let main = asm.gen();

        assert_eq!(
            main,
            r#".text
.global _main
.align 2
_main:
    mov X16, #1
    mov X0, #69
    svc #0
"#
        );
    }
}
