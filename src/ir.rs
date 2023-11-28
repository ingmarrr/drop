use crate::{
    ast::{AsIr, AstLit, BinExpr, BinOp, Expr},
    diagnostics::Diagnoster,
    err::GenErr,
};

pub struct AstParser<D>
where
    D: Diagnoster,
{
    pub asir: Vec<AsIr>,
    pub instrs: Vec<Instr>,
    pub data: Vec<DataItem>,
    pub regs: Vec<i32>,
    pub pos: usize,
    pub diag: D,
}

impl<D> AstParser<D>
where
    D: Diagnoster,
{
    pub fn new(asir: Vec<AsIr>, diag: D) -> AstParser<D> {
        AstParser::<D> {
            asir,
            instrs: Vec::new(),
            data: Vec::new(),
            regs: Vec::new(),
            pos: 0,
            diag,
        }
    }

    pub fn gen_all(&mut self) -> Result<(), GenErr> {
        for asir in self.asir.clone().iter() {
            match asir {
                AsIr::Expr(ref expr) => {
                    tilog::info!("Generating expr: {:?}", expr);
                    let instr = self.gen_expr(expr.clone())?;
                    self.instrs.push(instr)
                }
                AsIr::Let(ref let_) => {
                    tilog::info!("Generating instructions: {:?}", let_);
                }
            }
        }
        Ok(())
    }

    pub fn gen_expr(&mut self, expr: Expr) -> Result<Instr, GenErr> {
        match expr {
            Expr::Bin(binexpr) => self.gen_binexpr(binexpr),
            Expr::Lit(lit) => self.gen_lit_expr(lit),
        }
    }

    pub fn gen_binexpr(&mut self, binexpr: BinExpr) -> Result<Instr, GenErr> {
        match binexpr.op {
            BinOp::Add => {
                let lhs = self.gen_op(*binexpr.lhs)?;
                let rhs = self.gen_op(*binexpr.rhs)?;
                match (lhs, rhs) {
                    (Operand::Reg(rd), Operand::Reg(rn)) => Ok(Instr::Add {
                        rd,
                        rn,
                        op: Operand::Reg(rd),
                    }),

                    (Operand::Reg(rd), Operand::Imm(imm)) => Ok(Instr::Add {
                        rd,
                        rn: rd,
                        op: Operand::Imm(imm),
                    }),
                    (Operand::Imm(imm), Operand::Reg(rn)) => Ok(Instr::Add {
                        rd: rn,
                        rn,
                        op: Operand::Imm(imm),
                    }),
                    (Operand::Imm(imm), Operand::Imm(imm2)) => Ok(Instr::Add {
                        rd: Reg::X(self.reg_iota()),
                        rn: Reg::X(self.reg_iota()),
                        op: Operand::Imm(imm + imm2),
                    }),

                    (Operand::Reg(rd), Operand::Mem(mem)) => Ok(Instr::Add {
                        rd,
                        rn: rd,
                        op: Operand::Mem(mem),
                    }),
                    (Operand::Mem(mem), Operand::Reg(rn)) => Ok(Instr::Add {
                        rd: rn,
                        rn,
                        op: Operand::Mem(mem),
                    }),
                    _ => unimplemented!(),
                }
            }
            BinOp::Sub => {
                let lhs = self.gen_op(*binexpr.lhs)?;
                let rhs = self.gen_op(*binexpr.rhs)?;
                match (lhs, rhs) {
                    (Operand::Reg(rd), Operand::Reg(rn)) => Ok(Instr::Sub {
                        rd,
                        rn,
                        op: Operand::Reg(rd),
                    }),

                    (Operand::Reg(rd), Operand::Imm(imm)) => Ok(Instr::Sub {
                        rd,
                        rn: rd,
                        op: Operand::Imm(imm),
                    }),
                    (Operand::Imm(imm), Operand::Reg(rn)) => Ok(Instr::Sub {
                        rd: rn,
                        rn,
                        op: Operand::Imm(imm),
                    }),
                    (Operand::Imm(imm), Operand::Imm(imm2)) => Ok(Instr::Sub {
                        rd: Reg::X(self.reg_iota()),
                        rn: Reg::X(self.reg_iota()),
                        op: Operand::Imm(imm - imm2),
                    }),

                    (Operand::Reg(rd), Operand::Mem(mem)) => Ok(Instr::Sub {
                        rd,
                        rn: rd,
                        op: Operand::Mem(mem),
                    }),
                    (Operand::Mem(mem), Operand::Reg(rn)) => Ok(Instr::Sub {
                        rd: rn,
                        rn,
                        op: Operand::Mem(mem),
                    }),
                    _ => unimplemented!(),
                }
            }
        }
    }

    pub fn gen_lit_expr(&mut self, lit: AstLit) -> Result<Instr, GenErr> {
        Ok(Instr::Mov {
            rd: Reg::X(self.reg_iota()),
            op: self.gen_lit_op(lit)?,
        })
    }

    pub fn gen_op(&mut self, expr: Expr) -> Result<Operand, GenErr> {
        match expr {
            Expr::Lit(lit) => self.gen_lit_op(lit),
            Expr::Bin(bin) => {
                let binexpr = self.gen_binexpr(bin)?;
                Ok(Operand::Reg(Reg::X(self.push(binexpr))))
            }
        }
    }

    pub fn gen_lit_op(&mut self, lit: AstLit) -> Result<Operand, GenErr> {
        match lit {
            AstLit::U8(val) => Ok(Operand::Imm(val as i64)),
            AstLit::U16(val) => Ok(Operand::Imm(val as i64)),
            AstLit::U32(val) => Ok(Operand::Imm(val as i64)),
            AstLit::U64(val) => Ok(Operand::Imm(val as i64)),
            AstLit::I8(val) => Ok(Operand::Imm(val as i64)),
            AstLit::I16(val) => Ok(Operand::Imm(val as i64)),
            AstLit::I32(val) => Ok(Operand::Imm(val as i64)),
            AstLit::I64(val) => Ok(Operand::Imm(val)),
            AstLit::String(val) => Ok(Operand::Data(self.push_data(Const::AsciiString(val)))),
        }
    }

    fn push(&mut self, instr: Instr) -> i32 {
        let pos = self.instrs.len() as i32;
        self.instrs.push(instr);
        pos
    }

    fn push_data(&mut self, data: Const) -> usize {
        let pos = self.data.len();
        self.data.push(DataItem {
            label: pos,
            val: data,
        });
        pos
    }

    fn reg_iota(&mut self) -> i32 {
        let iota = self.regs.len() as i32;
        self.regs.push(iota);
        iota
    }
}

pub struct Func {
    pub name: String,
    pub instrs: Vec<Instr>,
    pub is_global: bool,
    pub align: usize,
}

pub enum Instr {
    Add { rd: Reg, rn: Reg, op: Operand },
    Sub { rd: Reg, rn: Reg, op: Operand },
    Mov { rd: Reg, op: Operand },
    Sys { op: Operand },
}

pub enum Operand {
    Reg(Reg),
    Imm(i64),
    Mem(Mem),
    Data(usize),
    Complex(ComplexOperand),
}

impl std::fmt::Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Reg(reg) => write!(f, "{}", reg),
            Operand::Imm(imm) => write!(f, "#{}", imm),
            Operand::Mem(mem) => write!(f, "[{}]", mem),
            Operand::Data(data) => write!(f, "L{}", data),
            Operand::Complex(complex) => write!(f, "{}", complex),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Reg {
    // General purpose registers
    X(i32),

    // Registers with specific purposes
    SP,
    LR,
    FP,
    IP,
}

impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Reg::X(i) => write!(f, "{}", i),
            Reg::SP => write!(f, "SP"),
            Reg::LR => write!(f, "LR"),
            Reg::FP => write!(f, "FP"),
            Reg::IP => write!(f, "IP"),
        }
    }
}

pub struct Mem {
    pub addr: usize,
    pub val: i64,
    pub size: usize,
    pub perms: Perms,
    pub label: Option<String>,
}

impl std::fmt::Display for Mem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.label {
            Some(ref label) => write!(f, "{}", label),
            None => write!(f, "[{}]", self.addr),
        }
    }
}

pub enum Perms {
    R,
    RW,
    RX,
    RWX,
}

pub enum ComplexOperand {
    Shifted { base: Reg, shift: Shift },
    Extended { base: Reg, ext: Ext },
}

impl std::fmt::Display for ComplexOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComplexOperand::Shifted { base, shift } => write!(f, "{} {}", base, shift),
            ComplexOperand::Extended { base, ext } => write!(f, "{} {}", base, ext),
        }
    }
}

pub enum Shift {
    LSL(i32),
    LSR(i32),
    ASR(i32),
    ROR(i32),
}

impl std::fmt::Display for Shift {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Shift::LSL(i) => write!(f, "LSL #{}", i),
            Shift::LSR(i) => write!(f, "LSR #{}", i),
            Shift::ASR(i) => write!(f, "ASR #{}", i),
            Shift::ROR(i) => write!(f, "ROR #{}", i),
        }
    }
}

pub enum Ext {
    UXTB,
    UXTH,
    UXTW,
    UXTX,
    SXTB,
    SXTH,
    SXTW,
    SXTX,
}

impl std::fmt::Display for Ext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ext::UXTB => write!(f, "UXTB"),
            Ext::UXTH => write!(f, "UXTH"),
            Ext::UXTW => write!(f, "UXTW"),
            Ext::UXTX => write!(f, "UXTX"),
            Ext::SXTB => write!(f, "SXTB"),
            Ext::SXTH => write!(f, "SXTH"),
            Ext::SXTW => write!(f, "SXTW"),
            Ext::SXTX => write!(f, "SXTX"),
        }
    }
}

pub struct DataItem {
    pub label: usize,
    pub val: Const,
}

pub enum Const {
    NtString(String),
    AsciiString(String),

    Bytes(Vec<u8>),
    HalfWords(Vec<u16>),
    Words(Vec<u32>),
    DoubleWords(Vec<u64>),

    Floats(Vec<f32>),
    Doubles(Vec<f64>),
}
