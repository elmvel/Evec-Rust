use std::fmt::{self, Write, Display};

use crate::ast::*;
use crate::const_eval::ConstExpr;
use crate::ir::*;
use crate::gen::Compiletime;
use crate::lexer::Location;

impl TempValue {
    pub fn dump_qbe<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a TempValue, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.0.tag)
            }
        }
        Helper(self, comptime)
    }
}

impl Block {
    pub fn dump_qbe<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a Block, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                writeln!(f, "{}", self.0.name.dump_qbe(self.1))?;
                for stmt in &self.0.stmts {
                    write!(f, "{}", stmt.dump_qbe(self.1))?;
                }
                Ok(())
            }
        }
        Helper(self, comptime)
    }
}

impl TopLevel {
    pub fn dump_qbe<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a TopLevel, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.0 {
                    TopLevel::Type => todo!(),
                    TopLevel::Data => todo!(),
                    TopLevel::Function(name, params, ret_type, blocks, is_main) => {
                        let qbe_return_type = match ret_type {
                            Some(ref typ) => typ.qbe_ext_type(),
                            None => {
                                if *is_main {
                                    "w"
                                } else {
                                    ""
                                }
                            }
                        };
                        write!(f, "export function {qbe_return_type} ${name}(")?;
                        
                        let mut param_count = 0;
                        write!(
                            f,
                            "{}",
                            (params
                             .iter()
                             .map(|Param(tag, typ)| {
                                 let f = format!("{} %.{param_count}", typ.qbe_ext_type());
                                 param_count += 1;
                                 f
                             })
                             .collect::<Vec<String>>()
                             .join(", "))
                        )?;
                        
                        writeln!(f, ") {{");
                        
                        for block in blocks {
                            write!(f, "{}", block.dump_qbe(self.1))?;
                        }
                        
                        writeln!(f, "}}");
                        Ok(())
                    }
                }
            }
        }
        Helper(self, comptime)
    }
}

impl Statement {
    pub fn dump_qbe<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a Statement, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.0 {
                    Statement::Assignment(tv, instr) => {
                        let typ = if matches!(instr, Instruction::Call(..)) {
                            tv.typ.qbe_abi_type()
                        } else {
                            tv.typ.qbe_type()
                        };
                        writeln!(f, "{} ={} {}", Value::Temp(tv.clone()).dump_qbe(self.1), typ, instr.dump_qbe(self.1))
                    }
                    Statement::Discard(instr) => writeln!(f, "{}", instr.dump_qbe(self.1)),
                    Statement::Raw(text) => writeln!(f, "{text}"),
                }
            }
        }
        Helper(self, comptime)
    }
}

impl Value {
    pub fn dump_qbe<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a Value, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.0 {
                    Value::Global(name) => write!(f, "${name}"),
                    Value::Constant(name) => write!(f, "{name}"),
                    Value::Temp(tv) => write!(f, "%.{}", tv.dump_qbe(self.1)),
                    Value::Label(name) => write!(f, "@{name}"),
                }
            }
        }
        Helper(self, comptime)
    }
}

impl Instruction {
    pub fn dump_qbe<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a Instruction, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.0 {
                    Instruction::Ret(opt) => match opt {
                        Some(v) => write!(f, "ret {}", v.dump_qbe(self.1)),
                        None => write!(f, "ret"),
                    },
                    Instruction::Copy(v) => {
                        write!(f, "copy {}", v.dump_qbe(self.1))
                    }
                    Instruction::Add(v1, v2) => {
                        write!(f, "add {}, {}", v1.dump_qbe(self.1), v2.dump_qbe(self.1))
                    }
                    Instruction::Sub(v1, v2) => {
                        write!(f, "sub {}, {}", v1.dump_qbe(self.1), v2.dump_qbe(self.1))
                    }
                    Instruction::Mul(v1, v2) => {
                        write!(f, "mul {}, {}", v1.dump_qbe(self.1), v2.dump_qbe(self.1))
                    }
                    Instruction::Div(v1, v2) => {
                        write!(f, "div {}, {}", v1.dump_qbe(self.1), v2.dump_qbe(self.1))
                    }
                    Instruction::DivU(v1, v2) => {
                        write!(f, "udiv {}, {}", v1.dump_qbe(self.1), v2.dump_qbe(self.1))
                    }
                    Instruction::Call(v, temps) => {
                        // TODO: variadics
                        write!(f, "call {}(", v.dump_qbe(self.1))?;
                        write!(
                            f,
                            "{}",
                            (temps
                             .iter()
                             .map(|TempValue { tag, typ, .. }| {
                                 let qtype = typ.qbe_ext_type();
                                 format!("{qtype} %.{tag}")
                             })
                             .collect::<Vec<String>>()
                             .join(", "))
                        )?;
                        write!(f, ")")
                    }
                    Instruction::Load(v_ptr, ptr_typ) => {
                        let typ = ptr_typ.deref(self.1);
                        let qtype = typ.qbe_type();
                        if typ.is_struct() {
                            match typ {
                                Type::Array(..) | Type::Slice(..) => {
                                    write!(f, "copy {}", v_ptr.dump_qbe(self.1))
                                }
                                _ => todo!(),
                            }
                        } else {
                            if typ.sizeof(self.1) == 8 || typ.sizeof(self.1) == 4 {
                                write!(f, "load{qtype} {}", v_ptr.dump_qbe(self.1))
                            } else {
                                let ext = typ.qbe_ext_type();
                                write!(f, "load{ext} {}", v_ptr.dump_qbe(self.1))
                            }
                        }
                    }
                    Instruction::Store(v_ptr, v, typ) => {
                        if typ.is_struct() {
                            match typ {
                                Type::Array(lazyexpr, typeid) => {
                                    let inner = self.1.fetch_type(*typeid).unwrap();
                                    let constexpr = lazyexpr.const_resolve();
                                    let ConstExpr::Number(n) = constexpr else {
                                        unreachable!("user land error")
                                    };
                                    let bytes = n as usize * inner.sizeof(self.1);
                                    write!(f, "blit {}, {}, {bytes}", v.dump_qbe(self.1), v_ptr.dump_qbe(self.1))
                                }
                                Type::Slice(..) => {
                                    let bytes = typ.sizeof(self.1);
                                    write!(f, "blit {}, {}, {bytes}", v.dump_qbe(self.1), v_ptr.dump_qbe(self.1))
                                }
                                _ => todo!(),
                            }
                        } else {
                            let qtype = typ.qbe_type();
                            write!(f, "store{qtype} {}, {}", v.dump_qbe(self.1), v_ptr.dump_qbe(self.1))
                        }
                    }
                    Instruction::Alloc(typ) => {
                        // TODO: get alignment per type
                        write!(f, "alloc8 {}", typ.sizeof(self.1))
                    }
                    Instruction::Jmp(v) => {
                        write!(f, "jmp {}", v.dump_qbe(self.1))
                    }
                    Instruction::Jnz(v_test, v_true, v_false) => {
                        write!(f, "jnz {}, {}, {}",
                               v_test.dump_qbe(self.1),
                               v_true.dump_qbe(self.1),
                               v_false.dump_qbe(self.1)
                        )
                    }
                    Instruction::Cmp(op, typ, v1, v2) => {
                        let instr = match op {
                            Op::Gt => "gt",
                            Op::Lt => "lt",
                            Op::Ge => "ge",
                            Op::Le => "le",
                            Op::EqEq => "eq",
                            Op::NotEq => "ne",
                            _ => unreachable!(),
                        };
                        let qtyp = typ.qbe_type();
                        if op.qbe_depends_sign() {
                            if typ.unsigned() {
                                write!(f, "cu{instr}{qtyp} {}, {}",
                                       v1.dump_qbe(self.1),
                                       v2.dump_qbe(self.1),
                                )
                            } else {
                                write!(f, "cs{instr}{qtyp} {}, {}",
                                       v1.dump_qbe(self.1),
                                       v2.dump_qbe(self.1),
                                )
                            }
                        } else {
                            write!(f, "c{instr}{qtyp} {}, {}",
                                   v1.dump_qbe(self.1),
                                   v2.dump_qbe(self.1),
                            )
                        }
                    }
                    Instruction::Cast(v, as_typ, from_typ) => {
                        if as_typ.assert_number(ldef!()).is_ok() && from_typ.assert_number(ldef!()).is_ok() {
                            match from_typ {
                                Type::U64 | Type::S64 => write!(f, "copy {}", v.dump_qbe(self.1)),
                                Type::U32 | Type::S32 => {
                                    let s = if from_typ.unsigned() { "u" } else { "s" };
                                    if as_typ.sizeof(self.1) > from_typ.sizeof(self.1) {
                                        write!(f, "ext{s}w {}", v.dump_qbe(self.1))
                                    } else {
                                        write!(f, "copy {}", v.dump_qbe(self.1))
                                    }
                                }
                                Type::U16 | Type::S16 => {
                                    let s = if from_typ.unsigned() { "u" } else { "s" };
                                    write!(f, "ext{s}h {}", v.dump_qbe(self.1))
                                }
                                Type::U8 | Type::S8 => {
                                    let s = if from_typ.unsigned() { "u" } else { "s" };
                                    write!(f, "ext{s}b {}", v.dump_qbe(self.1))
                                }
                                _ => unreachable!(),
                            }
                        } else {
                            todo!("unsupported conversion")
                        }
                    }
                }
            }
        }
        Helper(self, comptime)
    }
}
