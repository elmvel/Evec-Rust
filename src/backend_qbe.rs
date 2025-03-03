use std::fmt;

use crate::lexer::Location;
use crate::ast::*;
use crate::ir::*;

impl fmt::Display for TempValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.tag)
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.name)?;
        for stmt in &self.stmts {
            write!(f, "{stmt}")?;
        }
        Ok(())
    }
}

impl fmt::Display for TopLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TopLevel::Type => todo!(),
            TopLevel::Data => todo!(),
            TopLevel::Function(name, params, ret_type, blocks, is_main) => {
                let qbe_return_type = match ret_type {
                    Some(ref typ) => typ.qbe_ext_type(),
                    None => if *is_main { "w" } else { "" },
                };
                write!(f, "export function {qbe_return_type} ${name}(")?;

                let mut param_count = 0;
                write!(f, "{}", (params
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
                    write!(f, "{block}")?;
                }

                writeln!(f, "}}");
                Ok(())
            },
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Assignment(tv, instr) => {
                let typ = if matches!(instr, Instruction::Call(..)) {
                    tv.typ.qbe_abi_type()
                } else {
                    tv.typ.qbe_type()
                };
                writeln!(f, "{} ={} {instr}", Value::Temp(tv.clone()), typ)
            }
            Statement::Discard(instr) => writeln!(f, "{instr}"),
            Statement::Raw(text) => writeln!(f, "{text}"),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Global(name) => write!(f, "${name}"),
            Value::Constant(name) => write!(f, "{name}"),
            Value::Temp(tv) => write!(f, "%.{tv}"),
            Value::Label(name) => write!(f, "@{name}"),
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Ret(opt) => {
                match opt {
                    Some(v) => write!(f, "ret {v}"),
                    None => write!(f, "ret"),
                }
            },
            Instruction::Copy(v) => {
                write!(f, "copy {v}")
            },
            Instruction::Add(v1, v2) => {
                write!(f, "add {v1}, {v2}")
            },
            Instruction::Sub(v1, v2) => {
                write!(f, "sub {v1}, {v2}")
            },
            Instruction::Mul(v1, v2) => {
                write!(f, "mul {v1}, {v2}")
            },
            Instruction::Div(v1, v2) => {
                write!(f, "div {v1}, {v2}")
            },
            Instruction::DivU(v1, v2) => {
                write!(f, "udiv {v1}, {v2}")
            },
            Instruction::Call(v, temps) => {
                // TODO: variadics
                write!(f, "call {v}(")?;
                write!(f, "{}", (temps
                                  .iter()
                                  .map(|TempValue{tag, typ}| {
                                      let qtype = typ.qbe_ext_type();
                                      format!("{qtype} %.{tag}")
                                  })
                                  .collect::<Vec<String>>()
                                  .join(", ")
                ))?;
                write!(f, ")")
            },
            Instruction::Load(v_ptr, typ) => {
                let qtype = typ.qbe_type();
                if typ.is_struct() {
                    match typ.struct_kind {
                        StructKind::Array | StructKind::Slice => {
                            write!(f, "copy {v_ptr}")
                        },
                        _ => todo!(),
                    }
                } else {
                    if typ.sizeof() == 8 || typ.sizeof() == 4 {
                        write!(f, "load{qtype} {v_ptr}")
                    } else {
                        let ext = typ.qbe_ext_type();
                        write!(f, "load{ext} {v_ptr}")
                    }
                }
            },
            Instruction::Store(v_ptr, v, typ) => {
                if typ.is_struct() {
                    match typ.struct_kind {
                        StructKind::Array => {
                            let Some(ref inner) = typ.inner else { unreachable!() };
                            let bytes = typ.elements * inner.sizeof();
                            write!(f, "blit {v}, {v_ptr}, {bytes}")
                        },
                        StructKind::Slice => {
                            let bytes = typ.sizeof();
                            write!(f, "blit {v}, {v_ptr}, {bytes}")
                        },
                        _ => todo!(),
                    }
                } else {
                    let qtype = typ.qbe_type();
                    write!(f, "store{qtype} {v}, {v_ptr}")
                }
            },
            Instruction::Alloc(typ) => {
                // TODO: get alignment per type
                write!(f, "alloc8 {}", typ.sizeof())
            },
            Instruction::Jmp(v) => {
                write!(f, "jmp {v}")
            },
            Instruction::Jnz(v_test, v_true, v_false) => {
                write!(f, "jnz {v_test}, {v_true}, {v_false}")
            },
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
                        write!(f, "cu{instr}{qtyp} {v1}, {v2}")
                    } else {
                        write!(f, "cs{instr}{qtyp} {v1}, {v2}")
                    }
                } else {
                    write!(f, "c{instr}{qtyp} {v1}, {v2}")
                }
            },
            Instruction::Cast(v, as_typ, from_typ) => {
                if as_typ.assert_number(ldef!()).is_ok() && from_typ.assert_number(ldef!()).is_ok() {
                    match from_typ.kind {
                        TypeKind::U64 | TypeKind::S64 => write!(f, "copy {v}"),
                        TypeKind::U32 | TypeKind::S32 => {
                            let s = if from_typ.unsigned() { "u" } else { "s" };
                            if as_typ.sizeof() > from_typ.sizeof() {
                                write!(f, "ext{s}w {v}")
                            } else {
                                write!(f, "copy {v}")
                            }
                        },
                        TypeKind::U16 | TypeKind::S16 => {
                            let s = if from_typ.unsigned() { "u" } else { "s" };
                            write!(f, "ext{s}h {v}")
                        },
                        TypeKind::U8 | TypeKind::S8 => {
                            let s = if from_typ.unsigned() { "u" } else { "s" };
                            write!(f, "ext{s}b {v}")
                        },
                        _ => unreachable!()
                    }
                } else {
                    todo!("unsupported conversion")
                }
            },
        }
    }
}
