use std::fs::File;
use std::path::Path;
use std::io::Write;

use crate::package::{Composition, OracleDef, PackageInstance};
use crate::statement::{CodeBlock,Statement};
use crate::expressions::Expression;


/// TODO: Move to struct so we can have verbose versions (e.g. writing types to expressions)

fn genindentation(cnt:u8) -> String {
    let mut acc = String::new();
    for _ in 0..cnt {
        acc = format!("{}\\pcind", acc);
    }
    acc
}

struct BlockWriter<'a> {
    file: &'a mut File,
    typeinfo: bool
}

impl <'a> BlockWriter<'a> {

    fn new(file: &'a mut File) -> BlockWriter<'a> {
        BlockWriter{
            file: file,
            typeinfo: false,
        }
    }


    fn expression_to_tex(&self, expr: &Expression) -> String {
        match expr {
            Expression::Typed(_t, new_expr) => self.expression_to_tex(new_expr),
            Expression::Bot => format!("\\bot"),
            Expression::Identifier(ident) => ident.ident(),
            Expression::Add(lhs,rhs) => format!("({} + {})",
                                    self.expression_to_tex(&*lhs),
                                    self.expression_to_tex(&*rhs)),
            Expression::Equals(exprs) => {
                exprs.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(" = ")
            }
            Expression::Tuple(exprs) => {
                format!(
                    "({})",
                    exprs.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", ")
                )
            }
            Expression::FnCall(name,args) => {
                format!(
                    "{}({})",
                    name,
                    args.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", ")
                )
            }
            _ => {
                format!("{:?}", expr)
            }
        }
    }

    fn write_statement(&mut self, statement: &Statement, indentation: u8) -> std::io::Result<()> {
        match &statement {
            Statement::Abort => {
                writeln!(self.file, "{} \\pcabort\\\\", genindentation(indentation))?;
            }
            Statement::Return(None) => {
                writeln!(self.file, "{} \\pcreturn\\\\", genindentation(indentation))?;
            }
            Statement::Return(Some(expr)) => {
                writeln!(self.file, "{} \\pcreturn {}\\\\",
                         genindentation(indentation),
                         self.expression_to_tex(&expr)
                )?;
            }
            Statement::Assign(ident, None, expr) => {
                writeln!(self.file, "{} {} \\gets {}\\\\",
                         genindentation(indentation),
                         ident.ident(),
                         self.expression_to_tex(&expr)
                )?;
            }
            Statement::Assign(ident, Some(idxexpr), expr) => {
                writeln!(self.file, "{} {}[{}] \\gets {}\\\\",
                         genindentation(indentation),
                         ident.ident(),
                         self.expression_to_tex(&idxexpr),
                         self.expression_to_tex(&expr)
                )?;
            }
            Statement::Parse(ids, expr) => {
                writeln!(self.file, "{}\\pcparse {} \\pcas {}\\\\",
                         genindentation(indentation),
                         self.expression_to_tex(&expr),
                         ids.iter().map(|ident| ident.ident()).collect::<Vec<_>>().join(", ")
                )?;
            }
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                writeln!(self.file, "{}\\pcif {} \\pcthen\\\\",
                         genindentation(indentation),
                         self.expression_to_tex(&expr)
                )?;
                self.write_codeblock(&ifcode, indentation+1)?;
                if ! elsecode.0.is_empty() {
                    writeln!(self.file, "{}\\pcelse\\\\",
                             genindentation(indentation)
                    )?;
                    self.write_codeblock(&elsecode, indentation+1)?;
                }
            }
            Statement::Sample(ident, None, maybecnt, tipe) => {
                let cnt = maybecnt.expect("Expected samplified input");

                writeln!(self.file, "{}{} \\stackrel{{{}}}{{\\samples}} {:?}\\\\",
                         genindentation(indentation),
                         ident.ident(),
                         cnt, tipe
                )?;
            }
            Statement::Sample(ident, Some(idxexpr), maybecnt, tipe) => {
                let cnt = maybecnt.expect("Expected samplified input");

                writeln!(self.file, "{}{}[{}] \\stackrel{{{}}}{{\\samples}} {:?}\\\\",
                         genindentation(indentation),
                         ident.ident(),
                         self.expression_to_tex(&idxexpr),
                         cnt, tipe
                )?;
            }
            Statement::InvokeOracle {id: ident, opt_idx: None, name, args, target_inst_name: Some(target_inst_name),tipe:_} => {
                writeln!(self.file,
                         "{}{} \\stackrel{{\\gets}}{{\\mathsf{{invoke}}}} {}({}) \\pccomment{{{:?}}} \\\\",
                         genindentation(indentation),
                         ident.ident(), name,
                         args.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", "),
                         target_inst_name
                )?;
            }
            Statement::InvokeOracle {id: ident, opt_idx: Some(idxexpr), name, args, target_inst_name: Some(target_inst_name),tipe:_} => {
                writeln!(self.file,
                         "{}{}[{}] \\stackrel{{\\gets}}{{\\mathsf{{invoke}}}} {}({}) \\pccomment{{{:?}}} \\\\",
                         genindentation(indentation),
                         ident.ident(),
                         self.expression_to_tex(&idxexpr),
                         name,
                         args.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", "),
                         target_inst_name
                )?;
            }
            Statement::InvokeOracle {target_inst_name: None, ..} => {
                unreachable!("Expect oracle-lowlevelified input")
            }
        }
        Ok(())
    }

    fn write_codeblock(&mut self, codeblock: &CodeBlock, indentation: u8) -> std::io::Result<()>  {
        for stmt in &codeblock.0 {
            self.write_statement(&stmt, indentation)?
        }
        Ok(())
    }

}

pub fn tex_write_oracle(oracle: &OracleDef, pkgname: &str, target: &Path) -> std::io::Result<()> {
    let fname = target.join(format!("{}_{}.tex", pkgname, oracle.sig.name));
    let mut file = File::create(fname)?;
    let mut writer = BlockWriter::new(&mut file);

    writeln!(writer.file, "\\procedure{{\\O{{{}}}({})}}{{",
             oracle.sig.name,
             oracle.sig.args.iter().map(|(a,b)| a.clone()).collect::<Vec<_>>().join(", ")
    )?;

    let codeblock = &oracle.code;
    writer.write_codeblock(codeblock, 0)?;

    writeln!(writer.file, "}}")?;
    Ok(())
}

pub fn tex_write_package(package: &PackageInstance, target: &Path) -> std::io::Result<()> {
    for oracle in &package.pkg.oracles {
        tex_write_oracle(oracle, &package.name, target)?
    }
    Ok(())
}

pub fn tex_write_composition(composition: &Composition, target: &Path) -> std::io::Result<()> {
    for pkg in &composition.pkgs {
        tex_write_package(pkg, target)?
    }
    Ok(())
}
