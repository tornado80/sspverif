use std::io::{Result, Write};
//use std::io::prelude::*;

use crate::statement::CodeBlock;
use crate::statement::Statement;
use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

pub trait SmtFmt {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()>;
}

#[derive(Debug)]
pub enum SmtExpr {
    Atom(String),
    List(Vec<SmtExpr>)
}

impl SmtFmt for SmtExpr {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()> {
        match self {
            SmtExpr::Atom(str) => write!(write, "{}", str),
            SmtExpr::List(lst) => {
                write!(write, "(")?;
                for elem in lst {
                    elem.write_smt_to(write)?;
                    write!(write, " ")?;
                };
                write!(write, ")")
            },

        }
    }
}

impl Into<SmtExpr> for Expression {
    fn into(self) -> SmtExpr {
        match self {
            Expression::BooleanLiteral(litname) => {
                SmtExpr::Atom(litname)
            },
            Expression::Equals(exprs) => {
                let mut acc = vec![];
                acc.push(SmtExpr::Atom("=".to_string()));
                for expr in exprs {
                    acc.push((*expr).clone().into());
                }
                SmtExpr::List(acc)
            },
            Expression::Identifier(ident) => {
                let Identifier::Scalar(identname) = *ident;
                SmtExpr::Atom(identname)
            },
            Expression::Bot => {
                SmtExpr::List(vec![SmtExpr::Atom("bot".to_string())])
            },
            Expression::Sample(tipe) => {
                // TODO: fix this later! This is generally speaking not correct!
                SmtExpr::List(vec![SmtExpr::Atom("rand".to_string())])
            },
            _ => { panic!("not implemented"); }
        }
    }
}

impl Into<SmtExpr> for Statement {
    fn into(self) -> SmtExpr {
        match self {
            Statement::IfThenElse(cond, ifcode, elsecode) => {
                SmtExpr::List(vec![
                    SmtExpr::Atom("ite".to_string()),
                    cond.into(),
                    ifcode.into(),
                    elsecode.into(),
                ])
            }
            _ => {panic!("not implemented")}
        }
    }

}

impl Into<SmtExpr> for CodeBlock {
    fn into(self) -> SmtExpr {
        let mut result = None;
        for stmt in self.0.iter().rev() {
            result = Some(match stmt {
                Statement::IfThenElse(cond, ifcode, elsecode) => {
                    SmtExpr::List(vec![
                        SmtExpr::Atom("ite".to_string()),
                        cond.clone().into(),
                        ifcode.clone().into(),
                        elsecode.clone().into(),
                    ])
                },
                Statement::Assign(ident, expr) => {
                    let Identifier::Scalar(identname) = ident;
                    SmtExpr::List(vec![
                        SmtExpr::Atom("let".to_string()),
                        SmtExpr::List(vec![
                            SmtExpr::List(vec![
                                SmtExpr::Atom(identname.clone()),
                                expr.clone().into()
                            ])
                        ]),
                        result.unwrap()
                    ])
                }
                _ => {panic!("not implemented")}
            });
        }
        result.unwrap()
    }
}

impl Into<SmtExpr> for Type {
    fn into(self) -> SmtExpr {
        match &self {
            Type::Bits(length) => {
                // TODO make sure we define this somewhere
                SmtExpr::Atom(format!("Bits_{}", length))
            },
            Type::Boolean => {
                SmtExpr::Atom("Bool".to_string())
            },
            _ => {panic!("not implemented!")}
        }
    }
}

impl SmtFmt for CodeBlock {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()> {
        write!(write, "(")?;
        for line in &self.0 {
            line.write_smt_to(write)?;
        }
        write!(write, ")")?;
        Ok(())
    }
}


impl SmtFmt for Statement {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()> {
        match self {
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                write!(write, "(ite ")?;
                expr.write_smt_to(write)?;
                ifcode.write_smt_to(write)?;
                elsecode.write_smt_to(write)?;
                write!(write, ")\n")?;
            },
            _ => { panic!("no implemented"); }
        }
        Ok(())
    }
}


impl SmtFmt for Expression {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()> {
        match self {
            Expression::BooleanLiteral(litname) => {
                write!(write, "{}", litname)?;
            }
            _ => { panic!("no implemented"); }
        }
        Ok(())
    }
}





/*

Bigger Story
============

We have a Type/Sort/Datastructuure with all variable (names) in that scope.

The set_value code will advance one step and *copy* all variables from the old Datastructure to the new one apart from the one we have just written.

If/Then/Else via hirarchial counters.

For if-then-else we have a different stucture/sorty/type inside the ite then outside so for each branch at the end we need to filter and generate the correct "outer" structure

returns/aborts inside (as opposed to just one at the very end) are still a big headache

*/


/*
fn set_value(identifier: Identifier, expression: Expression, varname: String, ctr: i32, scope: Scope) {
    let mut result = String::new();
    result.push(format!("(let (({varname}.{ctr} (make-variable-mapping",
                        varname=varname, ctr=ctr));

    for ident in scope.all() {
        if ident != identifier {
            println!("(access-variable-mapping-at-{ident} variablemapping{ctr-1})")
        } else {
            println!("({:?})", expression)
        }
        println!(")");
    }
    println!(")))");
}


pub fn generate_smt(block: &Vec<Box<Statement>>, varname:String) -> () {
    let mut ctr:i32 = 1;
    let mut scope = Scope::new();

    type_inference(block, scope);

    for stmt in block {
        match &**stmt {
            Statement::Abort => {

            },
            Statement::Return(expr) => {

            },
            Statement::Assign(id, expr) => {
                set_value(id, expr, varname, ctr, scope);
            },
            Statement::TableAssign(id, idx, expr) => {

            },
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                varnameif = "{varname}.{ctr}.if";
                let ifsmt = generate_smt(ifcode, varnameif);
                varnameelse = "{varname}.{ctr}.else";
                let elsesmt = generate_smt(elsecode, varnameelse);
                "(let (({varname}.{ctr} (scope-adapt (ite {expr} ({ifsmt}) ({elsesmt})))))"
            }
        }
        ctr = ctr + 1;
    }
    for i in 1..ctr {
        println!(")");
    }
}
*/
