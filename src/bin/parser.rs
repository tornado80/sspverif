extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use std::env;
use std::fs;

use sspds::types::Type;
use sspds::package::OracleDef;
use sspds::package::OracleSig;
use sspds::statement::CodeBlock;
use sspds::statement::Statement;
use sspds::expressions::Expression;
use sspds::identifier::Identifier;

#[derive(Parser)]
#[grammar = "parser/pkg.pest"]
pub struct SspParser;

use pest::iterators::{Pair,Pairs};


fn handle_type(tipe: Pair<Rule>) -> Type {
    match tipe.as_rule() {
        Rule::type_integer => Type::Integer,
        Rule::type_maybe => Type::Maybe(Box::new(handle_type(tipe.into_inner().next().unwrap()))),
        Rule::type_bits => Type::Bits(tipe.into_inner().next().unwrap().as_str().to_string()),
        Rule::type_fn => {
            let mut inner = tipe.into_inner();
            let argtipes = inner.next().unwrap().into_inner().map(|spec| {
                println!("{:#?}", spec);
                handle_type(spec.into_inner().next().unwrap())
            }).collect();
            let tipe = handle_type(inner.next().unwrap());
            Type::Fn(argtipes, Box::new(tipe))
        },
        _ => {
            unreachable!("{:#?}", tipe)
        }
    }
}


fn handle_decl_list(state: Pair<Rule>) -> Vec<(String, Type)> {
    state.into_inner().map(|entry| {
        let mut inner = entry.into_inner();
        let identifier = inner.next().unwrap().as_str();
        let tipe = handle_type(inner.next().unwrap());
        (identifier.to_string(), tipe)
    }).collect()
}


// TODO: identifier is optional
fn handle_arglist(arglist: Pair<Rule>) -> Vec<(String, Type)> {
    arglist.into_inner().map(|arg| {
        let mut inner = arg.into_inner();
        let id = inner.next().unwrap().as_str();
        let tipe = handle_type(inner.next().unwrap());
        (id.to_string(), tipe)
    }).collect()
}


fn handle_oracle_sig(oracle_sig: Pair<Rule>) -> OracleSig {
    let mut inner = oracle_sig.into_inner();
    let name = inner.next().unwrap().as_str();
    let maybe_arglist = inner.next().unwrap();
    let args =
        if maybe_arglist.as_str() == "" {
            vec![]
        } else {
            handle_arglist(maybe_arglist.into_inner().next().unwrap())
        };


    let maybe_tipe = inner.next();
    let tipe = match maybe_tipe {
        None => Type::Empty,
        Some(t) => handle_type(t)
    };

    OracleSig {
        name: name.to_string(),
        tipe: tipe,
        args: args
    }
}


fn handle_expression(expr: Pair<Rule>) -> Expression {
    match expr.as_rule() { // expr_equals | expr_not_equals | fn_call | table_access | identifier
        Rule::expr_equals => {
            Expression::Equals(expr.into_inner().map(handle_expression).collect())
        },
        Rule::expr_not_equals => {
            Expression::Not(Box::new(Expression::Equals(expr.into_inner().map(handle_expression).collect())))
        },
        Rule::expr_none => {
            let tipe = handle_type(expr.into_inner().next().unwrap());
            Expression::None(tipe)
        }
        Rule::expr_some => {
            let expr = handle_expression(expr.into_inner().next().unwrap());
            Expression::Some(Box::new(expr))
        }
        Rule::fn_call => {
            let mut inner = expr.into_inner();
            let ident = inner.next().unwrap().as_str();
            let args = match inner.next() {
                None => vec![],
                Some(inner_args) => inner_args.into_inner().map(handle_expression).collect()
            };
            Expression::FnCall(ident.to_string(), args)
        },
        Rule::identifier => {
            Identifier::new_scalar(expr.as_str()).to_expression()
        }
        _ => unreachable!("{:#?}", expr)
    }
}


fn handle_code(code: Pair<Rule>) -> CodeBlock {
    CodeBlock(code.into_inner().map(|stmt| {
        match stmt.as_rule() { // assign | return_stmt | abort | ite
            Rule::ite => {
                let mut inner = stmt.into_inner();
                let expr = handle_expression(inner.next().unwrap());
                let ifcode = handle_code(inner.next().unwrap());
                let maybe_elsecode = inner.next();
                let elsecode = match maybe_elsecode {
                    None => CodeBlock(vec![]),
                    Some(c) => handle_code(c)
                };
                Statement::IfThenElse(expr, ifcode, elsecode)
            },
            Rule::return_stmt => {
                let mut inner = stmt.into_inner();
                let maybe_expr = inner.next();
                let expr = match maybe_expr {
                    None => None,
                    Some(e) => Some(handle_expression(e))
                };
                Statement::Return(expr)
            },
            Rule::abort => Statement::Abort,
            Rule::sample => {
                let mut inner = stmt.into_inner();
                let ident = Identifier::new_scalar(inner.next().unwrap().as_str());
                let tipe = handle_type(inner.next().unwrap());
                Statement::Assign(ident, Expression::Sample(tipe))
            },
            Rule::assign => {
                let mut inner = stmt.into_inner();
                let ident = Identifier::new_scalar(inner.next().unwrap().as_str());
                let expr = handle_expression(inner.next().unwrap());
                Statement::Assign(ident, expr)
            },
            _ => { unreachable!("{:#?}", stmt) }
        }
    }).collect())
}


fn handle_oracle_def(oracle_def: Pair<Rule>) -> OracleDef {
    let mut inner = oracle_def.into_inner();
    let sig = handle_oracle_sig(inner.next().unwrap());
    let code = handle_code(inner.next().unwrap());


    OracleDef {
        sig: sig,
        code: code
    }
}


fn handle_pkg_spec(pkg_spec: Pair<Rule>) {
    for spec in pkg_spec.into_inner() {
        match spec.as_rule() {
            Rule::state => {
                match spec.into_inner().next() {
                    None => println!("state: []"),
                    Some(inner_spec) => println!("state: {:#?}", handle_decl_list(inner_spec))
                };
            },
            Rule::params => {println!("params: {:#?}", handle_decl_list(spec.into_inner().next().unwrap()));},
            Rule::import_oracles => println!("import_oracles"),
            Rule::oracle_def => {println!("oracle_def {:#?}", handle_oracle_def(spec));},
            _ => unreachable!("state"),
        }
    }
}


fn handle_pkg(pkg: Pair<Rule>) {
    let mut inner = pkg.into_inner();
    let name = inner.next().unwrap().as_str();
    let spec = inner.next().unwrap();
    handle_pkg_spec(spec);
    println!("{:?}", name);
}


fn main() {
    let args: Vec<String> = env::args().collect();
    let filecontent = fs::read_to_string(args[1].clone()).expect("cannot read file");
    let result = SspParser::parse(Rule::package, &filecontent);

    for elt in result.unwrap() {
        handle_pkg(elt);
    }
}
