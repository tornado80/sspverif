use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::OracleDef;
use crate::package::OracleSig;
use crate::package::Package;
use crate::statement::CodeBlock;
use crate::statement::Statement;
use crate::types::Type;

use super::common::*;
use super::Rule;

use pest::iterators::Pair;

use std::collections::HashMap;

pub fn handle_decl_list(state: Pair<Rule>) -> Vec<(String, Type)> {
    state
        .into_inner()
        .map(|entry| {
            let mut inner = entry.into_inner();
            let identifier = inner.next().unwrap().as_str();
            let tipe = handle_type(inner.next().unwrap());
            (identifier.to_string(), tipe)
        })
        .collect()
}

// TODO: identifier is optional
pub fn handle_arglist(arglist: Pair<Rule>) -> Vec<(String, Type)> {
    arglist
        .into_inner()
        .map(|arg| {
            let mut inner = arg.into_inner();
            let id = inner.next().unwrap().as_str();
            let tipe = handle_type(inner.next().unwrap());
            (id.to_string(), tipe)
        })
        .collect()
}

pub fn handle_oracle_sig(oracle_sig: Pair<Rule>) -> OracleSig {
    let mut inner = oracle_sig.into_inner();
    let name = inner.next().unwrap().as_str();
    let maybe_arglist = inner.next().unwrap();
    let args = if maybe_arglist.as_str() == "" {
        vec![]
    } else {
        handle_arglist(maybe_arglist.into_inner().next().unwrap())
    };

    let maybe_tipe = inner.next();
    let tipe = match maybe_tipe {
        None => Type::Empty,
        Some(t) => handle_type(t),
    };

    OracleSig {
        name: name.to_string(),
        tipe,
        args,
    }
}

pub fn handle_expression(expr: Pair<Rule>) -> Expression {
    match expr.as_rule() {
        // expr_equals | expr_not_equals | fn_call | table_access | identifier
        Rule::expr_add => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Add(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_sub => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Sub(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_mul => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Mul(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_div => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Div(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_tuple => Expression::Tuple(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_equals => Expression::Equals(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_not_equals => Expression::Not(Box::new(Expression::Equals(
            expr.into_inner().map(handle_expression).collect(),
        ))),
        Rule::expr_none => {
            let tipe = handle_type(expr.into_inner().next().unwrap());
            Expression::None(tipe)
        }
        Rule::expr_some => {
            let expr = handle_expression(expr.into_inner().next().unwrap());
            Expression::Some(Box::new(expr))
        }
        Rule::expr_unwrap => {
            let expr = handle_expression(expr.into_inner().next().unwrap());
            Expression::Unwrap(Box::new(expr))
        }
        Rule::table_access => {
            let mut inner = expr.into_inner();
            let ident = inner.next().unwrap().as_str();
            let expr = handle_expression(inner.next().unwrap());
            Expression::TableAccess(Identifier::new_scalar(ident), Box::new(expr))
        }
        Rule::fn_call => {
            let mut inner = expr.into_inner();
            let ident = inner.next().unwrap().as_str();
            let args = match inner.next() {
                None => vec![],
                Some(inner_args) => inner_args.into_inner().map(handle_expression).collect(),
            };
            Expression::FnCall(ident.to_string(), args)
        }
        Rule::identifier => Identifier::new_scalar(expr.as_str()).to_expression(),
        _ => unreachable!("{:#?}", expr),
    }
}

pub fn handle_code(code: Pair<Rule>) -> CodeBlock {
    CodeBlock(
        code.into_inner()
            .map(|stmt| {
                match stmt.as_rule() {
                    // assign | return_stmt | abort | ite
                    Rule::ite => {
                        let mut inner = stmt.into_inner();
                        let expr = handle_expression(inner.next().unwrap());
                        let ifcode = handle_code(inner.next().unwrap());
                        let maybe_elsecode = inner.next();
                        let elsecode = match maybe_elsecode {
                            None => CodeBlock(vec![]),
                            Some(c) => handle_code(c),
                        };
                        Statement::IfThenElse(expr, ifcode, elsecode)
                    }
                    Rule::return_stmt => {
                        let mut inner = stmt.into_inner();
                        let maybe_expr = inner.next();
                        let expr = maybe_expr.map(handle_expression);
                        Statement::Return(expr)
                    }
                    Rule::assert => {
                        let mut inner = stmt.into_inner();
                        let expr = handle_expression(inner.next().unwrap());
                        Statement::IfThenElse(
                            expr,
                            CodeBlock(vec![]),
                            CodeBlock(vec![Statement::Abort]),
                        )
                    }
                    Rule::abort => Statement::Abort,
                    Rule::sample => {
                        let mut inner = stmt.into_inner();
                        let ident = Identifier::new_scalar(inner.next().unwrap().as_str());
                        let tipe = handle_type(inner.next().unwrap());
                        Statement::Sample(ident, None, tipe)
                        //Statement::Assign(ident, Expression::Sample(tipe))
                    }
                    Rule::assign => {
                        let mut inner = stmt.into_inner();
                        let ident = Identifier::new_scalar(inner.next().unwrap().as_str());
                        let expr = handle_expression(inner.next().unwrap());
                        Statement::Assign(ident, None, expr)
                    }
                    Rule::table_sample => {
                        let mut inner = stmt.into_inner();
                        let ident = Identifier::new_scalar(inner.next().unwrap().as_str());
                        let index = handle_expression(inner.next().unwrap());
                        let tipe = handle_type(inner.next().unwrap());
                        Statement::Sample(ident, Some(index), tipe)
                    }
                    Rule::table_assign => {
                        let mut inner = stmt.into_inner();
                        let ident = Identifier::new_scalar(inner.next().unwrap().as_str());
                        let index = handle_expression(inner.next().unwrap());
                        let expr = handle_expression(inner.next().unwrap());
                        Statement::Assign(ident, Some(index), expr)
                    }
                    Rule::invocation => {
                        let mut inner = stmt.into_inner();
                        let ident = Identifier::new_scalar(inner.next().unwrap().as_str());
                        let maybe_index = inner.next().unwrap();
                        let (opt_idx, oracle_inv) = if maybe_index.as_rule() == Rule::table_index {
                            let mut inner_index = maybe_index.into_inner();
                            let index = handle_expression(inner_index.next().unwrap());
                            (Some(index), inner.next().unwrap())
                        } else {
                            (None, maybe_index)
                        };

                        let mut inner = oracle_inv.into_inner();
                        let oracle_name = inner.next().unwrap().as_str();
                        let args = match inner.next() {
                            None => vec![],
                            Some(inner_args) => {
                                inner_args.into_inner().map(handle_expression).collect()
                            }
                        };

                        Statement::InvokeOracle {
                            id: ident,
                            opt_idx,
                            name: oracle_name.to_owned(),
                            args,
                            target_inst_name: None,
                        }
                    }
                    _ => {
                        unreachable!("{:#?}", stmt)
                    }
                }
            })
            .collect(),
    )
}

pub fn handle_oracle_def(oracle_def: Pair<Rule>) -> OracleDef {
    let mut inner = oracle_def.into_inner();
    let sig = handle_oracle_sig(inner.next().unwrap());
    let code = handle_code(inner.next().unwrap());

    OracleDef { sig, code }
}

pub fn handle_pkg_spec(pkg_spec: Pair<Rule>) -> Package {
    let mut oracles = vec![];
    let mut state = None;
    let mut params = None;
    let mut imported_oracles = HashMap::new();

    for spec in pkg_spec.into_inner() {
        match spec.as_rule() {
            Rule::state => {
                if let Some(inner_spec) = spec.into_inner().next() {
                    state = Some(handle_decl_list(inner_spec));
                }
            }
            Rule::params => {
                params = Some(handle_decl_list(spec.into_inner().next().unwrap()));
            }
            Rule::import_oracles => {
                for sig_ast in spec.into_inner() {
                    let sig = handle_oracle_sig(sig_ast);
                    imported_oracles.insert(sig.name.clone(), sig);
                }
            }
            Rule::oracle_def => {
                oracles.push(handle_oracle_def(spec));
            }
            _ => unreachable!("unhandled ast node in package: {}", spec),
        }
    }

    Package {
        oracles,
        params: params.unwrap_or_default(),
        imports: imported_oracles.iter().map(|(_k, v)| v.clone()).collect(),
        state: state.unwrap_or_default(),
    }
}

pub fn handle_pkg(pkg: Pair<Rule>) -> (String, Package) {
    let mut inner = pkg.into_inner();
    let name = inner.next().unwrap().as_str();
    let spec = inner.next().unwrap();
    let pkg = handle_pkg_spec(spec);

    (name.to_owned(), pkg)
}
