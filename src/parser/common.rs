use crate::types::Type;

use super::Rule;

use pest::iterators::Pair;

pub fn handle_type(tipe: Pair<Rule>) -> Type {
    match tipe.as_rule() {
        Rule::type_empty => Type::Empty,
        Rule::type_integer => Type::Integer,
        Rule::type_bool => Type::Boolean,
        Rule::type_string => Type::String,
        Rule::type_maybe => Type::Maybe(Box::new(handle_type(tipe.into_inner().next().unwrap()))),
        Rule::type_bits => Type::Bits(tipe.into_inner().next().unwrap().as_str().to_string()),
        Rule::type_tuple => Type::Tuple(tipe.into_inner().map(handle_type).collect()),
        Rule::type_table => {
            let mut inner = tipe.into_inner();
            let indextype = handle_type(inner.next().unwrap());
            let valuetype = handle_type(inner.next().unwrap());
            Type::Table(Box::new(indextype), Box::new(valuetype))
        }
        Rule::type_fn => {
            let mut inner = tipe.into_inner();
            let argtipes = inner
                .next()
                .unwrap()
                .into_inner()
                .map(|spec| handle_type(spec.into_inner().next().unwrap()))
                .collect();
            let tipe = handle_type(inner.next().unwrap());
            Type::Fn(argtipes, Box::new(tipe))
        }
        _ => {
            unreachable!("{:#?}", tipe)
        }
    }
}
