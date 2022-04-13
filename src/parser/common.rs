use crate::types::Type;

use super::Rule;

use pest::iterators::Pair;

pub fn handle_type(tipe: Pair<Rule>) -> Type {
    match tipe.as_rule() {
        Rule::type_integer => Type::Integer,
        Rule::type_maybe => Type::Maybe(Box::new(handle_type(tipe.into_inner().next().unwrap()))),
        Rule::type_bits => Type::Bits(tipe.into_inner().next().unwrap().as_str().to_string()),
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
