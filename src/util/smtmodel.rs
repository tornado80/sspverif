use crate::debug_assert_matches;

use pest::Parser;
extern crate pest;

#[derive(Parser)]
#[grammar = "util/smtmodel.pest"]
struct SmtModelParser;

impl SmtModelParser {
    pub fn parse_model(content: &str) -> Vec<(String,String,String)> {
        let mut ast = SmtModelParser::parse(Rule::model, content).unwrap();
        let ast = ast.next().unwrap();
        debug_assert_matches!(ast.as_rule(), Rule::model);

        ast.into_inner().map(|line| {
            let mut inner = line.into_inner();
            let name = inner.next().unwrap();
            debug_assert_matches!(name.as_rule(), Rule::name);
            let tipe = inner.next().unwrap();
            debug_assert_matches!(tipe.as_rule(), Rule::tipe);
            let value = inner.next().unwrap();
            debug_assert_matches!(value.as_rule(), Rule::value);
            (String::from(name.as_str()), String::from(tipe.as_str()), String::from(value.as_str()))
        }).collect()
    }
}



#[derive(Debug, Clone)]
pub enum SmtModelEntry {
    IntegerEntry{ name: String, value: i64 }
}

#[derive(Debug, Clone)]
pub struct SmtModel {
    pub values: Vec<SmtModelEntry>
}

impl SmtModel {
    pub fn from_string(from: &str) -> Self{
        let parsed = SmtModelParser::parse_model(&from);
        let transformed = parsed.into_iter().map(|(name, tipe, value)| {
            match tipe.as_str() {
                "Int" => {SmtModelEntry::IntegerEntry{name, value: value.parse().unwrap()}}
                _ => unimplemented!()
            }
        }).collect();
        Self { values: transformed }
    }
}
