pub mod writer;

#[derive(Parser)]
#[grammar = "writers/tex/smtmodel.pest"]
pub struct SmtModelParser;
