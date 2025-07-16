mod generator;
mod ir;
mod parser;
mod errors;

use apache_avro::Schema;
use crate::parser::Parser;
use crate::generator::CodeGenerator;

fn main() {
    // Placeholder for actual schema loading
    let raw_schema_str = r#"{"type": "record", "name": "TestRecord", "fields": []}"#;
    let schemas = vec![Schema::parse_str(raw_schema_str).unwrap()];

    let parser = Parser::new(&schemas);
    let definitions = parser.definitions.clone();
    let ir_schemas = parser.parse().unwrap();

    let mut generator = CodeGenerator::new(definitions);
    let generated_code = generator.generate_all_schemas(&ir_schemas).unwrap();

    println!("{}", prettyplease::unparse(&syn::parse2(generated_code).unwrap()));
}
