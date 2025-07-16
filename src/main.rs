mod errors;
mod generator;
mod ir;
mod parser;

use std::fs;
use std::path::PathBuf;

use apache_avro::Schema;
use clap::Parser;

use crate::generator::CodeGenerator;
use crate::parser::Parser as AvroParser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the Avro schema file(s) or directory containing schema files.
    #[arg(short, long, value_name = "FILE_OR_DIR")]
    input: String,

    /// Output directory for the generated Rust code.
    #[arg(short, long, value_name = "DIR")]
    output: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let input_path = PathBuf::from(&args.input);
    let output_path = PathBuf::from(&args.output);

    if !output_path.exists() {
        fs::create_dir_all(&output_path)?;
    }

    let mut raw_schemas = Vec::new();

    if input_path.is_file() {
        let schema_str = fs::read_to_string(&input_path)?;
        let schema = Schema::parse_str(&schema_str)?;
        raw_schemas.push(schema);
    } else if input_path.is_dir() {
        for entry in fs::read_dir(&input_path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() && path.extension().is_some_and(|ext| ext == "avsc") {
                let schema_str = fs::read_to_string(&path)?;
                let schema = Schema::parse_str(&schema_str)?;
                raw_schemas.push(schema);
            }
        }
    } else {
        return Err(format!("Input path does not exist: {}", args.input).into());
    }

    let parser = AvroParser::new(&raw_schemas);
    let definitions = parser.definitions.clone();
    let ir_schemas = parser.parse()?;

    let mut generator = CodeGenerator::new(definitions);
    let generated_code = generator.generate_all_schemas(&ir_schemas)?;

    // For now, print to stdout. In a real scenario, write to files in the output directory.
    let parsed_code = syn::parse2(generated_code)
        .map_err(|e| format!("Failed to parse generated code: {}", e))?;
    println!("{}", prettyplease::unparse(&parsed_code));

    Ok(())
}

