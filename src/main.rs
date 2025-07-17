mod errors;
mod generator;
mod ir;
mod parser;

use std::fs;
use std::path::{Path, PathBuf};

use apache_avro::Schema;
use clap::Parser;

use crate::generator::CodeGenerator;
use crate::parser::Parser as AvroParser;

/// Command-line arguments for the Avro code generator.
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

/// Main function for the Avro code generator CLI.
///
/// Parses command-line arguments, reads Avro schema files, converts them into
/// an Intermediate Representation (IR), generates Rust code from the IR,
/// and prints the generated code to standard output.
///
/// # Returns
///
/// A `Result` indicating success or an error if any step fails.
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
        find_avro_schemas_recursive(&input_path, &mut raw_schemas)?;
    } else {
        return Err(format!("Input path does not exist: {}", args.input).into());
    }

    // Helper function to recursively find Avro schemas
fn find_avro_schemas_recursive(
    path: &Path,
    raw_schemas: &mut Vec<Schema>,
) -> Result<(), Box<dyn std::error::Error>> {
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_file() && path.extension().is_some_and(|ext| ext == "avsc") {
            let schema_str = fs::read_to_string(&path)?;
            let schema = Schema::parse_str(&schema_str)?;
            raw_schemas.push(schema);
        } else if path.is_dir() {
            find_avro_schemas_recursive(&path, raw_schemas)?;
        }
    }
    Ok(())
}

    let parser = AvroParser::new(&raw_schemas);
    let definitions = parser.parse()?;

    let mut generator = CodeGenerator::new(definitions.clone());
    let generated_code = generator.generate_all_schemas()?;

    // For now, print to stdout. In a real scenario, write to files in the output directory.
    let parsed_code = syn::parse2(generated_code)
        .map_err(|e| format!("Failed to parse generated code: {}", e))?;
    println!("{}", prettyplease::unparse(&parsed_code));

    Ok(())
}
