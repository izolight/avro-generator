# Avro Rust Code Generator

`avro-rust-codegen` is a command-line tool written in Rust that generates idiomatic Rust code from Apache Avro schemas. It aims to provide a robust and type-safe way to work with Avro data in Rust applications.

## Features

- **Schema Parsing:** Parses single Avro schema files (`.avsc`) or directories containing multiple schema files.
- **Intermediate Representation (IR):** Converts Avro schemas into a well-defined Intermediate Representation for easier processing.
- **Rust Code Generation:** Generates Rust structs, enums, and type aliases corresponding to Avro records, enums, and fixed types.
- **Type Mapping:** Maps Avro primitive and logical types (e.g., `string`, `int`, `long`, `date`, `uuid`, `decimal`) to appropriate Rust types (e.g., `String`, `i32`, `i64`, `chrono::NaiveDate`, `uuid::Uuid`, `rust_decimal::Decimal`).
- **Complex Type Handling:** Supports generation for Avro arrays, maps, options (nullable types), and unions.
- **Default Values:** Incorporates default values defined in Avro schemas into the generated Rust code.
- **Namespaces:** Handles Avro namespaces by generating Rust modules.

## Installation

```bash
cargo build --release
# The executable will be located at target/release/avro-rust-codegen
# You can also install it directly to your Cargo bin directory:
cargo install --path .
```

## Usage

The `avro-rust-codegen` CLI tool takes an input path (file or directory) and an output directory.

```bash
avro-rust-codegen -i <INPUT_PATH> -o <OUTPUT_DIR>
```

**Arguments:**

- `-i`, `--input <FILE_OR_DIR>`: Path to the Avro schema file(s) or a directory containing schema files (`.avsc`).
- `-o`, `--output <DIR>`: Output directory where the generated Rust code will be saved.

**Examples:**

1. **Generate code from a single schema file:**

   ```bash
   avro-rust-codegen -i schemas/user.avsc -o src/generated
   ```

2. **Generate code from all schema files in a directory:**

   ```bash
   avro-rust-codegen -i schemas/ -o src/generated
   ```
