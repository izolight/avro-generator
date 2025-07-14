use std::collections::HashMap;

use apache_avro::Schema;
use serde_json::Value as JsonValue;

use crate::ir::{
    EnumDetails, FieldIr, FixedDetails, NamedType, RecordDetails, SchemaIr, SchemaKind, TypeIr,
    ValueIr,
};

pub struct Parser {
    // stores definition of all named types with fully qualified names
    definitions: HashMap<String, SchemaIr>,
    // queue for schemas that need to be parsed
    processing_queue: Vec<(Schema, String)>,
}

impl Parser {
    pub fn new(raw_schemas: &[Schema]) -> Self {
        let mut definitions = HashMap::new();
        let mut processing_queue = Vec::new();
        for schema in raw_schemas {
            if let Some(name) = schema.name() {
                let fqn = name.fullname(schema.namespace());
                let kind = match schema {
                    Schema::Record(_) => SchemaKind::Record,
                    Schema::Enum(_) => SchemaKind::Enum,
                    Schema::Fixed(_) => SchemaKind::Fixed,
                    _ => continue, // this should never happen
                };
                let placeholder = SchemaIr::Placeholder {
                    fqn: fqn.clone(),
                    kind,
                };
                definitions.insert(fqn, placeholder);
            }
            processing_queue.push((schema.clone(), schema.namespace().unwrap_or_default()));
        }

        Self {
            definitions,
            processing_queue,
        }
    }

    pub fn parse(mut self) -> Vec<SchemaIr> {
        // loop over queue until empty
        while let Some((schema, namespace)) = self.processing_queue.pop() {
            self.parse_and_define_schema(&schema, &namespace);
        }
        // sort the result deterministically by the fqn
        let mut result: Vec<SchemaIr> = self.definitions.into_values().collect();
        result.sort_by_key(|ir| ir.fqn().to_string());
        result
    }

    /// Parsed a named schema (`Record`, `Enum`, `Fixed`) and saves the definition in the internal
    /// map
    fn parse_and_define_schema(&mut self, schema: &Schema, context_namespace: &str) {
        let fqn = match schema.name() {
            Some(name) => name.fullname(Some(context_namespace.to_string())),
            None => return,
        };
        // check iff we already processed it, if it is not a placeholder, return
        if !matches!(
            self.definitions.get(&fqn),
            Some(SchemaIr::Placeholder { .. })
        ) {
            return;
        }
        let final_ir = match schema {
            Schema::Record(r) => self.build_record_ir(r, context_namespace),
            Schema::Enum(e) => self.build_enum_ir(e, context_namespace),
            Schema::Fixed(f) => self.build_fixed_ir(f, context_namespace),
            _ => return,
        };
        self.definitions.insert(fqn, final_ir);
    }

    fn build_record_ir(
        &mut self,
        record_schema: &apache_avro::schema::RecordSchema,
        context_namespace: &str,
    ) -> SchemaIr {
        let mut fields_ir = Vec::new();
        for field in &record_schema.fields {
            // recursively call `resolve_type` to get IR type for the field
            let type_ir = self.resolve_type(&field.schema, context_namespace);
            let default_ir = field
                .default
                .as_ref()
                .map(|json_val| self.resolve_default_value(json_val, &type_ir));
            fields_ir.push(FieldIr {
                name: field.name.clone(),
                doc: field.doc.clone(),
                ty: type_ir,
                default: default_ir,
            });
        }
        SchemaIr::Record(NamedType {
            name: record_schema
                .name
                .fullname(Some(context_namespace.to_string())),
            doc: record_schema.doc.clone(),
            inner: RecordDetails { fields: fields_ir },
        })
    }

    fn build_enum_ir(
        &mut self,
        enum_schema: &apache_avro::schema::EnumSchema,
        context_namespace: &str,
    ) -> SchemaIr {
        SchemaIr::Enum(NamedType {
            name: enum_schema
                .name
                .fullname(Some(context_namespace.to_string())),
            doc: enum_schema.doc.clone(),
            inner: EnumDetails {
                symbols: enum_schema.symbols.clone(),
            },
        })
    }

    fn build_fixed_ir(
        &mut self,
        fixed_schema: &apache_avro::schema::FixedSchema,
        context_namespace: &str,
    ) -> SchemaIr {
        SchemaIr::Fixed(NamedType {
            name: fixed_schema
                .name
                .fullname(Some(context_namespace.to_string())),
            doc: fixed_schema.doc.clone(),
            inner: FixedDetails {
                size: fixed_schema.size,
            },
        })
    }

    // Converts raw Avro schemaa into `TypeIr`
    fn resolve_type(&mut self, schema: &Schema, context_namespace: &str) -> TypeIr {
        match schema {
            Schema::Null => TypeIr::Null,
            Schema::Boolean => TypeIr::Boolean,
            Schema::Int => TypeIr::Int,
            Schema::Long => TypeIr::Long,
            Schema::Float => TypeIr::Float,
            Schema::Double => TypeIr::Double,
            Schema::Bytes => TypeIr::Bytes,
            Schema::String => TypeIr::String,
            Schema::Date => TypeIr::Date,
            Schema::TimeMillis => TypeIr::TimeMillis,
            Schema::TimeMicros => TypeIr::TimeMicros,
            Schema::TimestampMillis => TypeIr::TimestampMillis,
            Schema::TimestampMicros => TypeIr::TimestampMicros,
            Schema::TimestampNanos => TypeIr::TimestampNanos,
            Schema::LocalTimestampMillis => TypeIr::LocalTimestampMillis,
            Schema::LocalTimestampMicros => TypeIr::LocalTimestampMicros,
            Schema::LocalTimestampNanos => TypeIr::LocalTimestampNanos,
            Schema::Duration => TypeIr::Duration,
            Schema::Uuid => TypeIr::Uuid,
            Schema::Decimal(decimal_schema) => TypeIr::Decimal {
                precision: decimal_schema.precision,
                scale: decimal_schema.scale,
            },
            Schema::BigDecimal => TypeIr::BigDecimal,
            Schema::Array(array_schema) => {
                let inner_type = self.resolve_type(&array_schema.items, context_namespace);
                TypeIr::Array(Box::new(inner_type))
            }
            Schema::Map(map_schema) => {
                let inner_type = self.resolve_type(&map_schema.types, context_namespace);
                TypeIr::Map(Box::new(inner_type))
            }
            Schema::Union(union_schema) => {
                let variants: Vec<_> = union_schema
                    .variants()
                    .iter()
                    .map(|v| self.resolve_type(v, context_namespace))
                    .collect();
                if variants.len() == 2 && variants.iter().any(|v| matches!(v, TypeIr::Null)) {
                    let non_null_type = variants
                        .into_iter()
                        .find(|v| !matches!(v, TypeIr::Null))
                        .unwrap();
                    TypeIr::Option(Box::new(non_null_type))
                } else {
                    TypeIr::Union(variants)
                }
            }
            // For named types we just return its name, the parsing is done in the main loop later
            Schema::Record(record_schema) => {
                let fqn = record_schema
                    .name
                    .fullname(Some(context_namespace.to_string()));
                TypeIr::Record(fqn)
            }
            Schema::Enum(enum_schema) => {
                let fqn = enum_schema
                    .name
                    .fullname(Some(context_namespace.to_string()));
                TypeIr::Enum(fqn)
            }
            Schema::Fixed(fixed_schema) => {
                let fqn = fixed_schema
                    .name
                    .fullname(Some(context_namespace.to_string()));
                TypeIr::Fixed(fqn)
            }
            Schema::Ref { name } => {
                let fqn = name.fullname(Some(context_namespace.to_string()));
                // look uup definition, can either be a placeholder or already parsed
                match self.definitions.get(&fqn) {
                    Some(SchemaIr::Placeholder { kind, .. }) => match kind {
                        SchemaKind::Record => TypeIr::Record(fqn),
                        SchemaKind::Enum => TypeIr::Enum(fqn),
                        SchemaKind::Fixed => TypeIr::Fixed(fqn),
                    },
                    Some(SchemaIr::Record(_)) => TypeIr::Record(fqn),
                    Some(SchemaIr::Fixed(_)) => TypeIr::Record(fqn),
                    Some(SchemaIr::Enum(_)) => TypeIr::Fixed(fqn),
                    None => panic!("resolve_type found a reference to an unknown type {fqn}"),
                }
            }
        }
    }

    /// Converts a `serde_json::Value` representing a default value into our strongly-typed `ValueIr`, guided by the target `TypeIr`.
    fn resolve_default_value(&self, json_val: &JsonValue, target_type: &TypeIr) -> ValueIr {
        match target_type {
            TypeIr::Null => match json_val {
                JsonValue::Null => ValueIr::Null,
                _ => panic!("Invalid default for Null: {:?}", json_val),
            },

            TypeIr::Boolean => match json_val {
                JsonValue::Bool(b) => ValueIr::Boolean(*b),
                _ => panic!("Invalid default for Boolean: {:?}", json_val),
            },

            TypeIr::Int | TypeIr::Date | TypeIr::TimeMillis => match json_val {
                JsonValue::Number(n) => ValueIr::Int(n.as_i64().unwrap() as i32),
                _ => panic!("Invalid default for Int-based type: {:?}", json_val),
            },

            TypeIr::Long
            | TypeIr::TimeMicros
            | TypeIr::TimestampMillis
            | TypeIr::TimestampMicros
            | TypeIr::TimestampNanos
            | TypeIr::LocalTimestampMillis
            | TypeIr::LocalTimestampMicros
            | TypeIr::LocalTimestampNanos => match json_val {
                JsonValue::Number(n) => ValueIr::Long(n.as_i64().unwrap()),
                _ => panic!("Invalid default for Long-based type: {:?}", json_val),
            },

            TypeIr::Float => match json_val {
                JsonValue::Number(n) => ValueIr::Float(n.as_f64().unwrap() as f32),
                _ => panic!("Invalid default for Float: {:?}", json_val),
            },

            TypeIr::Double => match json_val {
                JsonValue::Number(n) => ValueIr::Double(n.as_f64().unwrap()),
                _ => panic!("Invalid default for Double: {:?}", json_val),
            },

            TypeIr::String | TypeIr::Uuid | TypeIr::BigDecimal => match json_val {
                JsonValue::String(s) => ValueIr::String(s.clone()),
                _ => panic!("Invalid default for String-based type: {:?}", json_val),
            },

            // Avro JSON spec encodes bytes/fixed defaults as strings.
            TypeIr::Decimal { precision: _, scale } => match json_val {
                serde_json::Value::String(s) => {
                    let unscaled_big_int = parse_decimal_string_to_unscaled_bigint(s, *scale);
                    ValueIr::Decimal(unscaled_big_int)
                }
                serde_json::Value::Array(bytes_array) => {
                    let bytes: Vec<u8> = bytes_array
                        .iter()
                        .map(|v| v.as_u64().expect("Byte array elements must be numbers") as u8)
                        .collect();
                    let unscaled_big_int = num_bigint::BigInt::from_signed_bytes_be(&bytes);
                    ValueIr::Decimal(unscaled_big_int)
                }
                _ => panic!(
                    "Invalid default value for Decimal: Expected string or byte array, got {:?}",
                    json_val
                ),
            },
            TypeIr::Bytes | TypeIr::Fixed(_) => match json_val {
                JsonValue::String(s) => ValueIr::Bytes(s.clone().into_bytes()),
                _ => panic!("Invalid default for Bytes/Fixed type: {:?}", json_val),
            },

            TypeIr::Duration => match json_val {
                JsonValue::String(s) if s.len() == 12 => {
                    let bytes: [u8; 12] = s.as_bytes().try_into().unwrap();
                    ValueIr::Duration(bytes)
                }
                _ => panic!("Invalid default for Duration type: {:?}", json_val),
            },

            TypeIr::Array(inner_type) => match json_val {
                JsonValue::Array(arr) => {
                    let values = arr
                        .iter()
                        .map(|item| self.resolve_default_value(item, inner_type))
                        .collect();
                    ValueIr::Array(values)
                }
                _ => panic!("Invalid default for Array type: {:?}", json_val),
            },

            TypeIr::Map(inner_type) => match json_val {
                JsonValue::Object(obj) => {
                    let values = obj
                        .iter()
                        .map(|(k, v)| (k.clone(), self.resolve_default_value(v, inner_type)))
                        .collect();
                    ValueIr::Map(values)
                }
                _ => panic!("Invalid default for Map type: {:?}", json_val),
            },

            TypeIr::Enum(_) => match json_val {
                JsonValue::String(s) => ValueIr::Enum(s.clone()),
                _ => panic!("Invalid default for Enum type: {:?}", json_val),
            },

            TypeIr::Record(fqn) => match json_val {
                JsonValue::Object(obj) => {
                    let mut record_defaults = HashMap::new();
                    // Look up the record definition to know its fields
                    let record_ir = self.definitions.get(fqn).unwrap();
                    if let SchemaIr::Record(NamedType {
                        inner: record_details,
                        ..
                    }) = record_ir
                    {
                        for field in &record_details.fields {
                            if let Some(field_json_val) = obj.get(&field.name) {
                                record_defaults.insert(
                                    field.name.clone(),
                                    self.resolve_default_value(field_json_val, &field.ty),
                                );
                            }
                        }
                    }
                    ValueIr::Record(record_defaults)
                }
                _ => panic!("Invalid default for Record type: {:?}", json_val),
            },

            // The default for a union is a default for the *first* type in the union.
            TypeIr::Union(variants) => {
                let first_variant_type = variants.first().unwrap();
                self.resolve_default_value(json_val, first_variant_type)
            }

            // The default for an option can only be null.
            TypeIr::Option(_) => match json_val {
                JsonValue::Null => ValueIr::Null,
                _ => panic!("Default for an Option must be null. Got: {:?}", json_val),
            },
        }
    }
}

fn parse_decimal_string_to_unscaled_bigint(s: &str, scale: usize) -> num_bigint::BigInt {
    let parts: Vec<&str> = s.split('.').collect();
    let integer_part = parts[0];
    let fractional_part = if parts.len() > 1 { parts[1] } else { "" };
    let mut unscaled_str = String::from(integer_part);
    unscaled_str.push_str(fractional_part);
    let current_factional_len = fractional_part.len();
    if current_factional_len < scale {
        for _ in 0..(scale - current_factional_len) {
            unscaled_str.push('0');
        }
    } else if current_factional_len > scale {
        panic!("Default decimal value has more fractional digits than specified scale");
    }
    num_bigint::BigInt::parse_bytes(unscaled_str.as_bytes(), 10)
        .expect("Failed to parse unscaled decimal strng to BigInt")
}

#[test]
fn test_default_value_for_array_off_strings() {
    let parser = Parser::new(&[]);
    let target_type = TypeIr::Array(Box::new(TypeIr::String));
    let json_input = serde_json::json!(["a", "b", "c"]);

    let expected_ir = ValueIr::Array(vec![
        ValueIr::String("a".to_string()),
        ValueIr::String("b".to_string()),
        ValueIr::String("c".to_string()),
    ]);
    let result_ir = parser.resolve_default_value(&json_input, &target_type);
    assert_eq!(result_ir, expected_ir);
}

#[test]
#[should_panic]
fn test_default_value_mismatch() {
    let parser = Parser::new(&[]);
    let target_type = TypeIr::Int;
    let json_input = serde_json::json!("not-an-int");
    parser.resolve_default_value(&json_input, &target_type);
}

#[test]
fn test_parser_on_all_schemas() {
    insta::glob!("test_schemas/*.avsc", |path| {
        let raw_schema_str = std::fs::read_to_string(path).unwrap();
        let json_value: serde_json::Value =
            serde_json::from_str(&raw_schema_str).expect("Failed to parse file as JSON");
        let schemas = match json_value {
            serde_json::Value::Array(arr) => {
                let schema_strs: Vec<String> = arr.iter().map(|v| v.to_string()).collect();
                apache_avro::Schema::parse_list(schema_strs.iter().map(|s| s.as_str()))
            }
            serde_json::Value::Object(_) => {
                apache_avro::Schema::parse_str(&raw_schema_str).map(|s| vec![s])
            }
            _ => panic!("Schema file is not a vallid JSON objecct or array"),
        }
        .unwrap();
        let parser = Parser::new(&schemas);
        let schema_ir = parser.parse();
        let ir_as_json = serde_json::to_string_pretty(&schema_ir).unwrap();
        insta::assert_snapshot!(ir_as_json);
    })
}
