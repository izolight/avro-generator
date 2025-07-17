use std::collections::BTreeMap;

use apache_avro::Schema;
use serde_json::Value as JsonValue;

use crate::errors::ParserError;
use crate::ir::{
    EnumDetails, FieldIr, FixedDetails, NamedType, RecordDetails, SchemaIr, SchemaKind, TypeIr,
    ValueIr,
};

/// Parses Avro schemas into the Intermediate Representation (IR).
pub struct Parser {
    // stores definition of all named types with fully qualified names
    definitions: BTreeMap<String, SchemaIr>,
    // queue for schemas that need to be parsed
    processing_queue: Vec<(Schema, String)>,
}

impl Parser {
    /// Creates a new `Parser` instance and discovers all named schemas within the provided raw schemas.
    ///
    /// # Arguments
    ///
    /// * `raw_schemas` - A slice of `apache_avro::Schema` to parse.
    pub fn new(raw_schemas: &[Schema]) -> Self {
        let mut parser = Self {
            definitions: BTreeMap::new(),
            processing_queue: Vec::new(),
        };
        parser.discover_schemas(raw_schemas, None);
        parser
    }

    fn discover_schemas(&mut self, schemas: &[Schema], namespace: Option<String>) {
        for schema in schemas {
            // For named types, create a placeholder and add to queue
            if let Some(name) = schema.name() {
                let fqn = name.fullname(namespace.clone());
                if self.definitions.contains_key(&fqn) {
                    continue; // Already discovered
                }
                let kind = match schema {
                    Schema::Record(_) => SchemaKind::Record,
                    Schema::Enum(_) => SchemaKind::Enum,
                    Schema::Fixed(_) => SchemaKind::Fixed,
                    _ => continue,
                };
                let placeholder = SchemaIr::Placeholder {
                    fqn: fqn.clone(),
                    kind,
                };
                self.definitions.insert(fqn, placeholder);
                self.processing_queue
                    .push((schema.clone(), namespace.clone().unwrap_or_default()));
            }

            // Recursively discover in complex types
            match schema {
                Schema::Record(r) => {
                    let sub_namespace = r.name.namespace.clone().or(namespace.clone());
                    for field in &r.fields {
                        self.discover_schemas(&[field.schema.clone()], sub_namespace.clone());
                    }
                }
                Schema::Array(a) => {
                    self.discover_schemas(&[*a.items.clone()], namespace.clone());
                }
                Schema::Map(m) => {
                    self.discover_schemas(&[*m.types.clone()], namespace.clone());
                }
                Schema::Union(u) => {
                    self.discover_schemas(u.variants(), namespace.clone());
                }
                _ => {}
            }
        }
    }

    /// Parses the discovered schemas into their Intermediate Representation (IR).
    ///
    /// This method consumes the `Parser` instance.
    ///
    /// # Returns
    ///
    /// A `Result` containing a `Vec<SchemaIr>` of the parsed schemas, or a `ParserError` if parsing fails.
    pub fn parse(mut self) -> Result<BTreeMap<String, SchemaIr>, ParserError> {
        // loop over queue until empty
        while let Some((schema, namespace)) = self.processing_queue.pop() {
            self.parse_and_define_schema(&schema, &namespace)?;
        }
        Ok(self.definitions)
    }

    /// Parsed a named schema (`Record`, `Enum`, `Fixed`) and saves the definition in the internal
    /// map
    fn parse_and_define_schema(
        &mut self,
        schema: &Schema,
        context_namespace: &str,
    ) -> Result<(), ParserError> {
        let fqn = match schema.name() {
            Some(name) => name.fullname(Some(context_namespace.to_string())),
            None => return Ok(()),
        };
        // check if we already processed it, if it is not a placeholder, return
        if !matches!(
            self.definitions.get(&fqn),
            Some(SchemaIr::Placeholder { .. })
        ) {
            return Ok(());
        }
        let final_ir = match schema {
            Schema::Record(r) => self.build_record_ir(r, context_namespace)?,
            Schema::Enum(e) => self.build_enum_ir(e, context_namespace)?,
            Schema::Fixed(f) => self.build_fixed_ir(f, context_namespace)?,
            _ => return Ok(()),
        };
        self.definitions.insert(fqn, final_ir);
        Ok(())
    }

    fn build_record_ir(
        &mut self,
        record_schema: &apache_avro::schema::RecordSchema,
        context_namespace: &str,
    ) -> Result<SchemaIr, ParserError> {
        let mut fields_ir = Vec::new();
        for field in &record_schema.fields {
            // recursively call `resolve_type` to get IR type for the field
            let type_ir = self.resolve_type(&field.schema, context_namespace)?;
            let default_ir = if let Some(json_val) = &field.default {
                Some(self.resolve_default_value(json_val, &type_ir)?)
            } else {
                None
            };
            fields_ir.push(FieldIr {
                name: field.name.clone(),
                doc: field.doc.clone(),
                ty: type_ir,
                default: default_ir,
            });
        }
        Ok(SchemaIr::Record(NamedType {
            name: record_schema
                .name
                .fullname(Some(context_namespace.to_string())),
            doc: record_schema.doc.clone(),
            inner: RecordDetails { fields: fields_ir },
        }))
    }

    fn build_enum_ir(
        &mut self,
        enum_schema: &apache_avro::schema::EnumSchema,
        context_namespace: &str,
    ) -> Result<SchemaIr, ParserError> {
        Ok(SchemaIr::Enum(NamedType {
            name: enum_schema
                .name
                .fullname(Some(context_namespace.to_string())),
            doc: enum_schema.doc.clone(),
            inner: EnumDetails {
                symbols: enum_schema.symbols.clone(),
            },
        }))
    }

    fn build_fixed_ir(
        &mut self,
        fixed_schema: &apache_avro::schema::FixedSchema,
        context_namespace: &str,
    ) -> Result<SchemaIr, ParserError> {
        Ok(SchemaIr::Fixed(NamedType {
            name: fixed_schema
                .name
                .fullname(Some(context_namespace.to_string())),
            doc: fixed_schema.doc.clone(),
            inner: FixedDetails {
                size: fixed_schema.size,
            },
        }))
    }

    // Converts raw Avro schemaa into `TypeIr`
    fn resolve_type(
        &mut self,
        schema: &Schema,
        context_namespace: &str,
    ) -> Result<TypeIr, ParserError> {
        match schema {
            Schema::Null => Ok(TypeIr::Null),
            Schema::Boolean => Ok(TypeIr::Boolean),
            Schema::Int => Ok(TypeIr::Int),
            Schema::Long => Ok(TypeIr::Long),
            Schema::Float => Ok(TypeIr::Float),
            Schema::Double => Ok(TypeIr::Double),
            Schema::Bytes => Ok(TypeIr::Bytes),
            Schema::String => Ok(TypeIr::String),
            Schema::Date => Ok(TypeIr::Date),
            Schema::TimeMillis => Ok(TypeIr::TimeMillis),
            Schema::TimeMicros => Ok(TypeIr::TimeMicros),
            Schema::TimestampMillis => Ok(TypeIr::TimestampMillis),
            Schema::TimestampMicros => Ok(TypeIr::TimestampMicros),
            Schema::TimestampNanos => Ok(TypeIr::TimestampNanos),
            Schema::LocalTimestampMillis => Ok(TypeIr::LocalTimestampMillis),
            Schema::LocalTimestampMicros => Ok(TypeIr::LocalTimestampMicros),
            Schema::LocalTimestampNanos => Ok(TypeIr::LocalTimestampNanos),
            Schema::Duration => Ok(TypeIr::Duration),
            Schema::Uuid => Ok(TypeIr::Uuid),
            Schema::Decimal(decimal_schema) => Ok(TypeIr::Decimal {
                precision: decimal_schema.precision,
                scale: decimal_schema.scale,
            }),
            Schema::BigDecimal => Ok(TypeIr::BigDecimal),
            Schema::Array(array_schema) => {
                let inner_type = self.resolve_type(&array_schema.items, context_namespace)?;
                Ok(TypeIr::Array(Box::new(inner_type)))
            }
            Schema::Map(map_schema) => {
                let inner_type = self.resolve_type(&map_schema.types, context_namespace)?;
                Ok(TypeIr::Map(Box::new(inner_type)))
            }
            Schema::Union(union_schema) => {
                let variants: Result<Vec<_>, _> = union_schema
                    .variants()
                    .iter()
                    .map(|v| self.resolve_type(v, context_namespace))
                    .collect();
                let variants = variants?;
                if variants.len() == 2 && variants.iter().any(|v| matches!(v, TypeIr::Null)) {
                    let non_null_type = variants
                        .into_iter()
                        .find(|v| !matches!(v, TypeIr::Null))
                        .ok_or_else(|| ParserError::InvalidDefaultValue {
                        expected: "non-null type in union".to_string(),
                        found: "only null in union".to_string(),
                    })?;
                    Ok(TypeIr::Option(Box::new(non_null_type)))
                } else {
                    Ok(TypeIr::Union(variants))
                }
            }
            Schema::Record(record_schema) => {
                let fqn = record_schema
                    .name
                    .fullname(Some(context_namespace.to_string()));
                Ok(TypeIr::Record(fqn))
            }
            Schema::Enum(enum_schema) => {
                let fqn = enum_schema
                    .name
                    .fullname(Some(context_namespace.to_string()));
                Ok(TypeIr::Enum(fqn))
            }
            Schema::Fixed(fixed_schema) => {
                let fqn = fixed_schema
                    .name
                    .fullname(Some(context_namespace.to_string()));
                Ok(TypeIr::Fixed(fqn))
            }
            Schema::Ref { name } => {
                let fqn = name.fullname(Some(context_namespace.to_string()));
                // look up definition, can either be a placeholder or already parsed
                match self.definitions.get(&fqn) {
                    Some(SchemaIr::Placeholder { kind, .. }) => match kind {
                        SchemaKind::Record => Ok(TypeIr::Record(fqn.clone())),
                        SchemaKind::Enum => Ok(TypeIr::Enum(fqn.clone())),
                        SchemaKind::Fixed => Ok(TypeIr::Fixed(fqn.clone())),
                    },
                    Some(SchemaIr::Record(_)) => Ok(TypeIr::Record(fqn.clone())),
                    Some(SchemaIr::Fixed(_)) => Ok(TypeIr::Fixed(fqn.clone())),
                    Some(SchemaIr::Enum(_)) => Ok(TypeIr::Enum(fqn.clone())),
                    None => Err(ParserError::UnknownSchemaReference(fqn.clone())),
                }
            }
        }
    }

    /// Converts a `serde_json::Value` representing a default value into our strongly-typed `ValueIr`, guided by the target `TypeIr`.
    fn resolve_default_value(
        &self,
        json_val: &JsonValue,
        target_type: &TypeIr,
    ) -> Result<ValueIr, ParserError> {
        match target_type {
            TypeIr::Null => match json_val {
                JsonValue::Null => Ok(ValueIr::Null),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Null".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Boolean => match json_val {
                JsonValue::Bool(b) => Ok(ValueIr::Boolean(*b)),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Boolean".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Int | TypeIr::Date | TypeIr::TimeMillis => {
                match json_val {
                    JsonValue::Number(n) => Ok(ValueIr::Int(n.as_i64().ok_or_else(|| {
                        ParserError::InvalidDefaultValue {
                            expected: "Int-compatible number".to_string(),
                            found: format!("{:?}", n),
                        }
                    })? as i32)),
                    _ => Err(ParserError::InvalidDefaultValue {
                        expected: "Int-based type".to_string(),
                        found: format!("{:?}", json_val),
                    }),
                }
            }

            TypeIr::Long
            | TypeIr::TimeMicros
            | TypeIr::TimestampMillis
            | TypeIr::TimestampMicros
            | TypeIr::TimestampNanos
            | TypeIr::LocalTimestampMillis
            | TypeIr::LocalTimestampMicros
            | TypeIr::LocalTimestampNanos => match json_val {
                JsonValue::Number(n) => Ok(ValueIr::Long(n.as_i64().ok_or_else(|| {
                    ParserError::InvalidDefaultValue {
                        expected: "Long-compatible number".to_string(),
                        found: format!("{:?}", n),
                    }
                })?)),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Long-based type".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Float => match json_val {
                JsonValue::Number(n) => Ok(ValueIr::Float(n.as_f64().ok_or_else(|| {
                    ParserError::InvalidDefaultValue {
                        expected: "Float-compatible number".to_string(),
                        found: format!("{:?}", n),
                    }
                })? as f32)),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Float".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Double => match json_val {
                JsonValue::Number(n) => Ok(ValueIr::Double(n.as_f64().ok_or_else(|| {
                    ParserError::InvalidDefaultValue {
                        expected: "Double-compatible number".to_string(),
                        found: format!("{:?}", n),
                    }
                })?)),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Double".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::String | TypeIr::Uuid | TypeIr::BigDecimal => match json_val {
                JsonValue::String(s) => Ok(ValueIr::String(s.clone())),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "String-based type".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            // Avro JSON spec encodes bytes/fixed defaults as strings.
            TypeIr::Decimal {
                precision: _,
                scale,
            } => match json_val {
                serde_json::Value::String(s) => {
                    let unscaled_big_int = parse_decimal_string_to_unscaled_bigint(s, *scale)?;
                    Ok(ValueIr::Decimal(unscaled_big_int))
                }
                serde_json::Value::Array(bytes_array) => {
                    let bytes: Result<Vec<u8>, ParserError> = bytes_array
                        .iter()
                        .map(|v| {
                            v.as_u64().map(|val| val as u8).ok_or_else(|| {
                                ParserError::InvalidDefaultValue {
                                    expected: "Byte array elements to be numbers".to_string(),
                                    found: format!("{:?}", v),
                                }
                            })
                        })
                        .collect();
                    let unscaled_big_int = num_bigint::BigInt::from_signed_bytes_be(&bytes?);
                    Ok(ValueIr::Decimal(unscaled_big_int))
                }
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "string or byte array for Decimal".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },
            TypeIr::Bytes | TypeIr::Fixed(_) => match json_val {
                JsonValue::String(s) => Ok(ValueIr::Bytes(s.clone().into_bytes())),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Bytes/Fixed type".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Duration => match json_val {
                JsonValue::String(s) if s.len() == 12 => {
                    let bytes: [u8; 12] = s
                        .as_bytes()
                        .try_into()
                        .map_err(|_| ParserError::InvalidDurationString(s.clone()))?;
                    Ok(ValueIr::Duration(bytes))
                }
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Duration type (12-char string)".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Array(inner_type) => match json_val {
                JsonValue::Array(arr) => {
                    let values: Result<Vec<_>, ParserError> = arr
                        .iter()
                        .map(|item| self.resolve_default_value(item, inner_type))
                        .collect();
                    Ok(ValueIr::Array(values?))
                }
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Array type".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Map(inner_type) => match json_val {
                JsonValue::Object(obj) => {
                    let values: Result<std::collections::BTreeMap<String, ValueIr>, ParserError> =
                        obj.iter()
                            .map(|(k, v)| {
                                Ok((k.clone(), self.resolve_default_value(v, inner_type)?))
                            })
                            .collect();
                    Ok(ValueIr::Map(values?))
                }
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Map type".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Enum(_) => match json_val {
                JsonValue::String(s) => Ok(ValueIr::Enum(s.clone())),
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Enum type".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            TypeIr::Record(fqn) => match json_val {
                JsonValue::Object(obj) => {
                    let mut record_defaults = BTreeMap::new();
                    // Look up the record definition to know its fields
                    let record_ir = self
                        .definitions
                        .get(fqn)
                        .ok_or_else(|| ParserError::UnknownSchemaReference(fqn.clone()))?;
                    if let SchemaIr::Record(NamedType {
                        inner: record_details,
                        ..
                    }) = record_ir
                    {
                        for field in &record_details.fields {
                            if let Some(field_json_val) = obj.get(&field.name) {
                                record_defaults.insert(
                                    field.name.clone(),
                                    self.resolve_default_value(field_json_val, &field.ty)?,
                                );
                            }
                        }
                    }
                    Ok(ValueIr::Record(record_defaults))
                }
                _ => Err(ParserError::InvalidDefaultValue {
                    expected: "Record type".to_string(),
                    found: format!("{:?}", json_val),
                }),
            },

            // The default for a union is a default for the *first* type in the union.
            TypeIr::Union(variants) => {
                let first_variant_type =
                    variants
                        .first()
                        .ok_or_else(|| ParserError::InvalidDefaultValue {
                            expected: "non-empty union".to_string(),
                            found: "empty union".to_string(),
                        })?;
                self.resolve_default_value(json_val, first_variant_type)
            }

            // The default for an option can only be null.
            TypeIr::Option(inner_type) => match json_val {
                JsonValue::Null => Ok(ValueIr::Null),
                _ => self.resolve_default_value(json_val, inner_type),
            },
        }
    }
}

/// Parses a decimal string into an unscaled BigInt, considering the given scale.
///
/// # Arguments
///
/// * `s` - The string representation of the decimal number.
/// * `scale` - The scale of the decimal number.
///
/// # Returns
///
/// A `Result` containing the `num_bigint::BigInt` or a `ParserError` if parsing fails or scale mismatches.
fn parse_decimal_string_to_unscaled_bigint(
    s: &str,
    scale: usize,
) -> Result<num_bigint::BigInt, ParserError> {
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
        return Err(ParserError::DecimalScaleMismatch);
    }
    num_bigint::BigInt::parse_bytes(unscaled_str.as_bytes(), 10)
        .ok_or_else(|| ParserError::BigIntParseError(s.to_string()))
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
    let result_ir = parser
        .resolve_default_value(&json_input, &target_type)
        .expect("Failed to resolve default value");
    assert_eq!(result_ir, expected_ir);
}

#[test]
fn test_default_value_mismatch() {
    let parser = Parser::new(&[]);
    let target_type = TypeIr::Int;
    let json_input = serde_json::json!("not-an-int");
    let result = parser.resolve_default_value(&json_input, &target_type);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ParserError::InvalidDefaultValue { .. }
    ));
}

#[test]
fn test_parser_on_all_schemas() {
    insta::glob!("test_schemas/*.avsc", |path| {
        let raw_schema_str = std::fs::read_to_string(path).expect("Failed to read schema file");
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
        .expect("Failed to parse Avro schema");
        let parser = Parser::new(&schemas);
        let schema_ir = parser.parse().expect("Failed to parse schema IR");
        let ir_as_json =
            serde_json::to_string_pretty(&schema_ir).expect("Failed to serialize IR to JSON");
        insta::assert_snapshot!(ir_as_json);
    })
}
