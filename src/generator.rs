use std::collections::{BTreeMap, HashMap};

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, Type, parse_quote};

use thiserror::Error;

use crate::ir::{EnumIr, FixedIr, RecordIr, SchemaIr, TypeIr, ValueIr};

#[derive(Error, Debug)]
pub enum GeneratorError {
    #[error("Placeholder schema found during code generation: {0}")]
    PlaceholderFound(String),
    #[error("Mismatched type for default value. Expected {expected}, got {found}")]
    MismatchedDefaultType { expected: String, found: String },
    #[error("Decimal default value requires Decimal TypeIr")]
    DecimalDefaultValueMismatch,
    #[error("Failed to parse generated code: {0}")]
    SynError(#[from] syn::Error),
    #[error("Got multiple errors: {0:?}")]
    MultipleError(Vec<GeneratorError>),
}

pub struct CodeGenerator {
    generated_union_enums: HashMap<String, TokenStream>,
}

impl CodeGenerator {
    pub fn new() -> Self {
        CodeGenerator {
            generated_union_enums: HashMap::new(),
        }
    }

    /// Generates a TokenStream for a single SchemaIr
    pub fn generate_schema(&mut self, schema_ir: &SchemaIr) -> Result<TokenStream, GeneratorError> {
        match schema_ir {
            SchemaIr::Record(record_ir) => self.generate_record(record_ir),
            SchemaIr::Enum(enum_ir) => self.generate_enum(enum_ir),
            SchemaIr::Fixed(fixed_ir) => self.generate_fixed(fixed_ir),
            SchemaIr::Placeholder { fqn, .. } => Err(GeneratorError::PlaceholderFound(fqn.clone())),
        }
    }

    /// Generates a TokenStream for all schemas, typically wrapped in modules
    pub fn generate_all_schemas(
        &mut self,
        schemas: &[SchemaIr],
    ) -> Result<TokenStream, GeneratorError> {
        let mut root = ModuleNode::new(None);
        let mut errors = vec![];

        for schema_ir in schemas {
            let fqn = schema_ir.fqn();
            let parts: Vec<&str> = fqn.split('.').collect();

            if parts.len() > 1 {
                let (namespace_parts, _name) = parts.split_at(parts.len() - 1);
                root.add_schema(namespace_parts, schema_ir, self)?;
            } else {
                // It's in the global namespace
                let code = self.generate_schema(schema_ir).map_err(|e| errors.push(e));
                if let Some(c) = code.ok() {
                    root.code.extend(c);
                }
            }
        }

        if !errors.is_empty() {
            return Err(GeneratorError::MultipleError(errors));
        }

        Ok(root.to_token_stream())
    }

    fn avro_fqn_to_rust_path(&self, fqn: &str) -> Type {
        let parts: Vec<Ident> = fqn.split('.').map(|s| format_ident!("{}", s)).collect();
        parse_quote! { #(#parts)::* }
    }

    fn avro_fqn_to_rust_name(&self, fqn: &str) -> Result<Ident, GeneratorError> {
        let parts: Vec<&str> = fqn.split('.').collect();
        parts.last().map(|s| format_ident!("{}", s)).ok_or_else(|| {
            GeneratorError::MismatchedDefaultType {
                expected: "non-empty FQN".to_string(),
                found: fqn.to_string(),
            }
        })
    }

    fn map_type_ir_to_rust_type(
        &mut self,
        ty_ir: &TypeIr,
    ) -> Result<(Type, Option<TokenStream>), GeneratorError> {
        match ty_ir {
            TypeIr::Null => Ok((parse_quote! { () }, None)),
            TypeIr::Boolean => Ok((parse_quote! { bool }, None)),
            TypeIr::Int => Ok((parse_quote! { i32 }, None)),
            TypeIr::Long => Ok((parse_quote! { i64 }, None)),
            TypeIr::Float => Ok((parse_quote! { f32 }, None)),
            TypeIr::Double => Ok((parse_quote! { f64 }, None)),
            TypeIr::Bytes => Ok((parse_quote! { Vec<u8> }, None)),
            TypeIr::String => Ok((parse_quote! { String }, None)),
            TypeIr::Date => Ok((parse_quote! { chrono::NaiveDate }, None)),
            TypeIr::TimeMillis => Ok((parse_quote! { chrono::Duration }, None)),
            TypeIr::TimeMicros => Ok((parse_quote! { chrono::Duration }, None)),
            TypeIr::TimestampMillis => Ok((parse_quote! { chrono::DateTime<chrono::Utc> }, None)),
            TypeIr::TimestampMicros => Ok((parse_quote! { chrono::DateTime<chrono::Utc> }, None)),
            TypeIr::TimestampNanos => Ok((parse_quote! { chrono::DateTime<chrono::Utc> }, None)),
            TypeIr::LocalTimestampMillis => Ok((parse_quote! { chrono::NaiveDateTime }, None)),
            TypeIr::LocalTimestampMicros => Ok((parse_quote! { chrono::NaiveDateTime }, None)),
            TypeIr::LocalTimestampNanos => Ok((parse_quote! { chrono::NaiveDateTime }, None)),
            TypeIr::Duration => Ok((parse_quote! { apache_avro::Duration }, None)),
            TypeIr::Uuid => Ok((parse_quote! { uuid::Uuid }, None)),
            TypeIr::Decimal { .. } => Ok((parse_quote! { rust_decimal::Decimal }, None)),
            TypeIr::BigDecimal => Ok((parse_quote! { bigdecimal::BigDecimal }, None)),
            TypeIr::Array(inner) => {
                let (inner_type, gen_union) = self.map_type_ir_to_rust_type(inner)?;
                Ok((parse_quote! { Vec<#inner_type> }, gen_union))
            }
            TypeIr::Map(inner) => {
                let (inner_type, gen_union) = self.map_type_ir_to_rust_type(inner)?;
                Ok((
                    parse_quote! { std::collections::HashMap<String, #inner_type> },
                    gen_union,
                ))
            }
            TypeIr::Option(inner) => {
                let (inner_type, gen_union) = self.map_type_ir_to_rust_type(inner)?;
                Ok((parse_quote! { Option<#inner_type> }, gen_union))
            }
            TypeIr::Union(variants) => {
                let (union_enum_name, enum_tokens) = self.generate_union_enum(variants)?;
                Ok((parse_quote! { #union_enum_name }, Some(enum_tokens)))
            }
            TypeIr::Record(fqn) => Ok((self.avro_fqn_to_rust_path(fqn), None)),
            TypeIr::Enum(fqn) => Ok((self.avro_fqn_to_rust_path(fqn), None)),
            TypeIr::Fixed(fqn) => Ok((self.avro_fqn_to_rust_path(fqn), None)),
        }
    }

    // Generates a Rust expression for a default value
    fn generate_default_value_expr(
        &mut self,
        value_ir: &ValueIr,
        target_type: &TypeIr,
    ) -> Result<TokenStream, GeneratorError> {
        match value_ir {
            ValueIr::Null => Ok(quote! { None }),
            ValueIr::Boolean(b) => Ok(quote! { #b }),
            ValueIr::Int(i) => Ok(quote! { #i }),
            ValueIr::Long(l) => Ok(quote! { #l }),
            ValueIr::Float(f) => Ok(quote! { #f }),
            ValueIr::Double(d) => Ok(quote! { #d }),
            ValueIr::Bytes(b) => Ok(quote! { vec![#(#b),*] }),
            ValueIr::String(s) => Ok(quote! { #s.to_string() }),
            ValueIr::Date(d) => Ok(
                quote! { chrono::NaiveDateTime::from_ymd_opt(1970, 1, 1)?.checked_add_days(chrono::Days::new(#d as u32))? },
            ),
            ValueIr::TimeMillis(t) => Ok(quote! { chrono::Duration::millisecnds(#t as i64) }),
            ValueIr::TimeMicros(t) => Ok(quote! { chrono::Duration::microseconds(#t) }),
            ValueIr::TimestampMillis(t) => {
                Ok(quote! { chrono::DateTime::<chrono::Utc>::from_timestamp_millis(#t)? })
            }
            ValueIr::TimestampMicros(t) => {
                Ok(quote! { chrono::DateTime::<chrono::Utc>::from_timestamp_micros(#t)? })
            }
            ValueIr::TimestampNanos(t) => {
                Ok(quote! { chrono::DateTime::<chrono::Utc>::from_timestamp_nanos(#t)? })
            }
            ValueIr::LocalTimestampMillis(t) => {
                Ok(quote! { chrono::NaiveDateTime::from_timestamp_millis(#t)? })
            }
            ValueIr::LocalTimestampMicros(t) => {
                Ok(quote! { chrono::NaiveDateTime::from_timestamp_micros(#t)? })
            }
            ValueIr::LocalTimestampNanos(t) => {
                Ok(quote! { chrono::NaiveDateTime::from_timestamp_nanos(#t)? })
            }
            ValueIr::Duration(d) => Ok(quote! { apache_avro::Duration::new([#(#d),*]) }),
            ValueIr::Uuid(s) => Ok(quote! { uuid::Uuid::parse_str(#s)? }),
            ValueIr::Decimal(big_int) => {
                if let TypeIr::Decimal {
                    precision: _,
                    scale,
                } = target_type
                {
                    let s_str = big_int.to_string();
                    Ok(
                        quote! { rust_decimal::Decimal::from_str(#s_str)?.with_scale(#scale as u32) },
                    )
                } else {
                    Err(GeneratorError::DecimalDefaultValueMismatch)
                }
            }
            ValueIr::BigDecimal(s) => Ok(quote! { bigdecimal::BigDecimal::from_str(#s)? }),
            ValueIr::Array(arr) => {
                let inner_type = if let TypeIr::Array(inner) = target_type {
                    inner
                } else {
                    return Err(GeneratorError::MismatchedDefaultType {
                        expected: "Array".to_string(),
                        found: format!("{:?}", target_type),
                    });
                };
                let elements = arr
                    .iter()
                    .map(|v| self.generate_default_value_expr(v, inner_type))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(quote! { vec![#(#elements),*] })
            }
            ValueIr::Map(map) => {
                let inner_type = if let TypeIr::Map(inner) = target_type {
                    inner
                } else {
                    return Err(GeneratorError::MismatchedDefaultType {
                        expected: "Map".to_string(),
                        found: format!("{:?}", target_type),
                    });
                };
                let entries = map
                    .iter()
                    .map(|(k, v)| {
                        self.generate_default_value_expr(v, inner_type)
                            .map(|val_expr| {
                                quote! { m.insert(#k.to_string(), #val_expr); }
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(quote! {
                    {
                        let mut m = std::collections::HashMap::new();
                        #(#entries)*
                        m
                    }
                })
            }
            ValueIr::Enum(s) => {
                let enum_path = if let TypeIr::Enum(fqn) = target_type {
                    self.avro_fqn_to_rust_path(fqn)
                } else {
                    return Err(GeneratorError::MismatchedDefaultType {
                        expected: "Enum".to_string(),
                        found: format!("{:?}", target_type),
                    });
                };
                let variant_name = format_ident!("{}", s);
                Ok(quote! { #enum_path::#variant_name })
            }
            ValueIr::Fixed(b) => Ok(quote! { [#(#b),*] }),
            ValueIr::Record(map) => {
                let record_path = if let TypeIr::Record(fqn) = target_type {
                    self.avro_fqn_to_rust_path(fqn)
                } else {
                    return Err(GeneratorError::MismatchedDefaultType {
                        expected: "Record".to_string(),
                        found: format!("{:?}", target_type),
                    });
                };
                let fields = map
                    .iter()
                    .map(|(k, v)| {
                        self.generate_default_value_expr(v, &TypeIr::Null)
                            .map(|val_expr| {
                                let field_name = format_ident!("{}", k);
                                quote! { #field_name: #val_expr }
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(quote! { #record_path { #(#fields),* } })
            }
        }
    }

    /// Helper to convert a fully qualified Avro name to a Rust struct/enum name.
    /// e.g., "com.example.MyRecord" -> `MyRecord`
    fn generate_record(&mut self, record_ir: &RecordIr) -> Result<TokenStream, GeneratorError> {
        let struct_name = self.avro_fqn_to_rust_name(&record_ir.name)?;
        let doc = &record_ir.doc.as_ref().map(|d| quote! { #[doc = #d] });

        let mut field_tokens = Vec::new();
        let mut union_tokens = TokenStream::new();

        for field in &record_ir.inner.fields {
            let field_name = format_ident!("{}", field.name);
            let fn_name = format_ident!("default_{}", field.name);

            let (field_type, generated_union) = self.map_type_ir_to_rust_type(&field.ty)?;
            if let Some(union_code) = generated_union {
                union_tokens.extend(union_code);
            }

            let field_doc = &field.doc.as_ref().map(|d| quote! { #[doc = #d] });

            let default_attr = if field.default.is_some() {
                quote! { #[serde(default = #fn_name)] }
            } else {
                quote! {}
            };

            field_tokens.push(quote! {
                #field_doc
                #default_attr
                pub #field_name: #field_type
            });
        }

        let mut default_fns = Vec::new();
        for field in &record_ir.inner.fields {
            if let Some(default_val_ir) = &field.default {
                let fn_name = format_ident!("default_{}", field.name);
                let (field_type, _) = self.map_type_ir_to_rust_type(&field.ty)?;
                let default_expr = self.generate_default_value_expr(default_val_ir, &field.ty)?;
                default_fns.push(quote! {
                    fn #fn_name() -> #field_type {
                        #default_expr
                    }
                });
            }
        }

        Ok(quote! {
            #doc
            #[derive(Debug, PartialEq, Clone, serde::Serialize, serde::Deserialize)]
            pub struct #struct_name {
                #(#field_tokens),*
            }

            #(#default_fns)*

            #union_tokens
        })
    }

    fn generate_enum(&self, enum_ir: &EnumIr) -> Result<TokenStream, GeneratorError> {
        let enum_name = self.avro_fqn_to_rust_name(&enum_ir.name)?;
        let doc = &enum_ir.doc.as_ref().map(|d| quote! { #[doc = #d] });
        let variants = enum_ir.inner.symbols.iter().map(|symbol| {
            let variant_name = format_ident!("{}", symbol);
            quote! { #variant_name }
        });

        Ok(quote! {
            #doc
            #[derive(Debug, PartialEq, Eq, Clone, serde::Serialize, serde::Deserialize)]
            pub enum #enum_name {
                #(#variants),*
            }
        })
    }

    fn generate_fixed(&self, fixed_ir: &FixedIr) -> Result<TokenStream, GeneratorError> {
        let type_name = self.avro_fqn_to_rust_name(&fixed_ir.name)?;
        let doc = &fixed_ir.doc.as_ref().map(|d| quote! { #[doc = #d] });
        let size = fixed_ir.inner.size;

        Ok(quote! {
            #doc
            pub type #type_name = [u8; #size];
        })
    }

    /// Generate a rust enum for a complex avro union
    fn generate_union_enum(
        &mut self,
        union_ir_variants: &[TypeIr],
    ) -> Result<(Ident, TokenStream), GeneratorError> {
        // determine stable name
        let sorted_rust_types = union_ir_variants
            .iter()
            .map(|ty_ir| self.map_type_ir_to_rust_type(ty_ir).map(|(t, _)| t))
            .collect::<Result<Vec<_>, _>>()?;
        let mut sorted_rust_types: Vec<String> = sorted_rust_types
            .iter()
            .map(|t| quote!(#t).to_string())
            .collect();
        // quote!(#rust_type).to_string()
        sorted_rust_types.sort();

        let union_enum_name_str = format!("Union{}", sorted_rust_types.join(""));
        let union_enum_name = format_ident!("{}", union_enum_name_str);
        // check if this enum has already been generated
        if let Some(existing_tokens) = self.generated_union_enums.get(&union_enum_name_str) {
            return Ok((union_enum_name, existing_tokens.clone()));
        }

        let mut variants_data = Vec::new();
        for (index, ty_ir) in union_ir_variants.iter().enumerate() {
            let (rust_type, _) = self.map_type_ir_to_rust_type(ty_ir)?;
            let variant_ident = match ty_ir {
                TypeIr::String => format_ident!("String"),
                TypeIr::Long => format_ident!("Long"),
                TypeIr::Int => format_ident!("Int"),
                TypeIr::Boolean => format_ident!("Boolean"),
                TypeIr::Float => format_ident!("Float"),
                TypeIr::Double => format_ident!("Double"),
                TypeIr::Bytes => format_ident!("Bytes"),
                TypeIr::Null => format_ident!("Null"), // Should not be in complex unions, but for completeness
                TypeIr::Date => format_ident!("Date"),
                TypeIr::TimeMillis => format_ident!("TimeMillis"),
                TypeIr::TimeMicros => format_ident!("TimeMicros"),
                TypeIr::TimestampMillis => format_ident!("TimestampMillis"),
                TypeIr::TimestampMicros => format_ident!("TimestampMicros"),
                TypeIr::TimestampNanos => format_ident!("TimestampNanos"),
                TypeIr::LocalTimestampMillis => format_ident!("LocalTimestampMillis"),
                TypeIr::LocalTimestampMicros => format_ident!("LocalTimestampMicros"),
                TypeIr::LocalTimestampNanos => format_ident!("LocalTimestampNanos"),
                TypeIr::Duration => format_ident!("Duration"),
                TypeIr::Uuid => format_ident!("Uuid"),
                TypeIr::Decimal { .. } => format_ident!("Decimal"),
                TypeIr::BigDecimal => format_ident!("BigDecimal"),
                TypeIr::Array(_) => format_ident!("Array"), // Could be more specific, e.g., ArrayString
                TypeIr::Map(_) => format_ident!("Map"),     // Could be more specific
                TypeIr::Option(_) => format_ident!("Option"), // Should not be in complex unions
                TypeIr::Union(_) => format_ident!("NestedUnion"), // Should not be in complex unions
                TypeIr::Record(fqn) => self.avro_fqn_to_rust_name(fqn)?,
                TypeIr::Enum(fqn) => self.avro_fqn_to_rust_name(fqn)?,
                TypeIr::Fixed(fqn) => self.avro_fqn_to_rust_name(fqn)?,
            };

            let serde_vistor_method = match ty_ir {
                TypeIr::Boolean => Some(format_ident!("visit_bool")),
                TypeIr::Int => Some(format_ident!("visit_i32")),
                TypeIr::Long => Some(format_ident!("visit_i64")),
                TypeIr::Float => Some(format_ident!("visit_f32")),
                TypeIr::Double => Some(format_ident!("visit_f64")),
                TypeIr::String => Some(format_ident!("visit_str")),
                TypeIr::Bytes => Some(format_ident!("visit_bytes")),
                _ => None,
            };
            variants_data.push((index as u32, variant_ident, rust_type, serde_vistor_method));
        }
        let enum_variants = variants_data
            .iter()
            .map(|(_, variant_ident, rust_type, _)| {
                quote! { #variant_ident(#rust_type) }
            });

        let from_impls = variants_data
            .iter()
            .map(|(_, variant_ident, rust_type, _)| {
                quote! {
                    impl From<#rust_type> for #union_enum_name {
                        fn from(v: #rust_type) -> Self {
                            Self::#variant_ident(v)
                        }
                    }
                }
            });

        let try_from_impls = variants_data
            .iter()
            .map(|(_, variant_ident, rust_type, _)| {
                if union_ir_variants.len() == 1 {
                    quote! {
                        impl From<#union_enum_name> for #rust_type {
                            fn from(v: #union_enum_name) -> Self {
                                let #union_enum_name::#variant_ident(v) = v;
                                v
                            }
                        }
                    }
                } else {
                    quote! {
                        impl TryFrom<#union_enum_name> for #rust_type {
                            type Error = #union_enum_name;

                            fn try_from(v: #union_enum_name) -> Result<Self, Self::Error> {
                                if let #union_enum_name::#variant_ident(v) = v {
                                    Ok(v)
                                } else {
                                    Err(v)
                                }
                            }
                        }
                    }
                }
            });

        let visitor_methods = variants_data.iter().filter_map(
            |(_index, variant_ident, rust_type, serde_visitor_method)| {
                serde_visitor_method.as_ref().map(|method_name| {
                    let visit_type = match method_name.to_string().as_str() {
                        "visit_str" => quote! { &str },
                        "visit_bytes" => quote! { &[u8] },
                        _ => quote! { #rust_type },
                    };
                    quote! {
                        fn #method_name<E>(self, value: #visit_type) -> Result<Self::Value, E>
                        where
                            E: serde::de::Error,
                        {
                            Ok(#union_enum_name::#variant_ident(value.into()))
                        }
                    }
                })
            },
        );

        let serialize_arms = variants_data.iter().map(|(_, variant_ident, _, _)| {
            quote! {
                Self::#variant_ident(value) => value.serialize(serializer),
            }
        });

        let enum_definition = quote! {
            #[derive(Debug, PartialEq, Clone)]
            #[serde(remote = "Self")]
            pub enum #union_enum_name {
                #(#enum_variants),*
            }

            #(#from_impls)*
            #(#try_from_impls)*

            impl serde::Serialize for #union_enum_name {
                fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
                where
                    S: serde::Serializer,
                {
                    match self {
                        #(#serialize_arms)*
                    }
                }
            }

            impl<'de> serde::Deserialize<'de> for #union_enum_name {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: serde::Deserializer<'de>,
                {
                    struct UnionVisitor;

                    impl<'de> serde::de::Visitor<'de> for UnionVisitor {
                        type Value = #union_enum_name;

                        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                            formatter::write_str(format!(" {}", stringify!(#union_enum_name)).as_str())
                        }

                        #(#visitor_methods)*
                    }

                    deserializer.deserialize_any(UnionVisitor)
                }
            }
        };
        self.generated_union_enums
            .insert(union_enum_name_str, enum_definition.clone());
        Ok((union_enum_name, enum_definition))
    }
}

#[derive(Default)]
struct ModuleNode {
    name: Option<String>,
    submodules: BTreeMap<String, ModuleNode>,
    code: TokenStream,
}

impl ModuleNode {
    fn new(name: Option<String>) -> Self {
        Self {
            name,
            submodules: BTreeMap::new(),
            code: TokenStream::new(),
        }
    }

    fn add_schema(
        &mut self,
        namespace_parts: &[&str],
        schema_ir: &SchemaIr,
        generator: &mut CodeGenerator,
    ) -> Result<(), GeneratorError> {
        if let Some((first, rest)) = namespace_parts.split_first() {
            self.submodules
                .entry(first.to_string())
                .or_insert_with(|| ModuleNode::new(Some(first.to_string())))
                .add_schema(rest, schema_ir, generator)?;
        } else {
            let schema_code = generator.generate_schema(schema_ir)?;
            self.code.extend(schema_code);
        }
        Ok(())
    }

    fn to_token_stream(&self) -> TokenStream {
        let submodules_tokens = self
            .submodules
            .values()
            .map(|submodule| submodule.to_token_stream());

        let code = &self.code;

        if let Some(name) = &self.name {
            let ident = format_ident!("{}", name);
            quote! {
                pub mod #ident {
                    #(#submodules_tokens)*
                    #code
                }
            }
        } else {
            // Root node
            quote! {
                #(#submodules_tokens)*
                #code
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        EnumDetails, EnumIr, FieldIr, FixedDetails, FixedIr, RecordDetails, RecordIr, TypeIr,
        ValueIr,
    };
    use crate::parser::Parser;
    use quote::{format_ident, quote};
    use syn::{File, Type, parse_quote};

    #[test]
    fn test_avro_fqn_to_rust_path() {
        let fqn = "com.example.MyRecord";
        let expected: Type = parse_quote! { com::example::MyRecord };
        let actual = CodeGenerator::new().avro_fqn_to_rust_path(fqn);
        assert_eq!(quote!(#actual).to_string(), quote!(#expected).to_string());
    }

    #[test]
    fn test_avro_fqn_to_rust_name() {
        let fqn = "com.example.MyRecord";
        let expected = format_ident!("MyRecord");
        let actual = CodeGenerator::new().avro_fqn_to_rust_name(fqn).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_map_type_ir_to_rust_type() {
        let mut generator = CodeGenerator::new();

        // Simple types
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::Null).unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { () }.to_string());
        let (t, _) = generator
            .map_type_ir_to_rust_type(&TypeIr::Boolean)
            .unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { bool }.to_string());
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::Int).unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { i32 }.to_string());
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::Long).unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { i64 }.to_string());
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::Float).unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { f32 }.to_string());
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::Double).unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { f64 }.to_string());
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::Bytes).unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { Vec<u8> }.to_string());
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::String).unwrap();
        assert_eq!(quote! { #t }.to_string(), quote! { String }.to_string());
        // Logical types
        let (t, _) = generator.map_type_ir_to_rust_type(&TypeIr::Date).unwrap();
        assert_eq!(
            quote! { #t }.to_string(),
            quote! { chrono::NaiveDate }.to_string()
        );
        let (t, _) = generator
            .map_type_ir_to_rust_type(&TypeIr::Decimal {
                precision: 10,
                scale: 2,
            })
            .unwrap();
        assert_eq!(
            quote! { #t }.to_string(),
            quote! { rust_decimal::Decimal }.to_string()
        );
        // Complex types
        let (array_type, _) = generator
            .map_type_ir_to_rust_type(&TypeIr::Array(Box::new(TypeIr::String)))
            .unwrap();
        assert_eq!(
            quote!(#array_type).to_string(),
            quote! { Vec<String> }.to_string()
        );

        let (map_type, _) = generator
            .map_type_ir_to_rust_type(&TypeIr::Map(Box::new(TypeIr::Int)))
            .unwrap();
        assert_eq!(
            quote!(#map_type).to_string(),
            quote! { std::collections::HashMap<String, i32> }.to_string()
        );

        let (option_type, _) = generator
            .map_type_ir_to_rust_type(&TypeIr::Option(Box::new(TypeIr::Long)))
            .unwrap();
        assert_eq!(
            quote!(#option_type).to_string(),
            quote! { Option<i64> }.to_string()
        );

        let (record_type, _) = generator
            .map_type_ir_to_rust_type(&TypeIr::Record("my.Record".to_string()))
            .unwrap();
        assert_eq!(
            quote!(#record_type).to_string(),
            quote! { my::Record }.to_string()
        );
    }

    #[test]
    fn test_generate_default_value_expr() {
        let mut generator = CodeGenerator::new();

        // Simple values
        let null_expr = generator
            .generate_default_value_expr(&ValueIr::Null, &TypeIr::Option(Box::new(TypeIr::Int)))
            .unwrap();
        assert_eq!(null_expr.to_string(), quote! { None }.to_string());

        let bool_expr = generator
            .generate_default_value_expr(&ValueIr::Boolean(true), &TypeIr::Boolean)
            .unwrap();
        assert_eq!(bool_expr.to_string(), quote! { true }.to_string());

        let int_expr = generator
            .generate_default_value_expr(&ValueIr::Int(42), &TypeIr::Int)
            .unwrap();
        assert_eq!(int_expr.to_string(), quote! { 42i32 }.to_string());

        let string_expr = generator
            .generate_default_value_expr(&ValueIr::String("hello".to_string()), &TypeIr::String)
            .unwrap();
        assert_eq!(
            string_expr.to_string(),
            quote! { "hello".to_string() }.to_string()
        );

        // Array
        let array_val = ValueIr::Array(vec![ValueIr::Int(1), ValueIr::Int(2)]);
        let array_type = TypeIr::Array(Box::new(TypeIr::Int));
        let array_expr = generator
            .generate_default_value_expr(&array_val, &array_type)
            .unwrap();
        assert_eq!(
            array_expr.to_string(),
            quote! { vec![1i32, 2i32] }.to_string()
        );

        // Map
        let mut map_val_b_tree = std::collections::HashMap::new();
        map_val_b_tree.insert("a".to_string(), ValueIr::Int(1));
        let map_val = ValueIr::Map(map_val_b_tree);
        let map_type = TypeIr::Map(Box::new(TypeIr::Int));
        let map_expr = generator
            .generate_default_value_expr(&map_val, &map_type)
            .unwrap();
        let expected_map_expr = quote! {
            {
                let mut m = std::collections::HashMap::new();
                m.insert("a".to_string(), 1i32);
                m
            }
        };
        assert_eq!(
            map_expr.to_string().replace(" ", "").replace("\n", ""),
            expected_map_expr
                .to_string()
                .replace(" ", "")
                .replace("\n", "")
        );
    }

    #[test]
    fn test_generate_record() {
        let mut generator = CodeGenerator::new();
        let record_ir = RecordIr {
            name: "com.example.User".to_string(),
            doc: Some("A user record".to_string()),
            inner: RecordDetails {
                fields: vec![
                    FieldIr {
                        name: "id".to_string(),
                        doc: None,
                        ty: TypeIr::Long,
                        default: None,
                    },
                    FieldIr {
                        name: "username".to_string(),
                        doc: Some("The user\'s username".to_string()),
                        ty: TypeIr::String,
                        default: Some(ValueIr::String("guest".to_string())),
                    },
                ],
            },
        };
        let generated_code = generator.generate_record(&record_ir).unwrap();
        let formatted_code =
            prettyplease::unparse(&syn::parse2::<File>(generated_code.clone()).unwrap());
        insta::assert_snapshot!(formatted_code);
    }

    #[test]
    fn test_generate_enum() {
        let generator = CodeGenerator::new();
        let enum_ir = EnumIr {
            name: "com.example.Suit".to_string(),
            doc: Some("Card suit".to_string()),
            inner: EnumDetails {
                symbols: vec![
                    "SPADES".to_string(),
                    "HEARTS".to_string(),
                    "DIAMONDS".to_string(),
                    "CLUBS".to_string(),
                ],
            },
        };
        let generated_code = generator.generate_enum(&enum_ir).unwrap();
        let formatted_code =
            prettyplease::unparse(&syn::parse2::<File>(generated_code.clone()).unwrap());
        insta::assert_snapshot!(formatted_code);
    }

    #[test]
    fn test_generate_fixed() {
        let generator = CodeGenerator::new();
        let fixed_ir = FixedIr {
            name: "com.example.Md5".to_string(),
            doc: None,
            inner: FixedDetails { size: 16 },
        };
        let generated_code = generator.generate_fixed(&fixed_ir).unwrap();
        let formatted_code =
            prettyplease::unparse(&syn::parse2::<File>(generated_code.clone()).unwrap());
        insta::assert_snapshot!(formatted_code);
    }

    #[test]
    fn test_generate_union_enum() {
        let mut generator = CodeGenerator::new();
        let union_variants = vec![TypeIr::String, TypeIr::Int, TypeIr::Boolean];
        let (_name, generated_code) = generator.generate_union_enum(&union_variants).unwrap();
        let formatted_code =
            prettyplease::unparse(&syn::parse2::<File>(generated_code.clone()).unwrap());
        insta::assert_snapshot!(formatted_code);
    }

    #[test]
    fn generator_on_all_schemas() {
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

            let mut generator = CodeGenerator::new();
            let generated_code = generator.generate_all_schemas(&schema_ir).unwrap();
            let res = syn::parse2::<File>(generated_code.clone());
            if let Err(e) = res {
                eprintln!(
                    "Error parsing generated code for {}:\n{}",
                    path.display(),
                    generated_code
                );
                panic!("Syn error: {}", e);
            }
            let formatted_code = prettyplease::unparse(&res.unwrap());

            insta::assert_snapshot!(formatted_code);
        })
    }
}