use std::collections::HashMap;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, Type, parse_quote};

use crate::ir::{RecordIr, SchemaIr, TypeIr, ValueIr};

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
    pub fn generate_schema(&self, schema_ir: &SchemaIr) -> TokenStream {
        match schema_ir {
            SchemaIr::Record(record_ir) => self.generate_record(record_ir),
            SchemaIr::Enum(enum_ir) => self.generate_enum(enum_ir),
            SchemaIr::Fixed(fixed_ir) => self.generate_fixed(fixed_ir),
            SchemaIr::Placeholder { .. } => {
                quote! { compile_error!("Placeholder schema found durin code generation"); }
            }
        }
    }

    /// Generates a TokenStream for alll schemas, typically wrapped in modules
    pub fn generate_all_schemas(&self, schemas: &[SchemaIr]) -> TokenStream {
        let mut all_code = TokenStream::new();
        // Group schemas by namespace to create modules
        let mut namespaces: std::collections::BTreeMap<String, Vec<&SchemaIr>> =
            std::collections::BTreeMap::new();
        for schema_ir in schemas {
            let fqn = schema_ir.fqn();
            let parts: Vec<&str> = fqn.split('.').collect();
            let (namespace, _name) = if parts.len() > 1 {
                (parts[0..parts.len() - 1].join("."), parts.last().unwrap())
            } else {
                ("".to_string(), parts.last().unwrap())
            };
            namespaces
                .entry(namespace)
                .or_insert_with(Vec::new)
                .push(schema_ir);
        }

        for (namespace, schemas_in_ns) in namespaces {
            let namespace_tokens = if namespace.is_empty() {
                let inner_code = schemas_in_ns.iter().map(|s| self.generate_schema(s));
                quote! { #(#inner_code)* }
            } else {
                // create nested modules for namespaces
                let mut current_module_tokens = TokenStream::new();
                let mut current_path_parts: Vec<Ident> = Vec::new();
                for part in namespace.split('.') {
                    let module_name = format_ident!("{}", part);
                    current_path_parts.push(module_name.clone());
                    // innermost module, generate schemas
                    let inner_code = if current_path_parts.len() == namespace.split('.').count() {
                        schemas_in_ns
                            .iter()
                            .map(|s| self.generate_schema(s))
                            .collect()
                    } else {
                        TokenStream::new()
                    };
                    current_module_tokens = quote! {
                        pub mod #module_name {
                            #current_module_tokens
                            #inner_code
                        }
                    };
                }
                current_module_tokens
            };
            all_code.extend(namespace_tokens);
        }
        // After generating all records/enums/fixed, union enums are generated
        let mut sorted_union_enums: Vec<(&String, &TokenStream)> =
            self.generated_union_enums.iter().collect();
        sorted_union_enums.sort_by_key(|(name, _)| *name);
        for (_name, tokens) in sorted_union_enums {
            all_code.extend(tokens.clone());
        }

        all_code
    }

    fn avro_fqn_to_rust_path(&self, fqn: &str) -> Type {
        let parts: Vec<Ident> = fqn.split('.').map(|s| format_ident!("{}", s)).collect();
        parse_quote! { #(#parts)::* }
    }

    fn avro_fqn_to_rust_name(&self, fqn: &str) -> Ident {
        let parts: Vec<&str> = fqn.split('.').collect();
        format_ident!("{}", parts.last().unwrap())
    }

    // Maps a TypeIr to a Rust Type (TokenStream)
    fn map_type_ir_to_rust_type(&mut self, ty_ir: &TypeIr) -> Type {
        match ty_ir {
            TypeIr::Null => parse_quote! { () },
            TypeIr::Boolean => parse_quote! { bool },
            TypeIr::Int => parse_quote! { i32 },
            TypeIr::Long => parse_quote! { i64 },
            TypeIr::Float => parse_quote! { f32 },
            TypeIr::Double => parse_quote! { f64 },
            TypeIr::Bytes => parse_quote! { Vec<u8>},
            TypeIr::String => parse_quote! { String },
            TypeIr::Date => parse_quote! { chrono::NaiveDate },
            TypeIr::TimeMillis => parse_quote! { chrono::Duration },
            TypeIr::TimeMicros => parse_quote! { chrono::Duration },
            TypeIr::TimestampMillis => parse_quote! { chrono::DateTime<chrono::Utc> },
            TypeIr::TimestampMicros => parse_quote! { chrono::DateTime<chrono::Utc> },
            TypeIr::TimestampNanos => parse_quote! { chrono::DateTime<chrono::Utc> },
            TypeIr::LocalTimestampMillis => parse_quote! { chrono::NaiveDateTime },
            TypeIr::LocalTimestampMicros => parse_quote! { chrono::NaiveDateTime },
            TypeIr::LocalTimestampNanos => parse_quote! { chrono::NaiveDateTime },
            TypeIr::Duration => parse_quote! { apache_avro::Duration },
            TypeIr::Uuid => parse_quote! { uuid::Uuid },
            TypeIr::Decimal { .. } => parse_quote! { rust_decimal::Decimal },
            TypeIr::BigDecimal => parse_quote! { bigdecimal::BigDecimal },
            TypeIr::Array(inner) => {
                let inner_type = self.map_type_ir_to_rust_type(inner);
                parse_quote! { Vec<#inner_type> }
            }
            TypeIr::Map(inner) => {
                let inner_type = self.map_type_ir_to_rust_type(inner);
                parse_quote! { std::collections::HashMap<String, #inner_type> }
            }
            TypeIr::Option(inner) => {
                let inner_type = self.map_type_ir_to_rust_type(inner);
                parse_quote! { Option<#inner_type> }
            }
            TypeIr::Union(variants) => {
                let (union_enum_name, _enum_tokens) = self.generate_union_enum(variants);
                parse_quote! { #union_enum_name }
            }
            TypeIr::Record(fqn) => self.avro_fqn_to_rust_path(fqn),
            TypeIr::Enum(fqn) => self.avro_fqn_to_rust_path(fqn),
            TypeIr::Fixed(fqn) => self.avro_fqn_to_rust_path(fqn),
        }
    }

    // Generates a Rust expression for a default value
    fn generate_default_value_expr(&self, value_ir: &ValueIr, target_type: &TypeIr) -> TokenStream {
        match value_ir {
            ValueIr::Null => quote! { None },
            ValueIr::Boolean(b) => quote! { #b },
            ValueIr::Int(i) => quote! { #i },
            ValueIr::Long(l) => quote! { #l },
            ValueIr::Float(f) => quote! { #f },
            ValueIr::Double(d) => quote! { #d },
            ValueIr::Bytes(b) => quote! { vec![#(#b),*] },
            ValueIr::String(s) => quote! { #s.to_string() },
            ValueIr::Date(d) => {
                quote! { chrono::NaiveDateTime::from_ymd_opt(1970, 1, 1).unwrap().checked_add_days(chrono::Days::new(#d as u32)).unwrap() }
            }
            ValueIr::TimeMillis(t) => quote! { chrono::Duration::millisecnds(#t as i64) },
            ValueIr::TimeMicros(t) => quote! { chrono::Duration::microseconds(#t) },
            ValueIr::TimestampMillis(t) => {
                quote! { chrono::DateTime::<chrono::Utc>::from_timestamp_millis(#t).unwrap() }
            }
            ValueIr::TimestampMicros(t) => {
                quote! { chrono::DateTime::<chrono::Utc>::from_timestamp_micros(#t).unwrap() }
            }
            ValueIr::TimestampNanos(t) => {
                quote! { chrono::DateTime::<chrono::Utc>::from_timestamp_nanos(#t).unwrap() }
            }
            ValueIr::LocalTimestampMillis(t) => {
                quote! { chrono::NaiveDateTime::from_timestamp_millis(#t).unwrap() }
            }
            ValueIr::LocalTimestampMicros(t) => {
                quote! { chrono::NaiveDateTime::from_timestamp_micros(#t).unwrap() }
            }
            ValueIr::LocalTimestampNanos(t) => {
                quote! { chrono::NaiveDateTime::from_timestamp_nanos(#t).unwrap() }
            }
            ValueIr::Duration(d) => quote! { apache_avro::Duration::new([#(#d),*]) },
            ValueIr::Uuid(s) => quote! { uuid::Uuid::parse_str(#s).unwrap() },
            ValueIr::Decimal(big_int) => {
                if let TypeIr::Decimal { precision, scale } = target_type {
                    let s_str = big_int.to_string();
                    quote! { rust_decimal::Decimal::from_str(#s_str).unwrap().with_scale(#scale as u32) }
                } else {
                    panic!("Decimal default value requires Decimal TypeIr");
                }
            }
            ValueIr::BigDecimal(s) => quote! { bigdecimal::BigDecimal::from_str(#s).unwrap() },
            ValueIr::Array(arr) => {
                let inner_type = if let TypeIr::Array(inner) = target_type {
                    inner
                } else {
                    panic!("Mismatched type for array default")
                };
                let elements = arr
                    .iter()
                    .map(|v| self.generate_default_value_expr(v, inner_type));
                quote! { vec![#(#elements),*] }
            }
            ValueIr::Map(map) => {
                let inner_type = if let TypeIr::Map(inner) = target_type {
                    inner
                } else {
                    panic!("Mismatched type for map default")
                };
                let entries = map.iter().map(|(k, v)| {
                    let val_expr = self.generate_default_value_expr(v, inner_type);
                    quote! { m.insert(#k.to_string(), #val_expr); }
                });
                quote! {
                    {
                        let mut m = std::collections::HashMap::new();
                        #(#entries)*
                        m
                    }
                }
            }
            ValueIr::Enum(s) => {
                let enum_path = if let TypeIr::Enum(fqn) = target_type {
                    self.avro_fqn_to_rust_path(fqn)
                } else {
                    panic!("Mismatched type for enum default")
                };
                let variant_name = format_ident!("{}", s);
                quote! { #enum_path::#variant_name }
            }
            ValueIr::Fixed(b) => quote! { [#(#b),*] },
            ValueIr::Record(map) => {
                let record_path = if let TypeIr::Record(fqn) = target_type {
                    self.avro_fqn_to_rust_path(fqn)
                } else {
                    panic!("Mismatched type for record default")
                };
                let fields = map.iter().map(|(k, v)| {
                    let field_name = format_ident!("{}", k);
                    let val_expr = self.generate_default_value_expr(v, &TypeIr::Null); // TODO:
                    // fixme
                    quote! { #field_name: #val_expr }
                });
                quote! { #record_path { #(#fields),* } }
            }
        }
    }

    /// Helper to convert a fully qualified Avro name to a Rust struct/enum name.
    /// e.g., "com.example.MyRecord" -> `MyRecord`
    fn generate_record(&self, record_ir: &RecordIr) -> TokenStream {
        let struct_name = self.avro_fqn_to_rust_name(&record_ir.name);
        let doc = &record_ir.doc.as_ref().map(|d| quote! { #[doc = #d] });
        let fields = record_ir.inner.fields.iter().map(|field| {
            let field_name = format_ident!("{}", field.name);
            let field_type = self.map_type_ir_to_rust_type(&field.ty);
            let field_doc = &field.doc.as_ref().map(|d| quote! { #[doc = #d] });

            let default_attr = if field.default.is_some() {
                quote! { #[serde(default = "default_#field_name")] }
            } else {
                quote! {}
            };

            quote! {
                #field_doc
                #default_attr
                pub #field_name: #field_type,
            }
        });

        let default_fns: Vec<TokenStream> = record_ir
            .inner
            .fields
            .iter()
            .filter_map(|field| {
                if let Some(default_val_ir) = &field.default {
                    let fn_name = format_ident!("defult_{}", field.name);
                    let field_type = self.map_type_ir_to_rust_type(&field.ty);
                    let default_expr = self.generate_default_value_expr(default_val_ir, &field.ty);
                    Some(quote! {
                        fn #fn_name() -> #field_type {
                            #default_expr
                        }
                    })
                } else {
                    None
                }
            })
            .collect();

        quote! {
            #doc
            #[derive(Debug, PartialEq, Clone, serde::Serialize, serde::Deserialize)]
            pub struct #struct_name {
                #(#fields),*
            }

            #(#default_fns)*
        }
    }

    fn generate_union_enum(&mut self, union_ir_variants: &[TypeIr]) -> (Ident, TokenStream) {
        let mut sorted_rust_types: Vec<String> = union_ir_variants
            .iter()
            .map(|ty_ir| self.map_type_ir_to_rust_type(ty_ir).to_string())
            .collect();
        sorted_rust_types.sort();

        let union_enum_name_str = format!("Union{}", sorted_rust_types.join(""));
        let union_enum_name = format_ident!("{}", union_enum_name_str);
        if let Some(existing_tokens) = self.generated_union_enums.get(&union_enum_name_str) {
            return (union_enum_name, existing_tokens.clone());
        }

        let variants = union_ir_variants.iter().map(|ty_ir| {
            let rust_type = self.map_type_ir_to_rust_type(ty_ir);
            let variant_name = match ty_ir {
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
                TypeIr::Record(fqn) => self.avro_fqn_to_rust_name(fqn),
                TypeIr::Enum(fqn) => self.avro_fqn_to_rust_name(fqn),
                TypeIr::Fixed(fqn) => self.avro_fqn_to_rust_name(fqn),
            };
            quote! { #variant_name(#rust_type) }
        });

        let enum_definition = quote! {
            pub enumb #union_enum_name {
                #(#variants),*
            }

            impl serde::Serialize for #union_enum_name {
                fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
                where
                    S: serde::Serializer,
                {
                    match self {
                        #(
                            #union_enum_name::#variants => {
                                unimplemented!("custon avro union serialization needed for #union_enum_name");
                            }
                        )*
                    }
                }
            }

            impl<'de> serde::Deserialize<'de> for #union_enum_name {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: serde::Deserializer<'de>,
                {
                    unimplemented!("custom avrounion deserialization needed for #union_enum_name");
                }
            }
        };
        self.generated_union_enums
            .insert(union_enum_name_str, enum_definition.clone());
        (union_enum_name, enum_definition)
    }
}
