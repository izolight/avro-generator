use serde::Serialize;

#[derive(Debug, Serialize)]
pub enum SchemaIr {
    Record(RecordIr),
    Enum(EnumIr),
    Fixed(FixedIr),

    /// Represents a named type that has been discovered but not yet fully processed
    Placeholder {
        fqn: String,
        kind: SchemaKind,
    },
}

impl SchemaIr {
    pub fn fqn(&self) -> &str {
        match self {
            SchemaIr::Record(r) => &r.name,
            SchemaIr::Enum(e) => &e.name,
            SchemaIr::Fixed(f) => &f.name,
            SchemaIr::Placeholder { fqn, .. } => fqn,
        }
    }
}

#[derive(Debug, Serialize)]
pub enum SchemaKind {
    Record,
    Enum,
    Fixed,
}

#[derive(Debug, Serialize)]
pub struct NamedType<T> {
    pub name: String,
    pub doc: Option<String>,
    pub inner: T,
}

pub type RecordIr = NamedType<RecordDetails>;
pub type EnumIr = NamedType<EnumDetails>;
pub type FixedIr = NamedType<FixedDetails>;

#[derive(Debug, Serialize)]
pub struct RecordDetails {
    pub fields: Vec<FieldIr>,
}

#[derive(Debug, Serialize)]
pub struct FieldIr {
    pub name: String,
    pub doc: Option<String>,
    pub ty: TypeIr,
    pub default: Option<ValueIr>,
}

#[derive(Debug, Serialize)]
pub struct EnumDetails {
    pub symbols: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct FixedDetails {
    pub size: usize,
}

#[derive(Debug, Serialize)]
pub enum TypeIr {
    // Primitives
    Null,
    Boolean,
    Int,
    Long,
    Float,
    Double,
    Bytes,
    String,

    // Logicaal Types
    Date,
    TimeMillis,
    TimeMicros,
    TimestampMillis,
    TimestampMicros,
    TimestampNanos,
    LocalTimestampMillis,
    LocalTimestampMicros,
    LocalTimestampNanos,
    Duration,
    Uuid,
    Decimal { precision: usize, scale: usize },
    BigDecimal,

    // Complex types
    Array(Box<TypeIr>),
    Map(Box<TypeIr>),
    Option(Box<TypeIr>),
    Union(Vec<TypeIr>),

    // Named types
    Record(String),
    Enum(String),
    Fixed(String),
}

#[derive(Debug, PartialEq, Serialize)]
pub enum ValueIr {
    Null,
    Boolean(bool),
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    Bytes(Vec<u8>),
    String(String),
    // Corresponding variants for logical type defaults
    Date(i32),            // days from epoch
    TimeMillis(i32),      // ms from midnight
    TimeMicros(i64),      // us from midnight
    TimestampMillis(i64), // ms from epoch
    TimestampMicros(i64), // us from epoch
    TimestampNanos(i64),  // ns from epoch
    LocalTimestampMillis(i64),
    LocalTimestampMicros(i64),
    LocalTimestampNanos(i64),
    Duration([u8; 12]), // 4 bytes month, 4 bytes days, 4 bytes ms
    Uuid(String),       // String representation of UUID
    Decimal(num_bigint::BigInt),
    BigDecimal(String), // String representation of big decimal
    Array(Vec<ValueIr>),
    Map(std::collections::HashMap<String, ValueIr>),
    Enum(String),
    Fixed(Vec<u8>),
    Record(std::collections::HashMap<String, ValueIr>),
}
