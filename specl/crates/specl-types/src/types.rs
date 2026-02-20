//! Type representation for the Specl type system.

use std::collections::BTreeMap;
use std::fmt;

/// A Specl type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Boolean type.
    Bool,
    /// Natural number (non-negative integer).
    Nat,
    /// Integer.
    Int,
    /// String.
    String,
    /// Set type `Set[T]`.
    Set(Box<Type>),
    /// Sequence type `Seq[T]`.
    Seq(Box<Type>),
    /// Dict type `dict[K, V]` (finite map).
    Fn(Box<Type>, Box<Type>),
    /// Option type `Option[T]`.
    Option(Box<Type>),
    /// Record type with named fields.
    Record(RecordType),
    /// Tuple type `(T1, T2, ...)`.
    Tuple(Vec<Type>),
    /// Finite range type `lo..hi`.
    Range(i64, i64),
    /// Named type (reference to a type alias).
    Named(String),
    /// Type variable (for inference).
    Var(TypeVar),
    /// Error type (used for error recovery).
    Error,
}

impl Type {
    /// Check if this is a numeric type (Nat, Int, or Range).
    pub fn is_numeric(&self) -> bool {
        matches!(self, Type::Nat | Type::Int | Type::Range(_, _))
    }

    /// Check if this is a collection type (Set, Seq, or Fn).
    pub fn is_collection(&self) -> bool {
        matches!(self, Type::Set(_) | Type::Seq(_) | Type::Fn(_, _))
    }

    /// Check if this type contains any type variables.
    pub fn has_vars(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Set(t) | Type::Seq(t) | Type::Option(t) => t.has_vars(),
            Type::Fn(k, v) => k.has_vars() || v.has_vars(),
            Type::Record(r) => r.fields.values().any(|t| t.has_vars()),
            Type::Tuple(elems) => elems.iter().any(|t| t.has_vars()),
            _ => false,
        }
    }

    /// Substitute type variables according to a substitution.
    pub fn substitute(&self, subst: &Substitution) -> Type {
        match self {
            Type::Var(v) => subst.get(v).cloned().unwrap_or_else(|| self.clone()),
            Type::Set(t) => Type::Set(Box::new(t.substitute(subst))),
            Type::Seq(t) => Type::Seq(Box::new(t.substitute(subst))),
            Type::Option(t) => Type::Option(Box::new(t.substitute(subst))),
            Type::Fn(k, v) => {
                Type::Fn(Box::new(k.substitute(subst)), Box::new(v.substitute(subst)))
            }
            Type::Record(r) => Type::Record(RecordType {
                fields: r
                    .fields
                    .iter()
                    .map(|(k, v)| (k.clone(), v.substitute(subst)))
                    .collect(),
            }),
            Type::Tuple(elems) => Type::Tuple(elems.iter().map(|t| t.substitute(subst)).collect()),
            _ => self.clone(),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Nat => write!(f, "Nat"),
            Type::Int => write!(f, "Int"),
            Type::String => write!(f, "String"),
            Type::Set(t) => write!(f, "Set[{}]", t),
            Type::Seq(t) => write!(f, "Seq[{}]", t),
            Type::Fn(k, v) => write!(f, "dict[{}, {}]", k, v),
            Type::Option(t) => write!(f, "Option[{}]", t),
            Type::Record(r) => {
                write!(f, "Dict {{ ")?;
                for (i, (name, ty)) in r.fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, ty)?;
                }
                write!(f, " }}")
            }
            Type::Tuple(elems) => {
                write!(f, "(")?;
                for (i, ty) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ty)?;
                }
                write!(f, ")")
            }
            Type::Range(lo, hi) => write!(f, "{}..{}", lo, hi),
            Type::Named(name) => write!(f, "{}", name),
            Type::Var(v) => write!(f, "?{}", v.0),
            Type::Error => write!(f, "<error>"),
        }
    }
}

/// A record type with named fields.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordType {
    /// Ordered map of field names to types.
    pub fields: BTreeMap<String, Type>,
}

impl RecordType {
    /// Create a new empty record type.
    pub fn new() -> Self {
        Self {
            fields: BTreeMap::new(),
        }
    }

    /// Create a record type from field definitions.
    pub fn from_fields(fields: impl IntoIterator<Item = (String, Type)>) -> Self {
        Self {
            fields: fields.into_iter().collect(),
        }
    }

    /// Get the type of a field.
    pub fn get_field(&self, name: &str) -> Option<&Type> {
        self.fields.get(name)
    }
}

impl Default for RecordType {
    fn default() -> Self {
        Self::new()
    }
}

/// A type variable for type inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVar(pub u32);

impl TypeVar {
    /// Create a fresh type variable from an ID.
    pub fn new(id: u32) -> Self {
        Self(id)
    }
}

/// A type substitution mapping type variables to types.
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    mappings: BTreeMap<TypeVar, Type>,
}

impl Substitution {
    /// Create an empty substitution.
    pub fn new() -> Self {
        Self {
            mappings: BTreeMap::new(),
        }
    }

    /// Get the type bound to a variable, if any.
    pub fn get(&self, var: &TypeVar) -> Option<&Type> {
        self.mappings.get(var)
    }

    /// Bind a type variable to a type.
    pub fn insert(&mut self, var: TypeVar, ty: Type) {
        self.mappings.insert(var, ty);
    }

    /// Compose two substitutions: self then other.
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = Substitution::new();

        // Apply other to all types in self
        for (var, ty) in &self.mappings {
            result.insert(*var, ty.substitute(other));
        }

        // Add bindings from other that aren't in self
        for (var, ty) in &other.mappings {
            if !result.mappings.contains_key(var) {
                result.insert(*var, ty.clone());
            }
        }

        result
    }

    /// Check if the substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.mappings.is_empty()
    }
}

/// Type variable generator for fresh variables.
#[derive(Debug, Clone, Default)]
pub struct TypeVarGen {
    next_id: u32,
}

impl TypeVarGen {
    /// Create a new generator.
    pub fn new() -> Self {
        Self { next_id: 0 }
    }

    /// Generate a fresh type variable.
    pub fn fresh(&mut self) -> TypeVar {
        let var = TypeVar(self.next_id);
        self.next_id += 1;
        var
    }

    /// Generate a fresh type variable wrapped in a Type.
    pub fn fresh_type(&mut self) -> Type {
        Type::Var(self.fresh())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_display() {
        assert_eq!(Type::Bool.to_string(), "Bool");
        assert_eq!(Type::Set(Box::new(Type::Nat)).to_string(), "Set[Nat]");
        assert_eq!(
            Type::Fn(Box::new(Type::String), Box::new(Type::Int)).to_string(),
            "dict[String, Int]"
        );
    }

    #[test]
    fn test_type_has_vars() {
        let mut gen = TypeVarGen::new();
        assert!(!Type::Bool.has_vars());
        assert!(Type::Var(gen.fresh()).has_vars());
        assert!(Type::Set(Box::new(Type::Var(gen.fresh()))).has_vars());
    }

    #[test]
    fn test_substitution() {
        let mut gen = TypeVarGen::new();
        let v1 = gen.fresh();
        let v2 = gen.fresh();

        let mut subst = Substitution::new();
        subst.insert(v1, Type::Nat);

        assert_eq!(Type::Var(v1).substitute(&subst), Type::Nat);
        assert_eq!(Type::Var(v2).substitute(&subst), Type::Var(v2));
    }

    #[test]
    fn test_record_type() {
        let rec =
            RecordType::from_fields([("x".to_string(), Type::Nat), ("y".to_string(), Type::Bool)]);
        assert_eq!(rec.get_field("x"), Some(&Type::Nat));
        assert_eq!(rec.get_field("z"), None);
    }
}
