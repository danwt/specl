//! Runtime values for Specl.

use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// A runtime value in Specl.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// Boolean value.
    Bool(bool),
    /// Integer value (arbitrary precision).
    Int(i64),
    /// String value.
    String(String),
    /// Set of values (sorted Vec for cache-friendly small-set performance).
    /// Arc-wrapped for cheap cloning (CoW semantics).
    Set(Arc<Vec<Value>>),
    /// Sequence of values.
    Seq(Vec<Value>),
    /// Function/map from keys to values (sorted Vec of pairs for cache-friendly performance).
    /// Arc-wrapped for cheap cloning (CoW semantics).
    Fn(Arc<Vec<(Value, Value)>>),
    /// Flat integer map: keys are implicit 0..len, values are i64.
    /// 4x smaller and O(1) lookup vs O(log N) binary search.
    /// Produced automatically for Dict[Int, Int] comprehensions.
    IntMap(Arc<Vec<i64>>),
    /// Record with named fields.
    Record(BTreeMap<String, Value>),
    /// Tuple of values.
    Tuple(Vec<Value>),
    /// None value (for Option type).
    None,
    /// Some value (for Option type).
    Some(Box<Value>),
}

impl Value {
    /// Return a human-readable type name for error messages.
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Bool(_) => "Bool",
            Value::Int(_) => "Int",
            Value::String(_) => "String",
            Value::Set(_) => "Set",
            Value::Seq(_) => "Seq",
            Value::Fn(_) => "Fn",
            Value::IntMap(_) => "Fn",
            Value::Record(_) => "Record",
            Value::Tuple(_) => "Tuple",
            Value::None => "None",
            Value::Some(_) => "Some",
        }
    }

    /// Create an empty set.
    pub fn empty_set() -> Self {
        Value::Set(Arc::new(Vec::new()))
    }

    /// Create an empty sequence.
    pub fn empty_seq() -> Self {
        Value::Seq(Vec::new())
    }

    /// Create an empty function/map.
    pub fn empty_fn() -> Self {
        Value::Fn(Arc::new(Vec::new()))
    }

    /// Create a range set (lo..hi, inclusive). Already sorted.
    pub fn range(lo: i64, hi: i64) -> Self {
        Value::Set(Arc::new((lo..=hi).map(Value::Int).collect()))
    }

    /// Create a set from an iterator, sorting and deduplicating.
    pub fn set_from_iter(iter: impl IntoIterator<Item = Value>) -> Self {
        let mut v: Vec<Value> = iter.into_iter().collect();
        v.sort();
        v.dedup();
        Value::Set(Arc::new(v))
    }

    /// Create a function/map from an iterator of key-value pairs, sorting by key.
    /// Last value wins for duplicate keys.
    pub fn fn_from_iter(iter: impl IntoIterator<Item = (Value, Value)>) -> Self {
        let mut v: Vec<(Value, Value)> = iter.into_iter().collect();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        v.dedup_by(|a, b| {
            if a.0 == b.0 {
                std::mem::swap(&mut a.1, &mut b.1);
                true
            } else {
                false
            }
        });
        Value::Fn(Arc::new(v))
    }

    /// Insert a value into a sorted set Vec. Returns true if newly inserted.
    pub fn set_insert(set: &mut Vec<Value>, val: Value) -> bool {
        match set.binary_search(&val) {
            Ok(_) => false,
            Err(pos) => {
                set.insert(pos, val);
                true
            }
        }
    }

    /// Check if a sorted set Vec contains a value.
    pub fn set_contains(set: &[Value], val: &Value) -> bool {
        set.binary_search(val).is_ok()
    }

    /// Get a value from a sorted function Vec by key.
    pub fn fn_get<'a>(func: &'a [(Value, Value)], key: &Value) -> Option<&'a Value> {
        func.binary_search_by(|(k, _)| k.cmp(key))
            .ok()
            .map(|idx| &func[idx].1)
    }

    /// Insert or update a key-value pair in a sorted function Vec.
    pub fn fn_insert(func: &mut Vec<(Value, Value)>, key: Value, value: Value) {
        match func.binary_search_by(|(k, _)| k.cmp(&key)) {
            Ok(idx) => func[idx].1 = value,
            Err(pos) => func.insert(pos, (key, value)),
        }
    }

    /// Check if this value is "truthy" (for boolean coercion).
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            _ => true,
        }
    }

    /// Get as boolean, if this is a boolean value.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Get as integer, if this is an integer value.
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// Get as string, if this is a string value.
    pub fn as_string(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    /// Get as set, if this is a set value.
    pub fn as_set(&self) -> Option<&[Value]> {
        match self {
            Value::Set(s) => Some(s),
            _ => None,
        }
    }

    /// Get as sequence, if this is a sequence value.
    pub fn as_seq(&self) -> Option<&Vec<Value>> {
        match self {
            Value::Seq(s) => Some(s),
            _ => None,
        }
    }

    /// Get as function/map, if this is a function value.
    pub fn as_fn(&self) -> Option<&[(Value, Value)]> {
        match self {
            Value::Fn(f) => Some(f),
            _ => None,
        }
    }

    /// Get as IntMap, if this is an IntMap value.
    pub fn as_intmap(&self) -> Option<&[i64]> {
        match self {
            Value::IntMap(arr) => Some(arr),
            _ => None,
        }
    }

    /// Convert IntMap to equivalent Fn representation.
    pub fn intmap_to_fn(arr: &[i64]) -> Value {
        Value::Fn(Arc::new(Self::intmap_to_fn_vec(arr)))
    }

    /// Convert IntMap slice to Vec of (key, value) pairs.
    pub fn intmap_to_fn_vec(arr: &[i64]) -> Vec<(Value, Value)> {
        arr.iter()
            .enumerate()
            .map(|(i, v)| (Value::Int(i as i64), Value::Int(*v)))
            .collect()
    }

    /// Get as record, if this is a record value.
    pub fn as_record(&self) -> Option<&BTreeMap<String, Value>> {
        match self {
            Value::Record(r) => Some(r),
            _ => None,
        }
    }

    /// Serialize value to bytes for fingerprinting.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        self.write_bytes(&mut bytes);
        bytes
    }

    /// Write serialized bytes into a buffer. Used by State::fingerprint to avoid per-var allocation.
    pub fn write_bytes(&self, out: &mut Vec<u8>) {
        match self {
            Value::Bool(b) => {
                out.push(0);
                out.push(if *b { 1 } else { 0 });
            }
            Value::Int(n) => {
                out.push(1);
                out.extend_from_slice(&n.to_le_bytes());
            }
            Value::String(s) => {
                out.push(2);
                out.extend_from_slice(&(s.len() as u64).to_le_bytes());
                out.extend_from_slice(s.as_bytes());
            }
            Value::Set(s) => {
                out.push(3);
                out.extend_from_slice(&(s.len() as u64).to_le_bytes());
                for v in s.iter() {
                    v.write_bytes(out);
                }
            }
            Value::Seq(s) => {
                out.push(4);
                out.extend_from_slice(&(s.len() as u64).to_le_bytes());
                for v in s {
                    v.write_bytes(out);
                }
            }
            Value::Fn(f) => {
                out.push(5);
                out.extend_from_slice(&(f.len() as u64).to_le_bytes());
                for (k, v) in f.iter() {
                    k.write_bytes(out);
                    v.write_bytes(out);
                }
            }
            Value::IntMap(arr) => {
                out.push(10);
                out.extend_from_slice(&(arr.len() as u64).to_le_bytes());
                for v in arr.iter() {
                    out.extend_from_slice(&v.to_le_bytes());
                }
            }
            Value::Record(r) => {
                out.push(6);
                out.extend_from_slice(&(r.len() as u64).to_le_bytes());
                for (k, v) in r {
                    out.extend_from_slice(&(k.len() as u64).to_le_bytes());
                    out.extend_from_slice(k.as_bytes());
                    v.write_bytes(out);
                }
            }
            Value::Tuple(t) => {
                out.push(7);
                out.extend_from_slice(&(t.len() as u64).to_le_bytes());
                for v in t {
                    v.write_bytes(out);
                }
            }
            Value::None => {
                out.push(8);
            }
            Value::Some(v) => {
                out.push(9);
                v.write_bytes(out);
            }
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn discriminant(v: &Value) -> u8 {
            match v {
                Value::Bool(_) => 0,
                Value::Int(_) => 1,
                Value::String(_) => 2,
                Value::Set(_) => 3,
                Value::Seq(_) => 4,
                Value::Fn(_) | Value::IntMap(_) => 5,
                Value::Record(_) => 6,
                Value::Tuple(_) => 7,
                Value::None => 8,
                Value::Some(_) => 9,
            }
        }

        let d1 = discriminant(self);
        let d2 = discriminant(other);

        match d1.cmp(&d2) {
            std::cmp::Ordering::Equal => {}
            other => return other,
        }

        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
            (Value::Int(a), Value::Int(b)) => a.cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Set(a), Value::Set(b)) => a.cmp(b),
            (Value::Seq(a), Value::Seq(b)) => a.cmp(b),
            (Value::Fn(a), Value::Fn(b)) => a.cmp(b),
            (Value::IntMap(a), Value::IntMap(b)) => a.cmp(b),
            (Value::IntMap(_), Value::Fn(_)) => std::cmp::Ordering::Less,
            (Value::Fn(_), Value::IntMap(_)) => std::cmp::Ordering::Greater,
            (Value::Record(a), Value::Record(b)) => a.cmp(b),
            (Value::Tuple(a), Value::Tuple(b)) => a.cmp(b),
            (Value::None, Value::None) => std::cmp::Ordering::Equal,
            (Value::Some(a), Value::Some(b)) => a.cmp(b),
            _ => unreachable!("discriminants should match"),
        }
    }
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Bool(b) => {
                0u8.hash(state);
                b.hash(state);
            }
            Value::Int(n) => {
                1u8.hash(state);
                n.hash(state);
            }
            Value::String(s) => {
                2u8.hash(state);
                s.hash(state);
            }
            Value::Set(s) => {
                3u8.hash(state);
                s.len().hash(state);
                for v in s.iter() {
                    v.hash(state);
                }
            }
            Value::Seq(s) => {
                4u8.hash(state);
                s.len().hash(state);
                for v in s {
                    v.hash(state);
                }
            }
            Value::Fn(f) => {
                5u8.hash(state);
                f.len().hash(state);
                for (k, v) in f.iter() {
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::IntMap(arr) => {
                10u8.hash(state);
                arr.len().hash(state);
                for v in arr.iter() {
                    v.hash(state);
                }
            }
            Value::Record(r) => {
                6u8.hash(state);
                r.len().hash(state);
                for (k, v) in r {
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::Tuple(t) => {
                7u8.hash(state);
                t.len().hash(state);
                for v in t {
                    v.hash(state);
                }
            }
            Value::None => {
                8u8.hash(state);
            }
            Value::Some(v) => {
                9u8.hash(state);
                v.hash(state);
            }
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Set(s) => {
                write!(f, "{{")?;
                for (i, v) in s.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "}}")
            }
            Value::Seq(s) => {
                write!(f, "[")?;
                for (i, v) in s.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Value::Fn(m) => {
                write!(f, "fn{{")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} -> {}", k, v)?;
                }
                write!(f, "}}")
            }
            Value::IntMap(arr) => {
                write!(f, "fn{{")?;
                for (i, v) in arr.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} -> {}", i, v)?;
                }
                write!(f, "}}")
            }
            Value::Record(r) => {
                write!(f, "{{")?;
                for (i, (k, v)) in r.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, "}}")
            }
            Value::Tuple(t) => {
                write!(f, "(")?;
                for (i, v) in t.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
            Value::None => write!(f, "None"),
            Value::Some(v) => write!(f, "Some({})", v),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_equality() {
        assert_eq!(Value::Int(42), Value::Int(42));
        assert_ne!(Value::Int(42), Value::Int(43));
        assert_eq!(Value::Bool(true), Value::Bool(true));
        assert_eq!(
            Value::String("hello".to_string()),
            Value::String("hello".to_string())
        );
    }

    #[test]
    fn test_value_set() {
        let mut s = Vec::new();
        Value::set_insert(&mut s, Value::Int(1));
        Value::set_insert(&mut s, Value::Int(2));
        Value::set_insert(&mut s, Value::Int(1)); // duplicate
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn test_value_hash_consistency() {
        use std::hash::{DefaultHasher, Hash, Hasher};
        fn hash_value(v: &Value) -> u64 {
            let mut h = DefaultHasher::new();
            v.hash(&mut h);
            h.finish()
        }
        let v1 = Value::Int(42);
        let v2 = Value::Int(42);
        let v3 = Value::Int(43);

        assert_eq!(hash_value(&v1), hash_value(&v2));
        assert_ne!(hash_value(&v1), hash_value(&v3));
    }

    #[test]
    fn test_range() {
        let r = Value::range(1, 3);
        if let Value::Set(s) = r {
            assert_eq!(s.len(), 3);
            assert!(Value::set_contains(&s, &Value::Int(1)));
            assert!(Value::set_contains(&s, &Value::Int(2)));
            assert!(Value::set_contains(&s, &Value::Int(3)));
        } else {
            panic!("expected set");
        }
    }

    #[test]
    fn test_display() {
        assert_eq!(Value::Int(42).to_string(), "42");
        assert_eq!(Value::Bool(true).to_string(), "true");
        assert_eq!(Value::String("hello".to_string()).to_string(), "\"hello\"");
    }

    #[test]
    fn test_fn_operations() {
        let mut f = Vec::new();
        Value::fn_insert(&mut f, Value::Int(1), Value::Bool(true));
        Value::fn_insert(&mut f, Value::Int(2), Value::Bool(false));
        assert_eq!(Value::fn_get(&f, &Value::Int(1)), Some(&Value::Bool(true)));
        assert_eq!(Value::fn_get(&f, &Value::Int(2)), Some(&Value::Bool(false)));
        assert_eq!(Value::fn_get(&f, &Value::Int(3)), None);

        // Update existing key
        Value::fn_insert(&mut f, Value::Int(1), Value::Bool(false));
        assert_eq!(Value::fn_get(&f, &Value::Int(1)), Some(&Value::Bool(false)));
    }
}
