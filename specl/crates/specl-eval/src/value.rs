//! NaN-boxed runtime values for Specl.
//!
//! `Value` is a compact 8-byte representation using a tagged pointer scheme.
//! Inline types (Int, Bool, None) are stored directly in the u64.
//! Heap types (Set, Seq, Fn, etc.) store an Arc raw pointer in the lower 56 bits.
//!
//! This reduces per-value memory from 32 bytes to 8 bytes (4x improvement),
//! and makes Clone O(1) for all types (Arc refcount increment for heap types).

use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

// === Tag constants (bits 56-63) ===

const TAG_INT: u8 = 0x00; // i56 sign-extended in payload (most common → cheapest)
const TAG_BOOL_FALSE: u8 = 0x01;
const TAG_BOOL_TRUE: u8 = 0x02;
const TAG_NONE: u8 = 0x03;
const TAG_STRING: u8 = 0x10; // Arc<String>
const TAG_SET: u8 = 0x11; // Arc<Vec<Value>>
const TAG_SEQ: u8 = 0x12; // Arc<Vec<Value>>
const TAG_FN: u8 = 0x13; // Arc<Vec<(Value, Value)>>
const TAG_INTMAP: u8 = 0x14; // Arc<Vec<i64>>
const TAG_RECORD: u8 = 0x15; // Arc<BTreeMap<String, Value>>
const TAG_TUPLE: u8 = 0x16; // Arc<Vec<Value>>
const TAG_SOME: u8 = 0x17; // Arc<Value>
const TAG_BIGINT: u8 = 0xFF; // Arc<i64> (values outside i56 range)

const TAG_SHIFT: u32 = 56;
const PTR_MASK: u64 = (1u64 << TAG_SHIFT) - 1;
const I56_MIN: i64 = -(1i64 << 55);
const I56_MAX: i64 = (1i64 << 55) - 1;

/// NaN-boxed runtime value. 8 bytes.
///
/// Stores inline integers (i56), booleans, and None directly.
/// Heap types (String, Set, Seq, Fn, IntMap, Record, Tuple, Some)
/// are stored as Arc raw pointers for O(1) clone.
#[repr(transparent)]
pub struct Value(u64);

// SAFETY: Value contains either inline data (Int/Bool/None) or raw pointers
// to Arc allocations. Arc<T> is Send+Sync when T: Send+Sync, and all our
// inner types satisfy this.
unsafe impl Send for Value {}
unsafe impl Sync for Value {}

/// Borrowed view of a Value for pattern matching.
pub enum VK<'a> {
    Bool(bool),
    Int(i64),
    String(&'a str),
    Set(&'a [Value]),
    Seq(&'a [Value]),
    Fn(&'a [(Value, Value)]),
    IntMap(&'a [i64]),
    Record(&'a BTreeMap<String, Value>),
    Tuple(&'a [Value]),
    None,
    Some(&'a Value),
}

// === Tag / pointer helpers (private) ===

impl Value {
    #[inline(always)]
    fn tag(&self) -> u8 {
        (self.0 >> TAG_SHIFT) as u8
    }

    #[inline(always)]
    fn ptr(&self) -> usize {
        (self.0 & PTR_MASK) as usize
    }

    /// Extract inline i56 via sign extension.
    #[inline(always)]
    fn as_i56(&self) -> i64 {
        // Shift left 8 to put bit 55 in sign position, then arithmetic right shift
        ((self.0 << 8) as i64) >> 8
    }

    /// Read i64 from a BigInt Arc.
    #[inline]
    fn bigint_val(&self) -> i64 {
        debug_assert_eq!(self.tag(), TAG_BIGINT);
        unsafe { *(self.ptr() as *const i64) }
    }

    /// Pack a tag + pointer into a Value.
    #[inline(always)]
    fn from_heap<T>(tag: u8, arc: Arc<T>) -> Self {
        let ptr = Arc::into_raw(arc) as u64;
        debug_assert_eq!(ptr >> TAG_SHIFT, 0, "pointer exceeds 56 bits");
        Value(((tag as u64) << TAG_SHIFT) | (ptr & PTR_MASK))
    }

    /// Reconstruct Arc from stored pointer WITHOUT running Drop on self.
    /// Caller takes ownership of the Arc.
    #[inline]
    unsafe fn take_arc<T>(&self) -> Arc<T> {
        Arc::from_raw(self.ptr() as *const T)
    }
}

// === Constructors ===

impl Value {
    #[inline]
    pub fn int(n: i64) -> Self {
        if n >= I56_MIN && n <= I56_MAX {
            Value((n as u64) & PTR_MASK)
        } else {
            Self::from_heap(TAG_BIGINT, Arc::new(n))
        }
    }

    #[inline]
    pub fn bool(b: bool) -> Self {
        if b {
            Value((TAG_BOOL_TRUE as u64) << TAG_SHIFT)
        } else {
            Value((TAG_BOOL_FALSE as u64) << TAG_SHIFT)
        }
    }

    #[inline]
    pub fn none() -> Self {
        Value((TAG_NONE as u64) << TAG_SHIFT)
    }

    #[inline]
    pub fn string(s: String) -> Self {
        Self::from_heap(TAG_STRING, Arc::new(s))
    }

    #[inline]
    pub fn set(v: Arc<Vec<Value>>) -> Self {
        Self::from_heap(TAG_SET, v)
    }

    #[inline]
    pub fn seq(v: Vec<Value>) -> Self {
        Self::from_heap(TAG_SEQ, Arc::new(v))
    }

    /// Named `func` to avoid conflict with `fn` keyword.
    #[inline]
    pub fn func(v: Arc<Vec<(Value, Value)>>) -> Self {
        Self::from_heap(TAG_FN, v)
    }

    #[inline]
    pub fn intmap(v: Arc<Vec<i64>>) -> Self {
        Self::from_heap(TAG_INTMAP, v)
    }

    #[inline]
    pub fn record(r: BTreeMap<String, Value>) -> Self {
        Self::from_heap(TAG_RECORD, Arc::new(r))
    }

    #[inline]
    pub fn tuple(v: Vec<Value>) -> Self {
        Self::from_heap(TAG_TUPLE, Arc::new(v))
    }

    #[inline]
    pub fn some(v: Value) -> Self {
        Self::from_heap(TAG_SOME, Arc::new(v))
    }
}

// === Heap type methods (is_*, into_*_arc, from_*_arc) ===

macro_rules! heap_methods {
    ($tag:expr, $T:ty, $is_name:ident, $into_name:ident, $from_name:ident) => {
        #[inline]
        pub fn $is_name(&self) -> bool {
            self.tag() == $tag
        }

        /// Consume this Value and return the inner Arc.
        pub fn $into_name(self) -> Arc<$T> {
            debug_assert_eq!(self.tag(), $tag);
            let arc = unsafe { self.take_arc::<$T>() };
            std::mem::forget(self); // prevent Drop from running
            arc
        }

        pub fn $from_name(arc: Arc<$T>) -> Self {
            Self::from_heap($tag, arc)
        }
    };
}

impl Value {
    heap_methods!(TAG_STRING, String, is_string, into_string_arc, from_string_arc);
    heap_methods!(TAG_SET, Vec<Value>, is_set_v, into_set_arc, from_set_arc);
    heap_methods!(TAG_SEQ, Vec<Value>, is_seq, into_seq_arc, from_seq_arc);
    heap_methods!(TAG_FN, Vec<(Value, Value)>, is_fn, into_fn_arc, from_fn_arc);
    heap_methods!(TAG_INTMAP, Vec<i64>, is_intmap, into_intmap_arc, from_intmap_arc);
    heap_methods!(
        TAG_RECORD,
        BTreeMap<String, Value>,
        is_record,
        into_record_arc,
        from_record_arc
    );
    heap_methods!(TAG_TUPLE, Vec<Value>, is_tuple, into_tuple_arc, from_tuple_arc);
    heap_methods!(TAG_SOME, Value, is_some_v, into_some_arc, from_some_arc);

    #[inline]
    pub fn is_int(&self) -> bool {
        self.tag() == TAG_INT || self.tag() == TAG_BIGINT
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        self.tag() == TAG_BOOL_FALSE || self.tag() == TAG_BOOL_TRUE
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        self.tag() == TAG_NONE
    }

    /// True for TAG_FN or TAG_INTMAP (both represent dict/function values).
    #[inline]
    pub fn is_fn_like(&self) -> bool {
        self.is_fn() || self.is_intmap()
    }
}

// === kind() — the primary pattern-matching method ===

impl Value {
    #[inline]
    pub fn kind(&self) -> VK<'_> {
        match self.tag() {
            TAG_BOOL_FALSE => VK::Bool(false),
            TAG_BOOL_TRUE => VK::Bool(true),
            TAG_INT => VK::Int(self.as_i56()),
            TAG_BIGINT => VK::Int(self.bigint_val()),
            TAG_NONE => VK::None,
            TAG_STRING => VK::String(unsafe { &*(self.ptr() as *const String) }),
            TAG_SET => {
                let vec = unsafe { &*(self.ptr() as *const Vec<Value>) };
                VK::Set(vec.as_slice())
            }
            TAG_SEQ => {
                let vec = unsafe { &*(self.ptr() as *const Vec<Value>) };
                VK::Seq(vec.as_slice())
            }
            TAG_FN => {
                let vec = unsafe { &*(self.ptr() as *const Vec<(Value, Value)>) };
                VK::Fn(vec.as_slice())
            }
            TAG_INTMAP => {
                let vec = unsafe { &*(self.ptr() as *const Vec<i64>) };
                VK::IntMap(vec.as_slice())
            }
            TAG_RECORD => VK::Record(unsafe { &*(self.ptr() as *const BTreeMap<String, Value>) }),
            TAG_TUPLE => {
                let vec = unsafe { &*(self.ptr() as *const Vec<Value>) };
                VK::Tuple(vec.as_slice())
            }
            TAG_SOME => VK::Some(unsafe { &*(self.ptr() as *const Value) }),
            _ => unreachable!("invalid Value tag: {:#x}", self.tag()),
        }
    }
}

// === Existing API (unchanged signatures where possible) ===

impl Value {
    pub fn type_name(&self) -> &'static str {
        match self.tag() {
            TAG_BOOL_FALSE | TAG_BOOL_TRUE => "Bool",
            TAG_INT | TAG_BIGINT => "Int",
            TAG_STRING => "String",
            TAG_SET => "Set",
            TAG_SEQ => "Seq",
            TAG_FN | TAG_INTMAP => "Fn",
            TAG_RECORD => "Record",
            TAG_TUPLE => "Tuple",
            TAG_NONE => "None",
            TAG_SOME => "Some",
            _ => "Unknown",
        }
    }

    pub fn empty_set() -> Self {
        Value::set(Arc::new(Vec::new()))
    }

    pub fn empty_seq() -> Self {
        Value::seq(Vec::new())
    }

    pub fn empty_fn() -> Self {
        Value::func(Arc::new(Vec::new()))
    }

    pub fn range(lo: i64, hi: i64) -> Self {
        Value::set(Arc::new((lo..=hi).map(Value::int).collect()))
    }

    pub fn set_from_iter(iter: impl IntoIterator<Item = Value>) -> Self {
        let mut v: Vec<Value> = iter.into_iter().collect();
        v.sort();
        v.dedup();
        Value::set(Arc::new(v))
    }

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
        Value::func(Arc::new(v))
    }

    pub fn set_insert(set: &mut Vec<Value>, val: Value) -> bool {
        match set.binary_search(&val) {
            Ok(_) => false,
            Err(pos) => {
                set.insert(pos, val);
                true
            }
        }
    }

    pub fn set_contains(set: &[Value], val: &Value) -> bool {
        set.binary_search(val).is_ok()
    }

    pub fn fn_get<'a>(func: &'a [(Value, Value)], key: &Value) -> Option<&'a Value> {
        func.binary_search_by(|(k, _)| k.cmp(key))
            .ok()
            .map(|idx| &func[idx].1)
    }

    pub fn fn_insert(func: &mut Vec<(Value, Value)>, key: Value, value: Value) {
        match func.binary_search_by(|(k, _)| k.cmp(&key)) {
            Ok(idx) => func[idx].1 = value,
            Err(pos) => func.insert(pos, (key, value)),
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self.tag() {
            TAG_BOOL_FALSE => false,
            _ => true,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self.tag() {
            TAG_BOOL_TRUE => Some(true),
            TAG_BOOL_FALSE => Some(false),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        match self.tag() {
            TAG_INT => Some(self.as_i56()),
            TAG_BIGINT => Some(self.bigint_val()),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        if self.tag() == TAG_STRING {
            Some(unsafe { &*(self.ptr() as *const String) })
        } else {
            None
        }
    }

    pub fn as_set(&self) -> Option<&[Value]> {
        if self.tag() == TAG_SET {
            Some(unsafe { &*(self.ptr() as *const Vec<Value>) })
        } else {
            None
        }
    }

    pub fn as_seq(&self) -> Option<&[Value]> {
        if self.tag() == TAG_SEQ {
            Some(unsafe { &*(self.ptr() as *const Vec<Value>) })
        } else {
            None
        }
    }

    pub fn as_fn(&self) -> Option<&[(Value, Value)]> {
        if self.tag() == TAG_FN {
            Some(unsafe { &*(self.ptr() as *const Vec<(Value, Value)>) })
        } else {
            None
        }
    }

    pub fn as_intmap(&self) -> Option<&[i64]> {
        if self.tag() == TAG_INTMAP {
            Some(unsafe { &*(self.ptr() as *const Vec<i64>) })
        } else {
            None
        }
    }

    pub fn as_record(&self) -> Option<&BTreeMap<String, Value>> {
        if self.tag() == TAG_RECORD {
            Some(unsafe { &*(self.ptr() as *const BTreeMap<String, Value>) })
        } else {
            None
        }
    }

    pub fn intmap_to_fn(arr: &[i64]) -> Value {
        Value::func(Arc::new(Self::intmap_to_fn_vec(arr)))
    }

    pub fn intmap_to_fn_vec(arr: &[i64]) -> Vec<(Value, Value)> {
        arr.iter()
            .enumerate()
            .map(|(i, v)| (Value::int(i as i64), Value::int(*v)))
            .collect()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        self.write_bytes(&mut bytes);
        bytes
    }

    pub fn write_bytes(&self, out: &mut Vec<u8>) {
        match self.kind() {
            VK::Bool(b) => {
                out.push(0);
                out.push(if b { 1 } else { 0 });
            }
            VK::Int(n) => {
                out.push(1);
                out.extend_from_slice(&n.to_le_bytes());
            }
            VK::String(s) => {
                out.push(2);
                out.extend_from_slice(&(s.len() as u64).to_le_bytes());
                out.extend_from_slice(s.as_bytes());
            }
            VK::Set(s) => {
                out.push(3);
                out.extend_from_slice(&(s.len() as u64).to_le_bytes());
                for v in s {
                    v.write_bytes(out);
                }
            }
            VK::Seq(s) => {
                out.push(4);
                out.extend_from_slice(&(s.len() as u64).to_le_bytes());
                for v in s {
                    v.write_bytes(out);
                }
            }
            VK::Fn(f) => {
                out.push(5);
                out.extend_from_slice(&(f.len() as u64).to_le_bytes());
                for (k, v) in f {
                    k.write_bytes(out);
                    v.write_bytes(out);
                }
            }
            VK::IntMap(arr) => {
                out.push(10);
                out.extend_from_slice(&(arr.len() as u64).to_le_bytes());
                for v in arr {
                    out.extend_from_slice(&v.to_le_bytes());
                }
            }
            VK::Record(r) => {
                out.push(6);
                out.extend_from_slice(&(r.len() as u64).to_le_bytes());
                for (k, v) in &*r {
                    out.extend_from_slice(&(k.len() as u64).to_le_bytes());
                    out.extend_from_slice(k.as_bytes());
                    v.write_bytes(out);
                }
            }
            VK::Tuple(t) => {
                out.push(7);
                out.extend_from_slice(&(t.len() as u64).to_le_bytes());
                for v in t {
                    v.write_bytes(out);
                }
            }
            VK::None => {
                out.push(8);
            }
            VK::Some(v) => {
                out.push(9);
                v.write_bytes(out);
            }
        }
    }
}

// === Clone ===

impl Clone for Value {
    #[inline]
    fn clone(&self) -> Self {
        match self.tag() {
            // Inline types: just copy the bits
            TAG_INT | TAG_BOOL_FALSE | TAG_BOOL_TRUE | TAG_NONE => Value(self.0),
            // Heap types: increment Arc refcount
            TAG_STRING => {
                unsafe { Arc::increment_strong_count(self.ptr() as *const String) };
                Value(self.0)
            }
            TAG_SET => {
                unsafe { Arc::increment_strong_count(self.ptr() as *const Vec<Value>) };
                Value(self.0)
            }
            TAG_SEQ => {
                unsafe { Arc::increment_strong_count(self.ptr() as *const Vec<Value>) };
                Value(self.0)
            }
            TAG_FN => {
                unsafe {
                    Arc::increment_strong_count(self.ptr() as *const Vec<(Value, Value)>)
                };
                Value(self.0)
            }
            TAG_INTMAP => {
                unsafe { Arc::increment_strong_count(self.ptr() as *const Vec<i64>) };
                Value(self.0)
            }
            TAG_RECORD => {
                unsafe {
                    Arc::increment_strong_count(
                        self.ptr() as *const BTreeMap<String, Value>,
                    )
                };
                Value(self.0)
            }
            TAG_TUPLE => {
                unsafe { Arc::increment_strong_count(self.ptr() as *const Vec<Value>) };
                Value(self.0)
            }
            TAG_SOME => {
                unsafe { Arc::increment_strong_count(self.ptr() as *const Value) };
                Value(self.0)
            }
            TAG_BIGINT => {
                unsafe { Arc::increment_strong_count(self.ptr() as *const i64) };
                Value(self.0)
            }
            _ => unreachable!("invalid Value tag in clone"),
        }
    }
}

// === Drop ===

impl Drop for Value {
    fn drop(&mut self) {
        match self.tag() {
            // Inline types: nothing to drop
            TAG_INT | TAG_BOOL_FALSE | TAG_BOOL_TRUE | TAG_NONE => {}
            // Heap types: decrement Arc refcount
            TAG_STRING => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const String);
            },
            TAG_SET => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const Vec<Value>);
            },
            TAG_SEQ => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const Vec<Value>);
            },
            TAG_FN => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const Vec<(Value, Value)>);
            },
            TAG_INTMAP => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const Vec<i64>);
            },
            TAG_RECORD => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const BTreeMap<String, Value>);
            },
            TAG_TUPLE => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const Vec<Value>);
            },
            TAG_SOME => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const Value);
            },
            TAG_BIGINT => unsafe {
                Arc::decrement_strong_count(self.ptr() as *const i64);
            },
            _ => {}
        }
    }
}

// === PartialEq / Eq ===

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        // Fast path: identical bits (same Arc pointer or same inline value)
        if self.0 == other.0 {
            return true;
        }
        let t1 = self.tag();
        let t2 = other.tag();
        // Int == BigInt cross-comparison
        if (t1 == TAG_INT || t1 == TAG_BIGINT) && (t2 == TAG_INT || t2 == TAG_BIGINT) {
            return self.as_int().unwrap() == other.as_int().unwrap();
        }
        if t1 != t2 {
            // IntMap and Fn are considered different tags for the purposes of Eq,
            // even though they have the same ordering discriminant.
            return false;
        }
        // Same tag, different bits — compare inner data
        match t1 {
            TAG_INT | TAG_BOOL_FALSE | TAG_BOOL_TRUE | TAG_NONE => false,
            TAG_STRING => self.as_string() == other.as_string(),
            TAG_SET => self.as_set() == other.as_set(),
            TAG_SEQ => self.as_seq() == other.as_seq(),
            TAG_FN => self.as_fn() == other.as_fn(),
            TAG_INTMAP => self.as_intmap() == other.as_intmap(),
            TAG_RECORD => self.as_record() == other.as_record(),
            TAG_TUPLE => {
                let a = unsafe { &*(self.ptr() as *const Vec<Value>) };
                let b = unsafe { &*(other.ptr() as *const Vec<Value>) };
                a == b
            }
            TAG_SOME => {
                let a = unsafe { &*(self.ptr() as *const Value) };
                let b = unsafe { &*(other.ptr() as *const Value) };
                a == b
            }
            _ => false,
        }
    }
}

impl Eq for Value {}

// === PartialOrd / Ord ===

impl Value {
    /// Ordering discriminant matching the original enum layout.
    fn ord_discriminant(&self) -> u8 {
        match self.tag() {
            TAG_BOOL_FALSE | TAG_BOOL_TRUE => 0,
            TAG_INT | TAG_BIGINT => 1,
            TAG_STRING => 2,
            TAG_SET => 3,
            TAG_SEQ => 4,
            TAG_FN | TAG_INTMAP => 5,
            TAG_RECORD => 6,
            TAG_TUPLE => 7,
            TAG_NONE => 8,
            TAG_SOME => 9,
            _ => 255,
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        // Fast path: both inline Int (most common comparison in protocol specs).
        // TAG_INT is 0x00, so tag byte is 0 for inline ints.
        let t1 = self.tag();
        let t2 = other.tag();
        if t1 == TAG_INT && t2 == TAG_INT {
            return self.as_i56().cmp(&other.as_i56());
        }

        // Fast path: identical bits (same Arc pointer or same inline value)
        if self.0 == other.0 {
            return Ordering::Equal;
        }

        let d1 = self.ord_discriminant();
        let d2 = other.ord_discriminant();
        match d1.cmp(&d2) {
            Ordering::Equal => {}
            other => return other,
        }

        match (self.kind(), other.kind()) {
            (VK::Bool(a), VK::Bool(b)) => a.cmp(&b),
            (VK::Int(a), VK::Int(b)) => a.cmp(&b),
            (VK::String(a), VK::String(b)) => a.cmp(b),
            (VK::Set(a), VK::Set(b)) => a.cmp(b),
            (VK::Seq(a), VK::Seq(b)) => a.cmp(b),
            (VK::Fn(a), VK::Fn(b)) => a.cmp(b),
            (VK::IntMap(a), VK::IntMap(b)) => a.cmp(b),
            (VK::IntMap(_), VK::Fn(_)) => Ordering::Less,
            (VK::Fn(_), VK::IntMap(_)) => Ordering::Greater,
            (VK::Record(a), VK::Record(b)) => a.cmp(b),
            (VK::Tuple(a), VK::Tuple(b)) => a.cmp(b),
            (VK::None, VK::None) => Ordering::Equal,
            (VK::Some(a), VK::Some(b)) => a.cmp(b),
            _ => unreachable!("discriminants should match"),
        }
    }
}

// === Hash ===

/// Hash a slice of Values that are known to all be Int, skipping discriminant per element.
#[inline]
fn hash_int_elements<H: Hasher>(values: &[Value], state: &mut H) {
    for v in values {
        if let VK::Int(n) = v.kind() {
            n.hash(state);
        } else {
            v.hash(state);
        }
    }
}

/// Hash key-value pairs where keys are known to all be Int, skipping discriminant per element.
#[inline]
fn hash_int_keyed_pairs<H: Hasher>(pairs: &[(Value, Value)], state: &mut H) {
    for (k, v) in pairs {
        if let VK::Int(n) = k.kind() {
            n.hash(state);
        } else {
            k.hash(state);
        }
        v.hash(state);
    }
}

/// Check if all Values in a slice are Int.
#[inline]
fn all_int(values: &[Value]) -> bool {
    values.iter().all(|v| v.is_int())
}

/// Check if all keys in a slice of pairs are Int.
#[inline]
fn all_int_keys(pairs: &[(Value, Value)]) -> bool {
    pairs.iter().all(|(k, _)| k.is_int())
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.kind() {
            VK::Bool(b) => {
                0u8.hash(state);
                b.hash(state);
            }
            VK::Int(n) => {
                1u8.hash(state);
                n.hash(state);
            }
            VK::String(s) => {
                2u8.hash(state);
                s.hash(state);
            }
            VK::Set(s) => {
                3u8.hash(state);
                s.len().hash(state);
                if all_int(s) {
                    hash_int_elements(s, state);
                } else {
                    for v in s {
                        v.hash(state);
                    }
                }
            }
            VK::Seq(s) => {
                4u8.hash(state);
                s.len().hash(state);
                if all_int(s) {
                    hash_int_elements(s, state);
                } else {
                    for v in s {
                        v.hash(state);
                    }
                }
            }
            VK::Fn(f) => {
                5u8.hash(state);
                f.len().hash(state);
                if all_int_keys(f) {
                    hash_int_keyed_pairs(f, state);
                } else {
                    for (k, v) in f {
                        k.hash(state);
                        v.hash(state);
                    }
                }
            }
            VK::IntMap(arr) => {
                // Batch-hash: write the entire i64 slice as contiguous bytes.
                // AHasher can process 16 bytes at a time with AES-NI, much faster
                // than individual i64.hash() calls.
                10u8.hash(state);
                arr.len().hash(state);
                let bytes = unsafe {
                    std::slice::from_raw_parts(arr.as_ptr() as *const u8, arr.len() * 8)
                };
                state.write(bytes);
            }
            VK::Record(r) => {
                6u8.hash(state);
                r.len().hash(state);
                for (k, v) in &*r {
                    k.hash(state);
                    v.hash(state);
                }
            }
            VK::Tuple(t) => {
                7u8.hash(state);
                t.len().hash(state);
                if all_int(t) {
                    hash_int_elements(t, state);
                } else {
                    for v in t {
                        v.hash(state);
                    }
                }
            }
            VK::None => {
                8u8.hash(state);
            }
            VK::Some(v) => {
                9u8.hash(state);
                v.hash(state);
            }
        }
    }
}

// === Display ===

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            VK::Bool(b) => write!(f, "{}", b),
            VK::Int(n) => write!(f, "{}", n),
            VK::String(s) => write!(f, "\"{}\"", s),
            VK::Set(s) => {
                write!(f, "{{")?;
                for (i, v) in s.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "}}")
            }
            VK::Seq(s) => {
                write!(f, "[")?;
                for (i, v) in s.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            VK::Fn(m) => {
                write!(f, "fn{{")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} -> {}", k, v)?;
                }
                write!(f, "}}")
            }
            VK::IntMap(arr) => {
                write!(f, "fn{{")?;
                for (i, v) in arr.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} -> {}", i, v)?;
                }
                write!(f, "}}")
            }
            VK::Record(r) => {
                write!(f, "{{")?;
                for (i, (k, v)) in r.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, "}}")
            }
            VK::Tuple(t) => {
                write!(f, "(")?;
                for (i, v) in t.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
            VK::None => write!(f, "None"),
            VK::Some(v) => write!(f, "Some({})", v),
        }
    }
}

// === Debug ===

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            VK::Bool(b) => write!(f, "Bool({})", b),
            VK::Int(n) => write!(f, "Int({})", n),
            VK::String(s) => write!(f, "String({:?})", s),
            VK::Set(s) => {
                write!(f, "Set(")?;
                f.debug_list().entries(s.iter()).finish()?;
                write!(f, ")")
            }
            VK::Seq(s) => {
                write!(f, "Seq(")?;
                f.debug_list().entries(s.iter()).finish()?;
                write!(f, ")")
            }
            VK::Fn(m) => {
                write!(f, "Fn(")?;
                f.debug_list().entries(m.iter()).finish()?;
                write!(f, ")")
            }
            VK::IntMap(a) => {
                write!(f, "IntMap(")?;
                f.debug_list().entries(a.iter()).finish()?;
                write!(f, ")")
            }
            VK::Record(r) => {
                write!(f, "Record(")?;
                f.debug_map().entries(r.iter()).finish()?;
                write!(f, ")")
            }
            VK::Tuple(t) => {
                write!(f, "Tuple(")?;
                f.debug_list().entries(t.iter()).finish()?;
                write!(f, ")")
            }
            VK::None => write!(f, "None"),
            VK::Some(v) => write!(f, "Some({:?})", v),
        }
    }
}

// === Tests ===

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_size() {
        assert_eq!(std::mem::size_of::<Value>(), 8);
    }

    #[test]
    fn test_int_roundtrip() {
        for n in [0, 1, -1, 42, -42, I56_MIN, I56_MAX] {
            let v = Value::int(n);
            assert_eq!(v.as_int(), Some(n), "failed for n={n}");
        }
        // BigInt
        let big = Value::int(i64::MAX);
        assert_eq!(big.as_int(), Some(i64::MAX));
        let big_neg = Value::int(i64::MIN);
        assert_eq!(big_neg.as_int(), Some(i64::MIN));
    }

    #[test]
    fn test_value_equality() {
        assert_eq!(Value::int(42), Value::int(42));
        assert_ne!(Value::int(42), Value::int(43));
        assert_eq!(Value::bool(true), Value::bool(true));
        assert_eq!(Value::string("hello".to_string()), Value::string("hello".to_string()));
    }

    #[test]
    fn test_value_set() {
        let mut s = Vec::new();
        Value::set_insert(&mut s, Value::int(1));
        Value::set_insert(&mut s, Value::int(2));
        Value::set_insert(&mut s, Value::int(1)); // duplicate
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
        let v1 = Value::int(42);
        let v2 = Value::int(42);
        let v3 = Value::int(43);

        assert_eq!(hash_value(&v1), hash_value(&v2));
        assert_ne!(hash_value(&v1), hash_value(&v3));
    }

    #[test]
    fn test_range() {
        let r = Value::range(1, 3);
        if let VK::Set(s) = r.kind() {
            assert_eq!(s.len(), 3);
            assert!(Value::set_contains(s, &Value::int(1)));
            assert!(Value::set_contains(s, &Value::int(2)));
            assert!(Value::set_contains(s, &Value::int(3)));
        } else {
            panic!("expected set");
        }
    }

    #[test]
    fn test_display() {
        assert_eq!(Value::int(42).to_string(), "42");
        assert_eq!(Value::bool(true).to_string(), "true");
        assert_eq!(Value::string("hello".to_string()).to_string(), "\"hello\"");
    }

    #[test]
    fn test_fn_operations() {
        let mut f = Vec::new();
        Value::fn_insert(&mut f, Value::int(1), Value::bool(true));
        Value::fn_insert(&mut f, Value::int(2), Value::bool(false));
        assert_eq!(Value::fn_get(&f, &Value::int(1)), Some(&Value::bool(true)));
        assert_eq!(Value::fn_get(&f, &Value::int(2)), Some(&Value::bool(false)));
        assert_eq!(Value::fn_get(&f, &Value::int(3)), None);

        // Update existing key
        Value::fn_insert(&mut f, Value::int(1), Value::bool(false));
        assert_eq!(Value::fn_get(&f, &Value::int(1)), Some(&Value::bool(false)));
    }

    #[test]
    fn test_clone_and_drop() {
        // Heap types: clone should increment refcount, drop should decrement
        let set = Value::set(Arc::new(vec![Value::int(1), Value::int(2)]));
        let set2 = set.clone();
        assert_eq!(set, set2);
        drop(set2);
        // Original should still be valid
        assert_eq!(set.as_set().unwrap().len(), 2);
    }

    #[test]
    fn test_bigint_equality() {
        // BigInt values should be equal based on mathematical value
        let a = Value::int(i64::MAX);
        let b = Value::int(i64::MAX);
        assert_eq!(a, b);
        assert_ne!(a, Value::int(i64::MAX - 1));
    }

    #[test]
    fn test_ordering() {
        assert!(Value::int(1) < Value::int(2));
        assert!(Value::bool(false) < Value::bool(true));
        assert!(Value::bool(true) < Value::int(0)); // Bool < Int in discriminant order
    }

    #[test]
    fn test_into_arc_roundtrip() {
        let v = Value::set(Arc::new(vec![Value::int(1), Value::int(2)]));
        let arc = v.into_set_arc();
        assert_eq!(arc.len(), 2);
        let v2 = Value::from_set_arc(arc);
        assert_eq!(v2.as_set().unwrap().len(), 2);
    }
}
