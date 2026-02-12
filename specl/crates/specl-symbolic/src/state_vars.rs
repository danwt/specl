//! Variable layout analysis: maps specl state variables to Z3 variables.

use specl_ir::CompiledSpec;
use specl_types::Type;

use crate::SymbolicResult;

/// Layout of Z3 variables for a specl specification.
#[derive(Debug)]
pub struct VarLayout {
    /// One entry per specl state variable.
    pub entries: Vec<VarEntry>,
}

/// How a single specl variable maps to Z3 variables.
#[derive(Debug, Clone)]
pub struct VarEntry {
    /// Index in CompiledSpec.vars.
    pub specl_var_idx: usize,
    /// Variable name.
    pub name: String,
    /// What kind of Z3 encoding to use.
    pub kind: VarKind,
}

/// Z3 encoding strategy for a variable.
#[derive(Debug, Clone)]
pub enum VarKind {
    /// Single Z3 Bool.
    Bool,
    /// Single Z3 Int, optionally bounded.
    Int { lo: Option<i64>, hi: Option<i64> },
    /// Dict exploded into individual Z3 variables per key.
    ExplodedDict {
        key_lo: i64,
        key_hi: i64,
        value_kind: Box<VarKind>,
    },
    /// Set over bounded domain: one Z3 Bool per element.
    ExplodedSet { lo: i64, hi: i64 },
}

impl VarLayout {
    /// Analyze a compiled spec and compute the Z3 variable layout.
    pub fn from_spec(spec: &CompiledSpec) -> SymbolicResult<Self> {
        let mut entries = Vec::new();
        for var in &spec.vars {
            let kind = Self::type_to_kind(&var.ty)?;
            entries.push(VarEntry {
                specl_var_idx: var.index,
                name: var.name.clone(),
                kind,
            });
        }
        Ok(VarLayout { entries })
    }

    fn type_to_kind(ty: &Type) -> SymbolicResult<VarKind> {
        match ty {
            Type::Bool => Ok(VarKind::Bool),
            Type::Int => Ok(VarKind::Int { lo: None, hi: None }),
            Type::Nat => Ok(VarKind::Int {
                lo: Some(0),
                hi: None,
            }),
            Type::Range(lo, hi) => Ok(VarKind::Int {
                lo: Some(*lo),
                hi: Some(*hi),
            }),
            Type::Fn(key_ty, val_ty) => {
                if let Type::Range(lo, hi) = key_ty.as_ref() {
                    let value_kind = Self::type_to_kind(val_ty)?;
                    Ok(VarKind::ExplodedDict {
                        key_lo: *lo,
                        key_hi: *hi,
                        value_kind: Box::new(value_kind),
                    })
                } else {
                    Err(crate::SymbolicError::Unsupported(format!(
                        "Dict with non-range key type: {:?}",
                        key_ty
                    )))
                }
            }
            Type::Set(elem_ty) => {
                if let Type::Range(lo, hi) = elem_ty.as_ref() {
                    Ok(VarKind::ExplodedSet { lo: *lo, hi: *hi })
                } else {
                    Err(crate::SymbolicError::Unsupported(format!(
                        "Set with non-range element type: {:?}",
                        elem_ty
                    )))
                }
            }
            _ => Err(crate::SymbolicError::Unsupported(format!(
                "variable type: {:?}",
                ty
            ))),
        }
    }
}

impl VarKind {
    /// Number of Z3 variables needed for this kind.
    pub fn z3_var_count(&self) -> usize {
        match self {
            VarKind::Bool | VarKind::Int { .. } => 1,
            VarKind::ExplodedDict {
                key_lo,
                key_hi,
                value_kind,
            } => {
                let num_keys = (*key_hi - *key_lo + 1) as usize;
                num_keys * value_kind.z3_var_count()
            }
            VarKind::ExplodedSet { lo, hi } => (*hi - *lo + 1) as usize,
        }
    }
}
