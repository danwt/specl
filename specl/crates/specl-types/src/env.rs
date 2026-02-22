//! Type environment and scope management.

use crate::types::Type;
use std::collections::HashMap;

/// A type environment for tracking variable and type bindings.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    /// Stack of scopes, innermost last.
    scopes: Vec<Scope>,
    /// Type aliases (global).
    type_aliases: HashMap<String, Type>,
    /// Constants (global).
    constants: HashMap<String, Type>,
    /// State variables (global).
    state_vars: HashMap<String, Type>,
    /// Actions and their signatures.
    actions: HashMap<String, ActionSig>,
    /// User-defined functions.
    funcs: HashMap<String, FuncInfo>,
}

/// A scope containing local variable bindings.
#[derive(Debug, Clone, Default)]
struct Scope {
    /// Variable name to type mapping.
    bindings: HashMap<String, Type>,
}

/// An action signature.
#[derive(Debug, Clone)]
pub struct ActionSig {
    /// Parameter names and types.
    pub params: Vec<(String, Type)>,
}

/// A user-defined function signature.
#[derive(Debug, Clone)]
pub struct FuncInfo {
    /// Parameter names.
    pub param_names: Vec<String>,
    /// Parameter types (may be type variables for polymorphism).
    pub param_types: Vec<Type>,
}

impl TypeEnv {
    /// Create a new empty type environment with a global scope.
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::default()],
            type_aliases: HashMap::new(),
            constants: HashMap::new(),
            state_vars: HashMap::new(),
            actions: HashMap::new(),
            funcs: HashMap::new(),
        }
    }

    // === Scope management ===

    /// Enter a new scope.
    pub fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    /// Exit the current scope.
    pub fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    // === Local variables ===

    /// Bind a local variable in the current scope.
    pub fn bind_local(&mut self, name: String, ty: Type) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.bindings.insert(name, ty);
        }
    }

    /// Look up a local variable, searching from innermost scope.
    pub fn lookup_local(&self, name: &str) -> Option<&Type> {
        for scope in self.scopes.iter().rev() {
            if let Some(ty) = scope.bindings.get(name) {
                return Some(ty);
            }
        }
        None
    }

    // === Type aliases ===

    /// Define a type alias.
    pub fn define_type_alias(&mut self, name: String, ty: Type) {
        self.type_aliases.insert(name, ty);
    }

    /// Look up a type alias.
    pub fn lookup_type_alias(&self, name: &str) -> Option<&Type> {
        self.type_aliases.get(name)
    }

    /// Resolve a named type to its actual type.
    /// Returns the type itself if it's not an alias.
    pub fn resolve_type(&self, ty: &Type) -> Type {
        match ty {
            Type::Named(name) => {
                if let Some(aliased) = self.lookup_type_alias(name) {
                    self.resolve_type(aliased)
                } else {
                    ty.clone()
                }
            }
            Type::Set(inner) => Type::Set(Box::new(self.resolve_type(inner))),
            Type::Seq(inner) => Type::Seq(Box::new(self.resolve_type(inner))),
            Type::Option(inner) => Type::Option(Box::new(self.resolve_type(inner))),
            Type::Fn(k, v) => Type::Fn(
                Box::new(self.resolve_type(k)),
                Box::new(self.resolve_type(v)),
            ),
            _ => ty.clone(),
        }
    }

    // === Constants ===

    /// Define a constant.
    pub fn define_const(&mut self, name: String, ty: Type) {
        self.constants.insert(name, ty);
    }

    /// Look up a constant.
    pub fn lookup_const(&self, name: &str) -> Option<&Type> {
        self.constants.get(name)
    }

    // === State variables ===

    /// Define a state variable.
    pub fn define_var(&mut self, name: String, ty: Type) {
        self.state_vars.insert(name, ty);
    }

    /// Look up a state variable.
    pub fn lookup_var(&self, name: &str) -> Option<&Type> {
        self.state_vars.get(name)
    }

    /// Get all state variable names.
    pub fn state_var_names(&self) -> impl Iterator<Item = &str> {
        self.state_vars.keys().map(|s| s.as_str())
    }

    // === Actions ===

    /// Define an action.
    pub fn define_action(&mut self, name: String, sig: ActionSig) {
        self.actions.insert(name, sig);
    }

    /// Look up an action.
    pub fn lookup_action(&self, name: &str) -> Option<&ActionSig> {
        self.actions.get(name)
    }

    // === Functions ===

    /// Define a user-defined function.
    pub fn define_func(&mut self, name: String, param_names: Vec<String>, param_types: Vec<Type>) {
        self.funcs.insert(
            name,
            FuncInfo {
                param_names,
                param_types,
            },
        );
    }

    /// Look up a function.
    pub fn lookup_func(&self, name: &str) -> Option<&FuncInfo> {
        self.funcs.get(name)
    }

    // === Unified lookup ===

    /// Look up any identifier (local, const, or var).
    pub fn lookup_ident(&self, name: &str) -> Option<&Type> {
        // Check local bindings first
        if let Some(ty) = self.lookup_local(name) {
            return Some(ty);
        }
        // Then constants
        if let Some(ty) = self.lookup_const(name) {
            return Some(ty);
        }
        // Then state variables
        self.lookup_var(name)
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scope_shadowing() {
        let mut env = TypeEnv::new();
        env.bind_local("x".to_string(), Type::Nat);

        env.push_scope();
        env.bind_local("x".to_string(), Type::Bool);

        assert_eq!(env.lookup_local("x"), Some(&Type::Bool));

        env.pop_scope();
        assert_eq!(env.lookup_local("x"), Some(&Type::Nat));
    }

    #[test]
    fn test_type_resolution() {
        let mut env = TypeEnv::new();
        env.define_type_alias("Counter".to_string(), Type::Nat);
        env.define_type_alias(
            "CounterSet".to_string(),
            Type::Set(Box::new(Type::Named("Counter".to_string()))),
        );

        let resolved = env.resolve_type(&Type::Named("CounterSet".to_string()));
        assert_eq!(resolved, Type::Set(Box::new(Type::Nat)));
    }

    #[test]
    fn test_unified_lookup() {
        let mut env = TypeEnv::new();
        env.define_const("MAX".to_string(), Type::Nat);
        env.define_var("count".to_string(), Type::Int);
        env.bind_local("x".to_string(), Type::Bool);

        assert_eq!(env.lookup_ident("MAX"), Some(&Type::Nat));
        assert_eq!(env.lookup_ident("count"), Some(&Type::Int));
        assert_eq!(env.lookup_ident("x"), Some(&Type::Bool));
        assert_eq!(env.lookup_ident("unknown"), None);
    }
}
