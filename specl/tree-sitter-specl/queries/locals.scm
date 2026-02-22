; Specl locals queries for scope tracking

; Module is a scope
(source_file) @scope

; Action bodies introduce a scope
(action_body) @scope

; Blocks introduce a scope
(block) @scope

; Let expressions introduce a scope
(let_expr) @scope

; Quantifiers introduce a scope
(quantifier_expr) @scope

; Choose expressions introduce a scope
(choose_expr) @scope

; Set comprehensions introduce a scope
(set_comprehension) @scope

; Function literals introduce a scope
(fn_lit) @scope

; Variable definitions
(var_decl name: (identifier) @definition.var)
(const_decl name: (identifier) @definition.constant)

; Parameters are definitions
(param name: (identifier) @definition.parameter)

; Let bindings are definitions
(let_expr name: (identifier) @definition.var)

; Quantifier variables are definitions
(quantifier_expr var: (identifier) @definition.var)

; Choose variables are definitions
(choose_expr var: (identifier) @definition.var)

; Set comprehension variables are definitions
(set_comprehension var: (identifier) @definition.var)

; Function literal variables are definitions
(fn_lit var: (identifier) @definition.var)

; Type definitions
(type_decl name: (identifier) @definition.type)

; Action definitions
(action_decl name: (identifier) @definition.function)

; Invariant definitions
(invariant_decl name: (identifier) @definition.function)

; Property definitions
(property_decl name: (identifier) @definition.function)

; References
(identifier) @reference
