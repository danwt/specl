; Specl syntax highlighting queries

; Keywords
[
  "module"
  "const"
  "var"
  "type"
  "action"
  "init"
  "invariant"
  "property"
  "fairness"
  "use"
  "require"
  "weak"
  "strong"
] @keyword

; Control flow
[
  "if"
  "then"
  "else"
  "let"
  "in"
  "for"
] @keyword.control

; Quantifiers
[
  "all"
  "any"
  "forall"
  "exists"
  "fix"
] @keyword.control

; Temporal operators
[
  "always"
  "eventually"
  "leads_to"
] @keyword.control

; Special expressions
[
  "changes"
  "enabled"
  "head"
  "tail"
  "len"
] @keyword.function

; Logical operators
[
  "and"
  "or"
  "not"
  "=>"
  "<=>"
] @keyword.operator

; Set operators
[
  "union"
  "intersect"
  "diff"
  "subset_of"
] @keyword.operator

; Membership
"in" @keyword.operator
"not in" @keyword.operator

; Types
(primitive_type) @type.builtin

[
  "Set"
  "Seq"
  "Fn"
  "Option"
] @type.builtin

(named_type (identifier) @type)

; Booleans
(boolean) @constant.builtin

; Numbers
(integer) @number

; Strings
(string) @string

; Identifiers
(identifier) @variable

; Function/action names
(action_decl name: (identifier) @function)
(invariant_decl name: (identifier) @function)
(property_decl name: (identifier) @function)

; Module name
(module_decl name: (identifier) @namespace)

; Parameters
(param name: (identifier) @variable.parameter)

; Field names
(field_decl name: (identifier) @property)
(field_assign name: (identifier) @property)

; Assignment (next-state update)
(assignment_expr var: (identifier) @variable)
(assignment_expr "=" @operator)

; Operators
[
  "+"
  "-"
  "*"
  "/"
  "%"
  "++"
  "\\"
  "=="
  "!="
  "<"
  "<="
  ">"
  ">="
  ".."
  "=>"
  "<=>"
] @operator

; Punctuation
[
  "("
  ")"
  "["
  "]"
  "{"
  "}"
] @punctuation.bracket

[
  ","
  ":"
  "."
] @punctuation.delimiter

; Comments
(comment) @comment
