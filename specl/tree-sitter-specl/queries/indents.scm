; Specl indentation queries

; Blocks increase indent
[
  (block)
  (action_body)
  (record_type)
  (record_lit)
  (set_lit)
  (seq_lit)
  (param_list)
] @indent

; Closing brackets decrease indent
[
  "}"
  "]"
  ")"
] @outdent

; These keywords should be aligned
[
  "then"
  "else"
  "in"
] @branch
