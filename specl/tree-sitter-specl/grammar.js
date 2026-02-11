/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

/**
 * Tree-sitter grammar for Specl specification language.
 */
module.exports = grammar({
  name: "specl",

  extras: ($) => [/\s/, $.comment],

  word: ($) => $.identifier,

  conflicts: ($) => [],

  rules: {
    // ==================== Module ====================
    source_file: ($) => seq($.module_decl, repeat($.declaration)),

    module_decl: ($) => seq("module", field("name", $.identifier)),

    // ==================== Declarations ====================
    declaration: ($) =>
      choice(
        $.const_decl,
        $.var_decl,
        $.type_decl,
        $.action_decl,
        $.init_decl,
        $.invariant_decl,
        $.property_decl,
        $.fairness_decl,
        $.use_decl
      ),

    const_decl: ($) =>
      seq("const", field("name", $.identifier), ":", field("type", $.type_expr)),

    var_decl: ($) =>
      seq("var", field("name", $.identifier), ":", field("type", $.type_expr)),

    type_decl: ($) =>
      seq("type", field("name", $.identifier), "=", field("type", $.type_expr)),

    action_decl: ($) =>
      seq(
        "action",
        field("name", $.identifier),
        $.param_list,
        $.action_body
      ),

    param_list: ($) =>
      seq("(", optional(seq($.param, repeat(seq(",", $.param)))), ")"),

    param: ($) =>
      seq(field("name", $.identifier), ":", field("type", $.type_expr)),

    action_body: ($) =>
      seq("{", repeat($.action_statement), optional($.expression), "}"),

    action_statement: ($) => choice($.require_stmt),

    require_stmt: ($) => seq("require", $.expression),

    init_decl: ($) => seq("init", $.block),

    block: ($) => seq("{", $.expression, "}"),

    invariant_decl: ($) =>
      seq("invariant", field("name", $.identifier), $.block),

    property_decl: ($) =>
      seq("property", field("name", $.identifier), $.block),

    fairness_decl: ($) =>
      seq("fairness", "{", repeat($.fairness_constraint), "}"),

    fairness_constraint: ($) =>
      seq(
        choice("weak", "strong"),
        field("action", $.identifier),
        optional($.param_list)
      ),

    use_decl: ($) => seq("use", $.module_path),

    module_path: ($) => seq($.identifier, repeat(seq(".", $.identifier))),

    // ==================== Types ====================
    type_expr: ($) =>
      choice(
        $.primitive_type,
        $.generic_type,
        $.record_type,
        $.tuple_type,
        $.range_type,
        $.named_type
      ),

    primitive_type: ($) => choice("Bool", "Nat", "Int", "String"),

    generic_type: ($) =>
      seq(
        field("name", choice("Set", "Seq", "Fn", "Option")),
        "[",
        field("args", $.type_args),
        "]"
      ),

    type_args: ($) => seq($.type_expr, repeat(seq(",", $.type_expr))),

    record_type: ($) =>
      seq("{", optional(seq($.field_decl, repeat(seq(",", $.field_decl)))), "}"),

    field_decl: ($) =>
      seq(field("name", $.identifier), ":", field("type", $.type_expr)),

    range_type: ($) =>
      seq(
        field("lo", choice($.integer, $.identifier)),
        "..",
        field("hi", choice($.integer, $.identifier))
      ),

    tuple_type: ($) =>
      seq(
        "(",
        field("first", $.type_expr),
        ",",
        field("rest", $.type_expr),
        repeat(seq(",", $.type_expr)),
        ")"
      ),

    named_type: ($) => $.identifier,

    // ==================== Expressions ====================
    expression: ($) => $.or_expr,

    or_expr: ($) =>
      prec.left(
        1,
        seq($.and_expr, repeat(seq(choice("or", "=>", "<=>"), $.and_expr)))
      ),

    and_expr: ($) =>
      prec.left(2, seq($.assignment_expr, repeat(seq("and", $.assignment_expr)))),

    // Assignment: x = value (for next-state updates)
    assignment_expr: ($) =>
      choice(
        seq(field("var", $.identifier), "=", field("value", $.comparison_expr)),
        $.comparison_expr
      ),

    comparison_expr: ($) =>
      prec.left(
        3,
        seq(
          $.membership_expr,
          repeat(
            seq(choice("==", "!=", "<", "<=", ">", ">="), $.membership_expr)
          )
        )
      ),

    membership_expr: ($) =>
      prec.left(
        4,
        seq($.additive_expr, repeat(seq(choice("in", "not in", "subset"), $.additive_expr)))
      ),

    additive_expr: ($) =>
      prec.left(
        5,
        seq(
          $.multiplicative_expr,
          repeat(seq(choice("+", "-", "++", "union", "\\"), $.multiplicative_expr))
        )
      ),

    multiplicative_expr: ($) =>
      prec.left(
        6,
        seq($.unary_expr, repeat(seq(choice("*", "/", "%", "intersect"), $.unary_expr)))
      ),

    unary_expr: ($) =>
      choice(seq(choice("not", "-"), $.unary_expr), $.postfix_expr),

    postfix_expr: ($) =>
      prec.left(
        8,
        seq(
          $.primary_expr,
          repeat(
            choice(
              seq("[", $.expression, "]"),
              seq("[", $.expression, "..", $.expression, "]"),
              seq(".", $.identifier),
              seq("(", optional($.argument_list), ")")
            )
          )
        )
      ),

    primary_expr: ($) =>
      choice(
        $.identifier,
        $.integer,
        $.string,
        $.boolean,
        $.set_lit,
        $.seq_lit,
        $.record_lit,
        $.fn_lit,
        $.set_comprehension,
        $.quantifier_expr,
        $.choose_expr,
        $.let_expr,
        $.if_expr,
        $.changes_expr,
        $.enabled_expr,
        $.head_expr,
        $.tail_expr,
        $.len_expr,
        $.keys_expr,
        $.values_expr,
        $.always_expr,
        $.eventually_expr,
        $.leads_to_expr,
        $.tuple_lit,
        $.paren_expr
      ),

    integer: ($) => /\d+/,

    string: ($) =>
      seq('"', repeat(choice(/[^"\\]+/, seq("\\", /./))), '"'),

    boolean: ($) => choice("true", "false"),

    set_lit: ($) =>
      seq("{", optional(seq($.expression, repeat(seq(",", $.expression)))), "}"),

    seq_lit: ($) =>
      seq("[", optional(seq($.expression, repeat(seq(",", $.expression)))), "]"),

    record_lit: ($) =>
      seq(
        "{",
        $.field_assign,
        repeat(seq(",", $.field_assign)),
        optional(","),
        "}"
      ),

    field_assign: ($) =>
      seq(field("name", $.identifier), ":", field("value", $.expression)),

    fn_lit: ($) =>
      seq(
        choice("fn", "Fn"),
        "(",
        field("var", $.identifier),
        "in",
        field("domain", $.expression),
        ")",
        "=>",
        field("body", $.expression)
      ),

    set_comprehension: ($) =>
      seq(
        "{",
        field("element", $.expression),
        "for",
        field("var", $.identifier),
        "in",
        field("domain", $.expression),
        optional(seq("if", field("filter", $.expression))),
        "}"
      ),

    quantifier_expr: ($) =>
      seq(
        field("quantifier", choice("all", "any", "forall", "exists")),
        field("var", $.identifier),
        "in",
        field("domain", $.expression),
        ":",
        field("body", $.expression)
      ),

    choose_expr: ($) =>
      seq(
        "choose",
        field("var", $.identifier),
        "in",
        field("domain", $.expression),
        ":",
        field("predicate", $.expression)
      ),

    let_expr: ($) =>
      seq(
        "let",
        field("name", $.identifier),
        "=",
        field("value", $.expression),
        "in",
        field("body", $.expression)
      ),

    if_expr: ($) =>
      seq(
        "if",
        field("condition", $.expression),
        "then",
        field("then", $.expression),
        "else",
        field("else", $.expression)
      ),

    changes_expr: ($) => seq("changes", "(", $.identifier, ")"),

    enabled_expr: ($) => seq("enabled", "(", $.identifier, ")"),

    head_expr: ($) => seq("head", "(", $.expression, ")"),

    tail_expr: ($) => seq("tail", "(", $.expression, ")"),

    len_expr: ($) => seq("len", "(", $.expression, ")"),

    keys_expr: ($) => seq("keys", "(", $.expression, ")"),

    values_expr: ($) => seq("values", "(", $.expression, ")"),

    always_expr: ($) => seq("always", $.paren_expr),

    eventually_expr: ($) => seq("eventually", $.paren_expr),

    leads_to_expr: ($) => seq($.paren_expr, "leads_to", $.paren_expr),

    paren_expr: ($) => seq("(", $.expression, ")"),

    tuple_lit: ($) =>
      seq(
        "(",
        field("first", $.expression),
        ",",
        field("second", $.expression),
        repeat(seq(",", $.expression)),
        ")"
      ),

    argument_list: ($) => seq($.expression, repeat(seq(",", $.expression))),

    // ==================== Identifiers and Comments ====================
    identifier: ($) => /[a-zA-Z_][a-zA-Z0-9_]*/,

    comment: ($) =>
      token(
        choice(seq("//", /[^\n]*/), seq("/*", /[^*]*\*+([^/*][^*]*\*+)*/, "/"))
      ),
  },
});
