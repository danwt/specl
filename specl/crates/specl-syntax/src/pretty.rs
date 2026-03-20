//! Pretty printer for the Specl AST.

use crate::ast::*;
use std::fmt::Write;

/// Pretty print a module to a string.
pub fn pretty_print(module: &Module) -> String {
    let mut printer = PrettyPrinter::new();
    printer.print_module(module);
    printer.output
}

/// Pretty print an expression to a string.
pub fn pretty_print_expr(expr: &Expr) -> String {
    let mut printer = PrettyPrinter::new();
    printer.print_expr(expr);
    printer.output
}

/// Pretty print a type expression to a string.
pub fn pretty_print_type(ty: &TypeExpr) -> String {
    let mut printer = PrettyPrinter::new();
    printer.print_type_expr(ty);
    printer.output
}

/// Pretty print a const value to a string.
pub fn pretty_print_const_value(value: &ConstValue) -> String {
    match value {
        ConstValue::Type(ty) => pretty_print_type(ty),
        ConstValue::Scalar(n) => n.to_string(),
    }
}

struct PrettyPrinter {
    output: String,
    indent: usize,
}

impl PrettyPrinter {
    fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
        }
    }

    fn write(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn writeln(&mut self, s: &str) {
        self.output.push_str(s);
        self.output.push('\n');
    }

    fn newline(&mut self) {
        self.output.push('\n');
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
    }

    fn print_module(&mut self, module: &Module) {
        self.write("module ");
        self.writeln(&module.name.name);

        for decl in &module.decls {
            self.newline();
            self.print_decl(decl);
        }
    }

    fn print_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Use(d) => self.print_use_decl(d),
            Decl::Const(d) => self.print_const_decl(d),
            Decl::Var(d) => self.print_var_decl(d),
            Decl::Type(d) => self.print_type_decl(d),
            Decl::Func(d) => self.print_func_decl(d),
            Decl::Init(d) => self.print_init_decl(d),
            Decl::Action(d) => self.print_action_decl(d),
            Decl::Invariant(d) => self.print_invariant_decl(d),
            Decl::Property(d) => self.print_property_decl(d),
            Decl::Fairness(d) => self.print_fairness_decl(d),
            Decl::View(d) => self.print_view_decl(d),
        }
    }

    fn print_view_decl(&mut self, decl: &ViewDecl) {
        self.write("view { ");
        for (i, var) in decl.variables.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&var.name);
        }
        self.writeln(" }");
    }

    fn print_use_decl(&mut self, decl: &UseDecl) {
        self.write("use ");
        self.writeln(&decl.module.name);
    }

    fn print_const_decl(&mut self, decl: &ConstDecl) {
        self.write("const ");
        self.write(&decl.name.name);
        self.write(": ");
        match &decl.value {
            ConstValue::Type(ty) => self.print_type_expr(ty),
            ConstValue::Scalar(n) => self.write(&n.to_string()),
        }
        if let Some(default) = decl.default_value {
            self.write(" = ");
            self.write(&default.to_string());
        }
        self.newline();
    }

    fn print_var_decl(&mut self, decl: &VarDecl) {
        self.write("var ");
        self.write(&decl.name.name);
        self.write(": ");
        self.print_type_expr(&decl.ty);
        self.newline();
    }

    fn print_type_decl(&mut self, decl: &TypeDecl) {
        self.write("type ");
        self.write(&decl.name.name);
        self.write(" = ");
        self.print_type_expr(&decl.ty);
        self.newline();
    }

    fn print_init_decl(&mut self, decl: &InitDecl) {
        self.writeln("init {");
        self.indent += 1;
        self.print_semicolon_statements(&decl.body);
        self.indent -= 1;
        self.writeln("}");
    }

    fn print_func_decl(&mut self, decl: &FuncDecl) {
        self.write("func ");
        self.write(&decl.name.name);
        self.write("(");
        for (i, param) in decl.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&param.name.name);
        }
        self.writeln(") {");
        self.indent += 1;
        self.write_indent();
        self.print_expr(&decl.body);
        self.newline();
        self.indent -= 1;
        self.writeln("}");
    }

    fn print_action_decl(&mut self, decl: &ActionDecl) {
        self.write("action ");
        self.write(&decl.name.name);
        self.write("(");
        for (i, param) in decl.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&param.name.name);
            self.write(": ");
            self.print_type_expr(&param.ty);
        }
        self.writeln(") {");
        self.indent += 1;

        for req in &decl.body.requires {
            self.write_indent();
            self.write("require ");
            self.print_expr(req);
            self.writeln(";");
        }

        if let Some(effect) = &decl.body.effect {
            self.print_semicolon_statements(effect);
        }

        self.indent -= 1;
        self.writeln("}");
    }

    /// Print statements separated by semicolons, splitting AND conjunctions into separate lines.
    fn print_semicolon_statements(&mut self, expr: &Expr) {
        let mut stmts = Vec::new();
        Self::collect_and_leaves(expr, &mut stmts);

        for stmt in &stmts {
            self.write_indent();
            self.print_expr(stmt);
            self.writeln(";");
        }
    }

    /// Collect leaf expressions from a conjunction (AND) tree.
    fn collect_and_leaves<'a>(expr: &'a Expr, leaves: &mut Vec<&'a Expr>) {
        if let ExprKind::Binary {
            op: BinOp::And,
            left,
            right,
        } = &expr.kind
        {
            Self::collect_and_leaves(left, leaves);
            Self::collect_and_leaves(right, leaves);
        } else {
            leaves.push(expr);
        }
    }

    fn print_invariant_decl(&mut self, decl: &InvariantDecl) {
        if decl.is_auxiliary {
            self.write("auxiliary ");
        }
        self.write("invariant ");
        self.write(&decl.name.name);
        self.writeln(" {");
        self.indent += 1;
        self.write_indent();
        self.print_expr(&decl.body);
        self.newline();
        self.indent -= 1;
        self.writeln("}");
    }

    fn print_property_decl(&mut self, decl: &PropertyDecl) {
        self.write("property ");
        self.write(&decl.name.name);
        self.writeln(" {");
        self.indent += 1;
        self.write_indent();
        self.print_expr(&decl.body);
        self.newline();
        self.indent -= 1;
        self.writeln("}");
    }

    fn print_fairness_decl(&mut self, decl: &FairnessDecl) {
        self.writeln("fairness {");
        self.indent += 1;
        for constraint in &decl.constraints {
            self.write_indent();
            match constraint.kind {
                FairnessKind::Weak => self.write("weak_fair("),
                FairnessKind::Strong => self.write("strong_fair("),
            }
            self.write(&constraint.action.name);
            self.writeln(")");
        }
        self.indent -= 1;
        self.writeln("}");
    }

    fn print_type_expr(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Named(id) => self.write(&id.name),
            TypeExpr::Set(inner, _) => {
                self.write("Set[");
                self.print_type_expr(inner);
                self.write("]");
            }
            TypeExpr::Seq(inner, _) => {
                self.write("Seq[");
                self.print_type_expr(inner);
                self.write("]");
            }
            TypeExpr::Dict(key, value, _) => {
                self.write("Dict[");
                self.print_type_expr(key);
                self.write(", ");
                self.print_type_expr(value);
                self.write("]");
            }
            TypeExpr::Option(inner, _) => {
                self.write("Option[");
                self.print_type_expr(inner);
                self.write("]");
            }
            TypeExpr::Range(lo, hi, _) => {
                self.print_expr(lo);
                self.write("..");
                self.print_expr(hi);
            }
        }
    }

    fn print_expr(&mut self, expr: &Expr) {
        self.print_expr_kind(&expr.kind);
    }

    fn print_expr_kind(&mut self, kind: &ExprKind) {
        match kind {
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::Int(n) => {
                let _ = write!(self.output, "{}", n);
            }
            ExprKind::String(s) => {
                self.write("\"");
                for c in s.chars() {
                    match c {
                        '\\' => self.write("\\\\"),
                        '"' => self.write("\\\""),
                        '\n' => self.write("\\n"),
                        '\t' => self.write("\\t"),
                        '\r' => self.write("\\r"),
                        _ => self.output.push(c),
                    }
                }
                self.write("\"");
            }
            ExprKind::Ident(name) => {
                self.write(name);
            }
            ExprKind::Primed(name) => {
                self.write(name);
                self.write("'");
            }
            ExprKind::Binary { op, left, right } => {
                // Handle assignment syntax: x' == e prints as x = e
                if *op == BinOp::Eq {
                    if let ExprKind::Primed(name) = &left.kind {
                        self.write(name);
                        self.write(" = ");
                        self.print_expr(right);
                        return;
                    }
                }
                self.print_expr(left);
                self.write(" ");
                self.print_binop(*op);
                self.write(" ");
                self.print_expr(right);
            }
            ExprKind::Unary { op, operand } => {
                self.print_unaryop(*op);
                self.print_expr(operand);
            }
            ExprKind::Index { base, index } => {
                self.print_expr(base);
                self.write("[");
                self.print_expr(index);
                self.write("]");
            }
            ExprKind::Slice { base, lo, hi } => {
                self.print_expr(base);
                self.write("[");
                self.print_expr(lo);
                self.write("..");
                self.print_expr(hi);
                self.write("]");
            }
            ExprKind::Field { base, field } => {
                self.print_expr(base);
                self.write(".");
                self.write(&field.name);
            }
            ExprKind::Call { func, args } => {
                self.print_expr(func);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(arg);
                }
                self.write(")");
            }
            ExprKind::SetLit(elements) => {
                self.write("{");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(elem);
                }
                self.write("}");
            }
            ExprKind::SeqLit(elements) => {
                self.write("[");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(elem);
                }
                self.write("]");
            }
            ExprKind::DictLit(entries) => {
                if entries.is_empty() {
                    self.write("{:}");
                } else {
                    self.write("{ ");
                    for (i, (key, value)) in entries.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.print_expr(key);
                        self.write(": ");
                        self.print_expr(value);
                    }
                    self.write(" }");
                }
            }
            ExprKind::FnLit { var, domain, body } => {
                self.write("{ ");
                self.write(&var.name);
                self.write(": ");
                self.print_expr(body);
                self.write(" for ");
                self.write(&var.name);
                self.write(" in ");
                self.print_expr(domain);
                self.write(" }");
            }
            ExprKind::SetComprehension {
                element,
                var,
                domain,
                filter,
            } => {
                self.write("{ ");
                self.print_expr(element);
                self.write(" for ");
                self.write(&var.name);
                self.write(" in ");
                self.print_expr(domain);
                if let Some(f) = filter {
                    self.write(" if ");
                    self.print_expr(f);
                }
                self.write(" }");
            }
            ExprKind::Quantifier {
                kind,
                bindings,
                body,
            } => {
                match kind {
                    QuantifierKind::Forall => self.write("all "),
                    QuantifierKind::Exists => self.write("any "),
                }
                for (i, binding) in bindings.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&binding.var.name);
                    self.write(" in ");
                    self.print_expr(&binding.domain);
                }
                self.write(": ");
                self.print_expr(body);
            }
            ExprKind::Fix {
                var,
                domain,
                predicate,
            } => {
                self.write("fix ");
                self.write(&var.name);
                if let Some(domain) = domain {
                    self.write(" in ");
                    self.print_expr(domain);
                }
                self.write(": ");
                self.print_expr(predicate);
            }
            ExprKind::Let { var, value, body } => {
                self.write("let ");
                self.write(&var.name);
                self.write(" = ");
                self.print_expr(value);
                self.write(" in ");
                self.print_expr(body);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.write("if ");
                self.print_expr(cond);
                self.write(" then ");
                self.print_expr(then_branch);
                self.write(" else ");
                self.print_expr(else_branch);
            }
            ExprKind::Require(expr) => {
                self.write("require ");
                self.print_expr(expr);
            }
            ExprKind::Changes(var) => {
                self.write("changes(");
                self.write(&var.name);
                self.write(")");
            }
            ExprKind::Enabled(action) => {
                self.write("enabled(");
                self.write(&action.name);
                self.write(")");
            }
            ExprKind::SeqHead(seq) => {
                self.write("head(");
                self.print_expr(seq);
                self.write(")");
            }
            ExprKind::SeqTail(seq) => {
                self.write("tail(");
                self.print_expr(seq);
                self.write(")");
            }
            ExprKind::Len(expr) => {
                self.write("len(");
                self.print_expr(expr);
                self.write(")");
            }
            ExprKind::Keys(expr) => {
                self.write("keys(");
                self.print_expr(expr);
                self.write(")");
            }
            ExprKind::Values(expr) => {
                self.write("values(");
                self.print_expr(expr);
                self.write(")");
            }
            ExprKind::BigUnion(expr) => {
                self.write("union_all(");
                self.print_expr(expr);
                self.write(")");
            }
            ExprKind::Powerset(expr) => {
                self.write("powerset(");
                self.print_expr(expr);
                self.write(")");
            }
            ExprKind::Always(expr) => {
                self.write("always ");
                self.print_expr(expr);
            }
            ExprKind::Eventually(expr) => {
                self.write("eventually ");
                self.print_expr(expr);
            }
            ExprKind::LeadsTo { left, right } => {
                self.print_expr(left);
                self.write(" leads_to ");
                self.print_expr(right);
            }
            ExprKind::Range { lo, hi } => {
                self.print_expr(lo);
                self.write("..");
                self.print_expr(hi);
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.print_expr(inner);
                self.write(")");
            }
        }
    }

    fn print_binop(&mut self, op: BinOp) {
        let s = match op {
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Implies => "implies",
            BinOp::Iff => "iff",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::In => "in",
            BinOp::NotIn => "not in",
            BinOp::Union => "union",
            BinOp::Intersect => "intersect",
            BinOp::Diff => "diff",
            BinOp::SubsetOf => "subset_of",
            BinOp::Concat => "++",
        };
        self.write(s);
    }

    fn print_unaryop(&mut self, op: UnaryOp) {
        let s = match op {
            UnaryOp::Not => "not ",
            UnaryOp::Neg => "-",
        };
        self.write(s);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    /// Parse source, pretty-print, re-parse, pretty-print again. Both outputs must match.
    fn assert_roundtrip(source: &str) {
        let m1 =
            parse(source).unwrap_or_else(|e| panic!("first parse failed: {e}\nsource:\n{source}"));
        let p1 = pretty_print(&m1);
        let m2 = parse(&p1).unwrap_or_else(|e| panic!("second parse failed: {e}\npretty:\n{p1}"));
        let p2 = pretty_print(&m2);
        assert_eq!(p1, p2, "roundtrip mismatch:\nfirst:\n{p1}\nsecond:\n{p2}");
    }

    #[test]
    fn test_pretty_print_simple() {
        let source = "module Test\nvar x: Nat\ninit { x == 0 }";
        let module = parse(source).unwrap();
        let output = pretty_print(&module);
        assert!(output.contains("module Test"));
        assert!(output.contains("var x: Nat"));
        assert!(output.contains("x == 0"));
    }

    #[test]
    fn test_pretty_print_action() {
        let source = r#"
module Test
action Foo(a: Nat, b: Bool) {
    require a > 0
    b = true
}
"#;
        let module = parse(source).unwrap();
        let output = pretty_print(&module);
        assert!(output.contains("action Foo(a: Nat, b: Bool)"));
        assert!(output.contains("require a > 0"));
    }

    #[test]
    fn test_pretty_print_expr() {
        let source = "module Test\ninit { x + y * z }";
        let module = parse(source).unwrap();
        if let Decl::Init(init) = &module.decls[0] {
            let output = pretty_print_expr(&init.body);
            assert!(output.contains("+"));
            assert!(output.contains("*"));
        }
    }

    #[test]
    fn test_roundtrip_empty_set_literal() {
        assert_roundtrip("module T\ninit { x = {} }");
    }

    #[test]
    fn test_roundtrip_empty_seq_literal() {
        assert_roundtrip("module T\ninit { x = [] }");
    }

    #[test]
    fn test_roundtrip_empty_dict_literal() {
        assert_roundtrip("module T\ninit { x = {:} }");
    }

    #[test]
    fn test_roundtrip_set_literal() {
        assert_roundtrip("module T\ninit { x = {1, 2, 3} }");
    }

    #[test]
    fn test_roundtrip_seq_literal() {
        assert_roundtrip("module T\ninit { x = [1, 2, 3] }");
    }

    #[test]
    fn test_roundtrip_dict_literal() {
        assert_roundtrip("module T\ninit { x = {0: 1, 1: 2} }");
    }

    #[test]
    fn test_roundtrip_set_comprehension() {
        assert_roundtrip("module T\ninit { x = {y + 1 for y in 0..3} }");
    }

    #[test]
    fn test_roundtrip_set_comprehension_with_filter() {
        assert_roundtrip("module T\ninit { x = {y in 0..5 if y > 2} }");
    }

    #[test]
    fn test_roundtrip_dict_comprehension() {
        assert_roundtrip("module T\ninit { x = {k: 0 for k in 0..3} }");
    }

    #[test]
    fn test_roundtrip_quantifiers() {
        assert_roundtrip(
            "module T\nvar x: Set[0..3]\ninvariant Inv { all k in 0..3: k in x implies k >= 0 }",
        );
    }

    #[test]
    fn test_roundtrip_exists_quantifier() {
        assert_roundtrip("module T\nvar x: Set[0..3]\ninvariant Inv { any k in 0..3: k in x }");
    }

    #[test]
    fn test_roundtrip_nested_quantifiers() {
        assert_roundtrip(
            "module T\nvar x: 0..3\ninvariant Inv { all a in 0..3: all b in 0..3: a + b >= 0 }",
        );
    }

    #[test]
    fn test_roundtrip_let_in() {
        assert_roundtrip("module T\ninvariant Inv { let x = 1 in x + 2 }");
    }

    #[test]
    fn test_roundtrip_nested_let_in() {
        assert_roundtrip("module T\ninvariant Inv { let x = 1 in let y = 2 in x + y }");
    }

    #[test]
    fn test_roundtrip_if_then_else() {
        assert_roundtrip("module T\ninit { x = if true then 1 else 2 }");
    }

    #[test]
    fn test_roundtrip_fix() {
        assert_roundtrip("module T\ninvariant Inv { (fix w in 0..3 : w > 1) >= 0 }");
    }

    #[test]
    fn test_roundtrip_unary_not() {
        assert_roundtrip("module T\ninvariant Inv { not false }");
    }

    #[test]
    fn test_roundtrip_unary_neg() {
        assert_roundtrip("module T\ninit { x = -1 }");
    }

    #[test]
    fn test_roundtrip_index() {
        assert_roundtrip("module T\ninit { x = d[0] }");
    }

    #[test]
    fn test_roundtrip_slice() {
        assert_roundtrip("module T\ninit { x = s[0..2] }");
    }

    #[test]
    fn test_roundtrip_field_access() {
        assert_roundtrip("module T\ninit { x = r.field }");
    }

    #[test]
    fn test_roundtrip_func_call() {
        assert_roundtrip("module T\nfunc F(a, b) { a + b }\ninit { x = F(1, 2) }");
    }

    #[test]
    fn test_roundtrip_range_expr() {
        assert_roundtrip("module T\ninvariant Inv { all k in 0..5: k >= 0 }");
    }

    #[test]
    fn test_roundtrip_paren() {
        assert_roundtrip("module T\ninit { x = (1 + 2) * 3 }");
    }

    #[test]
    fn test_roundtrip_temporal_always() {
        assert_roundtrip("module T\nproperty P { always true }");
    }

    #[test]
    fn test_roundtrip_temporal_eventually() {
        assert_roundtrip("module T\nproperty P { eventually true }");
    }

    #[test]
    fn test_roundtrip_temporal_leads_to() {
        assert_roundtrip("module T\nproperty P { true leads_to false }");
    }

    #[test]
    fn test_roundtrip_string_escaping() {
        let source = r#"module T
init { x = "hello \"world\"\n\t\\" }"#;
        let m1 = parse(source).unwrap();
        let p1 = pretty_print(&m1);
        assert!(
            p1.contains(r#""hello \"world\"\n\t\\""#),
            "expected escaped string in output, got: {p1}"
        );
        assert_roundtrip(source);
    }

    #[test]
    fn test_roundtrip_string_simple() {
        assert_roundtrip(
            r#"module T
init { x = "hello" }"#,
        );
    }

    #[test]
    fn test_roundtrip_fairness() {
        assert_roundtrip(
            "module T\nvar x: 0..1\naction A() { x = x }\nfairness {\n    weak_fair(A)\n}",
        );
    }

    #[test]
    fn test_roundtrip_fairness_strong() {
        assert_roundtrip(
            "module T\nvar x: 0..1\naction A() { x = x }\nfairness {\n    strong_fair(A)\n}",
        );
    }

    #[test]
    fn test_roundtrip_view_decl() {
        assert_roundtrip("module T\nvar x: Nat\nvar y: Nat\nview { x, y }");
    }

    #[test]
    fn test_roundtrip_use_decl() {
        assert_roundtrip("module T\nuse Other");
    }

    #[test]
    fn test_roundtrip_const_scalar() {
        assert_roundtrip("module T\nconst N: 5");
    }

    #[test]
    fn test_roundtrip_const_type() {
        assert_roundtrip("module T\nconst N: Nat");
    }

    #[test]
    fn test_roundtrip_const_range() {
        assert_roundtrip("module T\nconst N: 0..10");
    }

    #[test]
    fn test_roundtrip_const_with_default() {
        assert_roundtrip("module T\nconst N: Nat = 5");
    }

    #[test]
    fn test_roundtrip_type_decl() {
        assert_roundtrip("module T\ntype AccountId = 0..10");
    }

    #[test]
    fn test_roundtrip_type_set() {
        assert_roundtrip("module T\nvar x: Set[Nat]");
    }

    #[test]
    fn test_roundtrip_type_seq() {
        assert_roundtrip("module T\nvar x: Seq[Bool]");
    }

    #[test]
    fn test_roundtrip_type_dict() {
        assert_roundtrip("module T\nvar x: Dict[Nat, Bool]");
    }

    #[test]
    fn test_roundtrip_type_option() {
        assert_roundtrip("module T\nvar x: Option[Nat]");
    }

    #[test]
    fn test_roundtrip_auxiliary_invariant() {
        assert_roundtrip("module T\nauxiliary invariant Helper { true }");
    }

    #[test]
    fn test_roundtrip_property() {
        assert_roundtrip("module T\nproperty Liveness { always eventually true }");
    }

    #[test]
    fn test_roundtrip_changes() {
        assert_roundtrip("module T\nvar x: 0..1\naction A() { changes(x) }");
    }

    #[test]
    fn test_roundtrip_enabled() {
        assert_roundtrip(
            "module T\nvar x: 0..1\naction A() { x = x }\ninvariant Inv { enabled(A) }",
        );
    }

    #[test]
    fn test_roundtrip_builtins() {
        assert_roundtrip("module T\nvar s: Seq[Nat]\ninvariant Inv { len(s) >= 0 }");
        assert_roundtrip(
            "module T\nvar s: Seq[Nat]\ninvariant Inv { len(s) > 0 implies head(s) >= 0 }",
        );
        assert_roundtrip("module T\nvar d: Dict[Nat, Nat]\ninvariant Inv { len(keys(d)) >= 0 }");
        assert_roundtrip(
            "module T\nvar d: Dict[Nat, Nat]\ninvariant Inv { all v in values(d): v >= 0 }",
        );
        assert_roundtrip(
            "module T\nvar s: Set[Set[Nat]]\ninvariant Inv { len(union_all(s)) >= 0 }",
        );
        assert_roundtrip("module T\nvar s: Set[Nat]\ninvariant Inv { s in powerset(0..5) }");
    }

    #[test]
    fn test_roundtrip_binary_operators() {
        assert_roundtrip("module T\ninvariant Inv { true and false }");
        assert_roundtrip("module T\ninvariant Inv { true or false }");
        assert_roundtrip("module T\ninvariant Inv { true implies false }");
        assert_roundtrip("module T\ninvariant Inv { true iff false }");
        assert_roundtrip("module T\ninvariant Inv { 1 == 1 }");
        assert_roundtrip("module T\ninvariant Inv { 1 != 2 }");
        assert_roundtrip("module T\ninvariant Inv { 1 < 2 }");
        assert_roundtrip("module T\ninvariant Inv { 1 <= 2 }");
        assert_roundtrip("module T\ninvariant Inv { 2 > 1 }");
        assert_roundtrip("module T\ninvariant Inv { 2 >= 1 }");
        assert_roundtrip("module T\ninvariant Inv { 1 + 2 }");
        assert_roundtrip("module T\ninvariant Inv { 3 - 1 }");
        assert_roundtrip("module T\ninvariant Inv { 2 * 3 }");
        assert_roundtrip("module T\ninvariant Inv { 6 / 2 }");
        assert_roundtrip("module T\ninvariant Inv { 7 % 3 }");
    }

    #[test]
    fn test_roundtrip_set_operators() {
        assert_roundtrip("module T\nvar s: Set[0..3]\ninvariant Inv { 1 in s }");
        assert_roundtrip("module T\nvar s: Set[0..3]\ninvariant Inv { 1 not in s }");
        assert_roundtrip("module T\nvar s: Set[0..3]\ninvariant Inv { s union {1} == s }");
        assert_roundtrip("module T\nvar s: Set[0..3]\ninvariant Inv { s intersect {} == {} }");
        assert_roundtrip("module T\nvar s: Set[0..3]\ninvariant Inv { s diff {1} subset_of s }");
    }

    #[test]
    fn test_roundtrip_seq_concat() {
        assert_roundtrip("module T\ninit { x = [1] ++ [2] }");
    }

    #[test]
    fn test_roundtrip_action_with_let_stmt() {
        assert_roundtrip("module T\nvar x: 0..5\naction A() { let y = x; x = y + 1; }");
    }

    #[test]
    fn test_roundtrip_multi_statement_action() {
        assert_roundtrip("module T\nvar x: 0..5\nvar y: 0..5\naction A() { x = 1; y = 2; }");
    }

    #[test]
    fn test_roundtrip_multi_binding_quantifier() {
        assert_roundtrip("module T\ninvariant Inv { all a in 0..3, b in 0..3: a + b >= 0 }");
    }

    #[test]
    fn test_roundtrip_fn_lit() {
        assert_roundtrip("module T\ninit { x = {k: 0 for k in 0..3} }");
    }

    #[test]
    fn test_roundtrip_comprehensive_features() {
        let source = r#"module Features
var queue: Seq[0..3]
var busy: Set[0..1]
var done: Dict[0..1, 0..3]
var next_id: 0..3
var paused: Bool
view { queue, busy, done, next_id, paused }
func Max(a, b) {
    if a > b then a else b
}
init {
    queue = [];
    busy = {};
    done = {w: 0 for w in 0..1};
    next_id = 0;
}
action Enqueue() {
    require not paused;
    require next_id < 3;
    require len(queue) < 3;
    queue = queue ++ [next_id];
    next_id = next_id + 1;
}
action Claim(w: 0..1) {
    require len(queue) > 0;
    require not (w in busy);
    let task = head(queue);
    queue = tail(queue);
    busy = busy union {w};
    done = done | {w: done[w]};
}
invariant ScoresValid {
    all w in 0..1: done[w] >= 0 implies done[w] <= 3
}
auxiliary invariant Helper {
    next_id >= 0
}
property Liveness {
    always eventually true
}
"#;
        assert_roundtrip(source);
    }

    #[test]
    fn test_roundtrip_double_neg() {
        assert_roundtrip("module T\ninit { x = y - -1 }");
    }

    #[test]
    fn test_roundtrip_nested_not() {
        assert_roundtrip("module T\ninvariant Inv { not (true and false) }");
    }

    #[test]
    fn test_roundtrip_not_eq() {
        assert_roundtrip("module T\ninvariant Inv { not x == 1 }");
    }

    #[test]
    fn test_roundtrip_chained_implies() {
        assert_roundtrip("module T\ninvariant Inv { (a implies b) implies c }");
    }

    #[test]
    fn test_roundtrip_nested_if() {
        assert_roundtrip("module T\ninit { x = if true then (if false then 1 else 2) else 3 }");
    }

    #[test]
    fn test_roundtrip_set_of_sets() {
        assert_roundtrip("module T\nvar s: Set[Set[0..2]]");
    }

    #[test]
    fn test_roundtrip_dict_of_dicts() {
        assert_roundtrip("module T\nvar d: Dict[0..1, Dict[0..1, 0..1]]");
    }

    #[test]
    fn test_roundtrip_option_of_option() {
        assert_roundtrip("module T\nvar x: Option[Option[Nat]]");
    }

    #[test]
    fn test_roundtrip_deeply_nested_expr() {
        assert_roundtrip("module T\ninit { x = ((1 + 2) * (3 - 4)) / 5 }");
    }

    #[test]
    fn test_roundtrip_empty_action_params() {
        assert_roundtrip("module T\nvar x: 0..1\naction A() { x = 0 }");
    }

    #[test]
    fn test_roundtrip_all_examples() {
        let examples_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
        let mut failures = Vec::new();
        let mut total = 0;
        for dir in &["other", "showcase"] {
            let path = examples_dir.join(dir);
            if !path.exists() {
                continue;
            }
            for entry in std::fs::read_dir(&path).unwrap() {
                let entry = entry.unwrap();
                let file = entry.path();
                if file.extension().map_or(true, |e| e != "specl") {
                    continue;
                }
                total += 1;
                let source = std::fs::read_to_string(&file).unwrap();
                let m1 = match parse(&source) {
                    Ok(m) => m,
                    Err(_) => continue, // skip files that don't parse
                };
                let p1 = pretty_print(&m1);
                let m2 = match parse(&p1) {
                    Ok(m) => m,
                    Err(e) => {
                        failures.push(format!("ROUNDTRIP PARSE FAIL {}: {e}", file.display()));
                        continue;
                    }
                };
                let p2 = pretty_print(&m2);
                if p1 != p2 {
                    failures.push(format!("ROUNDTRIP MISMATCH {}", file.display()));
                }
            }
        }
        if !failures.is_empty() {
            panic!(
                "{} roundtrip failures out of {total} files:\n{}",
                failures.len(),
                failures.join("\n")
            );
        }
    }
}
