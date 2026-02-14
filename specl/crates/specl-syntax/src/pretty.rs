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
        }
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
                FairnessKind::Weak => self.write("weak_fair "),
                FairnessKind::Strong => self.write("strong_fair "),
            }
            self.writeln(&constraint.action.name);
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
            TypeExpr::Tuple(elements, _) => {
                self.write("(");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_type_expr(elem);
                }
                self.write(")");
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
                self.write(s);
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
            ExprKind::TupleLit(elements) => {
                self.write("(");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(elem);
                }
                self.write(")");
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
            ExprKind::RecordUpdate { base, updates } => {
                self.print_expr(base);
                self.write(" with { ");
                for (i, update) in updates.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    match update {
                        RecordFieldUpdate::Field { name, value } => {
                            self.write(&name.name);
                            self.write(": ");
                            self.print_expr(value);
                        }
                        RecordFieldUpdate::Dynamic { key, value } => {
                            self.write("[");
                            self.print_expr(key);
                            self.write("]: ");
                            self.print_expr(value);
                        }
                    }
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
            ExprKind::Choose {
                var,
                domain,
                predicate,
            } => {
                self.write("fix ");
                self.write(&var.name);
                self.write(" in ");
                self.print_expr(domain);
                self.write(": ");
                self.print_expr(predicate);
            }
            ExprKind::Fix { var, predicate } => {
                self.write("fix ");
                self.write(&var.name);
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
}
