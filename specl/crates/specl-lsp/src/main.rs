//! Specl Language Server Protocol implementation.

use dashmap::DashMap;
use ropey::Rope;
use specl_syntax::{parse, pretty_print, Decl, Expr, ExprKind, Lexer, Span, TokenKind};
use specl_types::check_module;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use tracing::{debug, info};

/// Document state stored by the server.
struct Document {
    /// Document content as a rope for efficient edits.
    content: Rope,
    /// Document version.
    version: i32,
}

/// The Specl language server.
struct SpeclLanguageServer {
    /// LSP client for sending notifications.
    client: Client,
    /// Open documents.
    documents: DashMap<Url, Document>,
}

fn format_action_params(params: &[specl_syntax::Param]) -> String {
    let parts: Vec<_> = params
        .iter()
        .map(|p| {
            format!(
                "{}: {}",
                p.name.name,
                specl_syntax::pretty::pretty_print_type(&p.ty)
            )
        })
        .collect();
    parts.join(", ")
}

fn format_func_params(params: &[specl_syntax::FuncParam]) -> String {
    let parts: Vec<_> = params.iter().map(|p| p.name.name.as_str()).collect();
    parts.join(", ")
}

fn decl_hover_text(decl: &Decl) -> Option<String> {
    match decl {
        Decl::Var(d) => {
            let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
            Some(format!("**var** `{}`: `{}`", d.name.name, type_str))
        }
        Decl::Const(d) => {
            let value_str = specl_syntax::pretty::pretty_print_const_value(&d.value);
            Some(format!("**const** `{}`: `{}`", d.name.name, value_str))
        }
        Decl::Action(d) => Some(format!(
            "**action** `{}({})`",
            d.name.name,
            format_action_params(&d.params)
        )),
        Decl::Invariant(d) => Some(format!("**invariant** `{}`", d.name.name)),
        Decl::Func(d) => Some(format!(
            "**func** `{}({})`",
            d.name.name,
            format_func_params(&d.params)
        )),
        Decl::Type(d) => {
            let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
            Some(format!("**type** `{}` = `{}`", d.name.name, type_str))
        }
        Decl::Property(d) => Some(format!("**property** `{}`", d.name.name)),
        _ => None,
    }
}

fn decl_name_span(decl: &Decl) -> Option<(&str, Span)> {
    match decl {
        Decl::Var(d) => Some((&d.name.name, d.name.span)),
        Decl::Const(d) => Some((&d.name.name, d.name.span)),
        Decl::Action(d) => Some((&d.name.name, d.name.span)),
        Decl::Invariant(d) => Some((&d.name.name, d.name.span)),
        Decl::Func(d) => Some((&d.name.name, d.name.span)),
        Decl::Type(d) => Some((&d.name.name, d.name.span)),
        Decl::Property(d) => Some((&d.name.name, d.name.span)),
        _ => None,
    }
}

fn make_hover(text: String, range: Option<Range>) -> Hover {
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: text,
        }),
        range,
    }
}

fn make_diagnostic(span: Span, message: String) -> Diagnostic {
    Diagnostic {
        range: SpeclLanguageServer::span_to_range(span),
        severity: Some(DiagnosticSeverity::ERROR),
        source: Some("specl".to_string()),
        message,
        ..Default::default()
    }
}

impl SpeclLanguageServer {
    fn new(client: Client) -> Self {
        Self {
            client,
            documents: DashMap::new(),
        }
    }

    /// Get document content by URI.
    fn get_content(&self, uri: &Url) -> Option<String> {
        self.documents.get(uri).map(|doc| doc.content.to_string())
    }

    /// Analyze a document and publish diagnostics.
    async fn analyze_document(&self, uri: &Url) {
        let Some(doc) = self.documents.get(uri) else {
            return;
        };

        let content = doc.content.to_string();
        let version = doc.version;
        drop(doc);

        let diagnostics = Self::get_diagnostics(&content);

        self.client
            .publish_diagnostics(uri.clone(), diagnostics, Some(version))
            .await;
    }

    /// Get diagnostics for source code.
    fn get_diagnostics(source: &str) -> Vec<Diagnostic> {
        let module = match parse(source) {
            Ok(m) => m,
            Err(e) => return vec![make_diagnostic(e.span(), e.to_string())],
        };

        if let Err(e) = check_module(&module) {
            vec![make_diagnostic(e.span(), e.to_string())]
        } else {
            vec![]
        }
    }

    /// Convert a Span to an LSP Range (single-line: uses line/column + length).
    /// Use `span_to_range_in` for multi-line spans (e.g. full declarations).
    fn span_to_range(span: Span) -> Range {
        let start_line = span.line.saturating_sub(1);
        let start_char = span.column.saturating_sub(1);
        let span_len = span.len() as u32;
        Range {
            start: Position {
                line: start_line,
                character: start_char,
            },
            end: Position {
                line: start_line,
                character: start_char + span_len,
            },
        }
    }

    /// Convert a Span to an LSP Range using source text for accurate end position.
    /// Handles multi-line spans correctly by computing end line/column from byte offsets.
    fn span_to_range_in(span: Span, source: &str) -> Range {
        let start_line = span.line.saturating_sub(1);
        let start_char = span.column.saturating_sub(1);
        let (end_line, end_char) = Self::byte_offset_to_position(source, span.end);
        Range {
            start: Position {
                line: start_line,
                character: start_char,
            },
            end: Position {
                line: end_line,
                character: end_char,
            },
        }
    }

    /// Get hover information at a position.
    fn get_hover(&self, source: &str, position: Position) -> Option<Hover> {
        let module = parse(source).ok()?;
        let line = position.line + 1;
        let col = position.character + 1;

        // Check if cursor is on a declaration name
        for decl in &module.decls {
            if let Some((_, span)) = decl_name_span(decl) {
                if Self::position_in_span(line, col, &span) {
                    let text = decl_hover_text(decl)?;
                    return Some(make_hover(text, Some(Self::span_to_range(span))));
                }
            }
        }

        // If not on a declaration name, find matching declaration by word
        let word = Self::word_at_position(source, position)?;
        for decl in &module.decls {
            if let Some((name, _)) = decl_name_span(decl) {
                if name == word {
                    let text = decl_hover_text(decl)?;
                    return Some(make_hover(text, None));
                }
            }
        }

        None
    }

    fn position_in_span(line: u32, col: u32, span: &Span) -> bool {
        if line != span.line {
            return false;
        }
        let span_len = span.len() as u32;
        col >= span.column && col < span.column + span_len
    }

    /// Get completions at a position.
    fn get_completions(&self, source: &str, _position: Position) -> Vec<CompletionItem> {
        let mut items = Vec::new();

        let keywords = [
            ("module", "Module declaration"),
            ("const", "Constant declaration"),
            ("var", "State variable declaration"),
            ("type", "Type alias declaration"),
            ("action", "Action declaration"),
            ("init", "Initial state predicate"),
            ("next", "Next state relation"),
            ("invariant", "Safety invariant"),
            ("property", "Temporal property"),
            ("require", "Precondition"),
            ("all", "Universal quantifier"),
            ("any", "Existential quantifier"),
            ("choose", "Deterministic choice"),
            ("let", "Local binding"),
            ("if", "Conditional expression"),
            ("then", "Then branch"),
            ("else", "Else branch"),
            ("in", "Membership/binding"),
            ("and", "Logical conjunction"),
            ("or", "Logical disjunction"),
            ("not", "Logical negation"),
            ("true", "Boolean true"),
            ("false", "Boolean false"),
            ("changes", "Explicit state change"),
            ("enabled", "Action enabled predicate"),
        ];

        for (keyword, detail) in keywords {
            items.push(CompletionItem {
                label: keyword.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some(detail.to_string()),
                ..Default::default()
            });
        }

        let types = [
            ("Bool", "Boolean type"),
            ("Nat", "Natural number type"),
            ("Int", "Integer type"),
            ("String", "String type"),
            ("Set", "Set type"),
            ("Seq", "Sequence type"),
            ("Dict", "Dictionary/map type"),
            ("Option", "Optional type"),
        ];

        for (ty, detail) in types {
            items.push(CompletionItem {
                label: ty.to_string(),
                kind: Some(CompletionItemKind::TYPE_PARAMETER),
                detail: Some(detail.to_string()),
                ..Default::default()
            });
        }

        if let Ok(module) = parse(source) {
            for decl in &module.decls {
                match decl {
                    Decl::Var(d) => {
                        items.push(CompletionItem {
                            label: d.name.name.clone(),
                            kind: Some(CompletionItemKind::VARIABLE),
                            detail: Some(format!(
                                "var: {}",
                                specl_syntax::pretty::pretty_print_type(&d.ty)
                            )),
                            ..Default::default()
                        });
                    }
                    Decl::Const(d) => {
                        items.push(CompletionItem {
                            label: d.name.name.clone(),
                            kind: Some(CompletionItemKind::CONSTANT),
                            detail: Some(format!(
                                "const: {}",
                                specl_syntax::pretty::pretty_print_const_value(&d.value)
                            )),
                            ..Default::default()
                        });
                    }
                    Decl::Action(d) => {
                        items.push(CompletionItem {
                            label: d.name.name.clone(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("action".to_string()),
                            ..Default::default()
                        });
                    }
                    Decl::Type(d) => {
                        items.push(CompletionItem {
                            label: d.name.name.clone(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            detail: Some("type".to_string()),
                            ..Default::default()
                        });
                    }
                    Decl::Func(d) => {
                        items.push(CompletionItem {
                            label: d.name.name.clone(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some("func".to_string()),
                            ..Default::default()
                        });
                    }
                    Decl::Invariant(d) => {
                        items.push(CompletionItem {
                            label: d.name.name.clone(),
                            kind: Some(CompletionItemKind::EVENT),
                            detail: Some("invariant".to_string()),
                            ..Default::default()
                        });
                    }
                    _ => {}
                }
            }
        }

        items
    }

    /// Find definition at a position.
    fn get_definition(&self, source: &str, position: Position, uri: &Url) -> Option<Location> {
        let module = parse(source).ok()?;
        let word = Self::word_at_position(source, position)?;

        for decl in &module.decls {
            if let Some((name, span)) = decl_name_span(decl) {
                if name == word {
                    let line = position.line + 1;
                    let col = position.character + 1;
                    if Self::position_in_span(line, col, &span) {
                        return None;
                    }
                    return Some(Location {
                        uri: uri.clone(),
                        range: Self::span_to_range(span),
                    });
                }
            }
        }

        None
    }

    /// Extract the identifier word at a cursor position from source text.
    fn word_at_position(source: &str, position: Position) -> Option<String> {
        let lines: Vec<&str> = source.lines().collect();
        let line = lines.get(position.line as usize)?;
        let col = position.character as usize;
        if col >= line.len() {
            return None;
        }

        let bytes = line.as_bytes();
        if col < bytes.len() && !Self::is_ident_char(bytes[col]) {
            return None;
        }

        let mut start = col;
        while start > 0 && Self::is_ident_char(bytes[start - 1]) {
            start -= 1;
        }

        let mut end = col;
        while end < bytes.len() && Self::is_ident_char(bytes[end]) {
            end += 1;
        }

        if start == end {
            return None;
        }

        Some(line[start..end].to_string())
    }

    fn is_ident_char(b: u8) -> bool {
        b.is_ascii_alphanumeric() || b == b'_'
    }

    /// Get document symbols for the outline view.
    fn get_document_symbols(&self, source: &str) -> Vec<DocumentSymbol> {
        let module = match parse(source) {
            Ok(m) => m,
            Err(_) => return vec![],
        };

        let mut symbols = Vec::new();

        for decl in &module.decls {
            let (name, kind, detail, span, name_span) = match decl {
                Decl::Var(d) => {
                    let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                    (d.name.name.clone(), SymbolKind::VARIABLE, Some(type_str), d.span, d.name.span)
                }
                Decl::Const(d) => {
                    let val_str = specl_syntax::pretty::pretty_print_const_value(&d.value);
                    (d.name.name.clone(), SymbolKind::CONSTANT, Some(val_str), d.span, d.name.span)
                }
                Decl::Action(d) => {
                    let params = format_action_params(&d.params);
                    let detail = if params.is_empty() { None } else { Some(format!("({params})")) };
                    (d.name.name.clone(), SymbolKind::FUNCTION, detail, d.span, d.name.span)
                }
                Decl::Invariant(d) => {
                    (d.name.name.clone(), SymbolKind::BOOLEAN, Some("invariant".into()), d.span, d.name.span)
                }
                Decl::Func(d) => {
                    let params = format_func_params(&d.params);
                    (d.name.name.clone(), SymbolKind::FUNCTION, Some(format!("({params})")), d.span, d.name.span)
                }
                Decl::Type(d) => {
                    let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                    (d.name.name.clone(), SymbolKind::TYPE_PARAMETER, Some(type_str), d.span, d.name.span)
                }
                Decl::Init(_) => {
                    let s = decl.span();
                    ("init".into(), SymbolKind::CONSTRUCTOR, None, s, s)
                }
                Decl::Property(d) => {
                    (d.name.name.clone(), SymbolKind::PROPERTY, Some("property".into()), d.span, d.name.span)
                }
                _ => continue,
            };

            #[allow(deprecated)]
            symbols.push(DocumentSymbol {
                name,
                detail,
                kind,
                tags: None,
                deprecated: None,
                range: Self::span_to_range_in(span, source),
                selection_range: Self::span_to_range(name_span),
                children: None,
            });
        }

        symbols
    }

    /// Find all references to the identifier at the given position.
    fn get_references(&self, source: &str, position: Position, uri: &Url) -> Vec<Location> {
        let word = match Self::word_at_position(source, position) {
            Some(w) => w,
            None => return vec![],
        };

        let tokens = Lexer::new(source).tokenize();
        let mut locations = Vec::new();

        for token in &tokens {
            if let TokenKind::Ident(name) = &token.kind {
                if name == &word {
                    locations.push(Location {
                        uri: uri.clone(),
                        range: Self::span_to_range(token.span),
                    });
                }
            }
        }

        locations
    }

    /// Get document highlights (all occurrences of symbol under cursor).
    fn get_document_highlights(&self, source: &str, position: Position) -> Vec<DocumentHighlight> {
        let word = match Self::word_at_position(source, position) {
            Some(w) => w,
            None => return vec![],
        };

        let module = parse(source).ok();
        let is_write_target = |span: &Span| -> bool {
            // Check if this occurrence is a declaration name (definition site)
            if let Some(ref m) = module {
                for decl in &m.decls {
                    if let Some((name, ns)) = decl_name_span(decl) {
                        if name == word && ns.start == span.start {
                            return true;
                        }
                    }
                }
            }
            false
        };

        let tokens = Lexer::new(source).tokenize();
        let mut highlights = Vec::new();

        for token in &tokens {
            if let TokenKind::Ident(name) = &token.kind {
                if name == &word {
                    let kind = if is_write_target(&token.span) {
                        Some(DocumentHighlightKind::WRITE)
                    } else {
                        Some(DocumentHighlightKind::READ)
                    };
                    highlights.push(DocumentHighlight {
                        range: Self::span_to_range(token.span),
                        kind,
                    });
                }
            }
        }

        highlights
    }

    /// Get signature help at the cursor position.
    /// Detects when cursor is inside `func(...)` or `action(...)` and returns parameter info.
    fn get_signature_help(&self, source: &str, position: Position) -> Option<SignatureHelp> {
        let lines: Vec<&str> = source.lines().collect();
        let line = lines.get(position.line as usize)?;
        let col = position.character as usize;
        if col == 0 || col > line.len() {
            return None;
        }

        // Walk backwards from cursor to find matching '(' and the function name before it
        let bytes = line.as_bytes();
        let mut depth = 0i32;
        let mut paren_pos = None;
        let mut active_param: u32 = 0;

        // Count commas at current nesting level to determine active parameter
        for i in (0..col).rev() {
            match bytes[i] {
                b')' => depth += 1,
                b'(' => {
                    if depth == 0 {
                        paren_pos = Some(i);
                        break;
                    }
                    depth -= 1;
                }
                b',' if depth == 0 => active_param += 1,
                _ => {}
            }
        }

        let paren_pos = paren_pos?;

        // Extract the identifier before the '('
        let mut end = paren_pos;
        while end > 0 && bytes[end - 1] == b' ' {
            end -= 1;
        }
        let mut start = end;
        while start > 0 && Self::is_ident_char(bytes[start - 1]) {
            start -= 1;
        }
        if start == end {
            return None;
        }
        let func_name = &line[start..end];

        // Find the declaration and build signature
        let module = parse(source).ok()?;
        for decl in &module.decls {
            match decl {
                Decl::Action(d) if d.name.name == func_name => {
                    let params: Vec<ParameterInformation> = d
                        .params
                        .iter()
                        .map(|p| ParameterInformation {
                            label: ParameterLabel::Simple(format!(
                                "{}: {}",
                                p.name.name,
                                specl_syntax::pretty::pretty_print_type(&p.ty)
                            )),
                            documentation: None,
                        })
                        .collect();
                    let label = format!(
                        "action {}({})",
                        d.name.name,
                        format_action_params(&d.params)
                    );
                    return Some(SignatureHelp {
                        signatures: vec![SignatureInformation {
                            label,
                            documentation: None,
                            parameters: Some(params),
                            active_parameter: Some(active_param),
                        }],
                        active_signature: Some(0),
                        active_parameter: Some(active_param),
                    });
                }
                Decl::Func(d) if d.name.name == func_name => {
                    let params: Vec<ParameterInformation> = d
                        .params
                        .iter()
                        .map(|p| ParameterInformation {
                            label: ParameterLabel::Simple(p.name.name.clone()),
                            documentation: None,
                        })
                        .collect();
                    let label = format!(
                        "func {}({})",
                        d.name.name,
                        format_func_params(&d.params)
                    );
                    return Some(SignatureHelp {
                        signatures: vec![SignatureInformation {
                            label,
                            documentation: None,
                            parameters: Some(params),
                            active_parameter: Some(active_param),
                        }],
                        active_signature: Some(0),
                        active_parameter: Some(active_param),
                    });
                }
                _ => {}
            }
        }

        None
    }

    /// Get inlay hints for parameter names at action/func call sites.
    fn get_inlay_hints(&self, source: &str) -> Vec<InlayHint> {
        let module = match parse(source) {
            Ok(m) => m,
            Err(_) => return vec![],
        };

        // Build lookup: name -> param names
        let mut param_names: std::collections::HashMap<String, Vec<String>> =
            std::collections::HashMap::new();
        for decl in &module.decls {
            match decl {
                Decl::Action(d) => {
                    param_names.insert(
                        d.name.name.clone(),
                        d.params.iter().map(|p| p.name.name.clone()).collect(),
                    );
                }
                Decl::Func(d) => {
                    param_names.insert(
                        d.name.name.clone(),
                        d.params.iter().map(|p| p.name.name.clone()).collect(),
                    );
                }
                _ => {}
            }
        }

        if param_names.is_empty() {
            return vec![];
        }

        let mut hints = Vec::new();
        // Walk all expressions in all declarations
        for decl in &module.decls {
            match decl {
                Decl::Action(d) => {
                    for req in &d.body.requires {
                        Self::collect_call_hints(req, &param_names, &mut hints);
                    }
                    if let Some(eff) = &d.body.effect {
                        Self::collect_call_hints(eff, &param_names, &mut hints);
                    }
                }
                Decl::Func(d) => {
                    Self::collect_call_hints(&d.body, &param_names, &mut hints);
                }
                Decl::Invariant(d) => {
                    Self::collect_call_hints(&d.body, &param_names, &mut hints);
                }
                Decl::Init(d) => {
                    Self::collect_call_hints(&d.body, &param_names, &mut hints);
                }
                Decl::Property(d) => {
                    Self::collect_call_hints(&d.body, &param_names, &mut hints);
                }
                _ => {}
            }
        }

        hints
    }

    /// Recursively walk an expression tree and collect inlay hints for call sites.
    fn collect_call_hints(
        expr: &Expr,
        param_names: &std::collections::HashMap<String, Vec<String>>,
        hints: &mut Vec<InlayHint>,
    ) {
        match &expr.kind {
            ExprKind::Call { func, args } => {
                if let ExprKind::Ident(name) = &func.kind {
                    if let Some(names) = param_names.get(name.as_str()) {
                        for (arg, pname) in args.iter().zip(names.iter()) {
                            hints.push(InlayHint {
                                position: Position {
                                    line: arg.span.line.saturating_sub(1),
                                    character: arg.span.column.saturating_sub(1),
                                },
                                label: InlayHintLabel::String(format!("{pname}: ")),
                                kind: Some(InlayHintKind::PARAMETER),
                                text_edits: None,
                                tooltip: None,
                                padding_left: None,
                                padding_right: None,
                                data: None,
                            });
                        }
                    }
                }
                // Also recurse into func expr and args
                Self::collect_call_hints(func, param_names, hints);
                for arg in args {
                    Self::collect_call_hints(arg, param_names, hints);
                }
            }
            ExprKind::Binary { left, right, .. } => {
                Self::collect_call_hints(left, param_names, hints);
                Self::collect_call_hints(right, param_names, hints);
            }
            ExprKind::Unary { operand, .. } => {
                Self::collect_call_hints(operand, param_names, hints);
            }
            ExprKind::Index { base, index } => {
                Self::collect_call_hints(base, param_names, hints);
                Self::collect_call_hints(index, param_names, hints);
            }
            ExprKind::Slice { base, lo, hi } => {
                Self::collect_call_hints(base, param_names, hints);
                Self::collect_call_hints(lo, param_names, hints);
                Self::collect_call_hints(hi, param_names, hints);
            }
            ExprKind::Field { base, .. } => {
                Self::collect_call_hints(base, param_names, hints);
            }
            ExprKind::If { cond, then_branch, else_branch } => {
                Self::collect_call_hints(cond, param_names, hints);
                Self::collect_call_hints(then_branch, param_names, hints);
                Self::collect_call_hints(else_branch, param_names, hints);
            }
            ExprKind::Let { value, body, .. } => {
                Self::collect_call_hints(value, param_names, hints);
                Self::collect_call_hints(body, param_names, hints);
            }
            ExprKind::Quantifier { body, bindings, .. } => {
                for b in bindings {
                    Self::collect_call_hints(&b.domain, param_names, hints);
                }
                Self::collect_call_hints(body, param_names, hints);
            }
            ExprKind::Choose { domain, predicate, .. } => {
                Self::collect_call_hints(domain, param_names, hints);
                Self::collect_call_hints(predicate, param_names, hints);
            }
            ExprKind::SetComprehension { element, domain, filter, .. } => {
                Self::collect_call_hints(element, param_names, hints);
                Self::collect_call_hints(domain, param_names, hints);
                if let Some(f) = filter {
                    Self::collect_call_hints(f, param_names, hints);
                }
            }
            ExprKind::Require(e)
            | ExprKind::SeqHead(e)
            | ExprKind::SeqTail(e)
            | ExprKind::Len(e)
            | ExprKind::Keys(e)
            | ExprKind::Values(e)
            | ExprKind::BigUnion(e)
            | ExprKind::Powerset(e)
            | ExprKind::Always(e)
            | ExprKind::Eventually(e)
            | ExprKind::Paren(e) => {
                Self::collect_call_hints(e, param_names, hints);
            }
            ExprKind::LeadsTo { left, right } | ExprKind::Range { lo: left, hi: right } => {
                Self::collect_call_hints(left, param_names, hints);
                Self::collect_call_hints(right, param_names, hints);
            }
            ExprKind::SetLit(exprs) | ExprKind::SeqLit(exprs) | ExprKind::TupleLit(exprs) => {
                for e in exprs {
                    Self::collect_call_hints(e, param_names, hints);
                }
            }
            ExprKind::DictLit(pairs) => {
                for (k, v) in pairs {
                    Self::collect_call_hints(k, param_names, hints);
                    Self::collect_call_hints(v, param_names, hints);
                }
            }
            ExprKind::RecordUpdate { base, updates } => {
                Self::collect_call_hints(base, param_names, hints);
                for u in updates {
                    match u {
                        specl_syntax::RecordFieldUpdate::Field { value, .. } => {
                            Self::collect_call_hints(value, param_names, hints);
                        }
                        specl_syntax::RecordFieldUpdate::Dynamic { key, value } => {
                            Self::collect_call_hints(key, param_names, hints);
                            Self::collect_call_hints(value, param_names, hints);
                        }
                    }
                }
            }
            ExprKind::FnLit { domain, body, .. } => {
                Self::collect_call_hints(domain, param_names, hints);
                Self::collect_call_hints(body, param_names, hints);
            }
            ExprKind::Fix { predicate, .. } => {
                Self::collect_call_hints(predicate, param_names, hints);
            }
            // Leaf nodes: no children to recurse into
            _ => {}
        }
    }

    /// Get folding ranges for declarations (blocks that can be collapsed).
    fn get_folding_ranges(&self, source: &str) -> Vec<FoldingRange> {
        let module = match parse(source) {
            Ok(m) => m,
            Err(_) => return vec![],
        };

        // Pre-compute line start offsets for byte-to-line conversion
        let line_starts: Vec<usize> = std::iter::once(0)
            .chain(source.match_indices('\n').map(|(i, _)| i + 1))
            .collect();

        let byte_to_line = |byte_offset: usize| -> u32 {
            match line_starts.binary_search(&byte_offset) {
                Ok(i) => i as u32,
                Err(i) => (i - 1) as u32,
            }
        };

        let mut ranges = Vec::new();
        for decl in &module.decls {
            let span = decl.span();
            let start_line = span.line.saturating_sub(1);
            let end_line = byte_to_line(span.end.saturating_sub(1));
            if end_line > start_line {
                ranges.push(FoldingRange {
                    start_line,
                    start_character: None,
                    end_line,
                    end_character: None,
                    kind: Some(FoldingRangeKind::Region),
                    collapsed_text: None,
                });
            }
        }

        // Also fold comment blocks (consecutive // lines)
        let mut comment_start: Option<u32> = None;
        for (i, line) in source.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") {
                if comment_start.is_none() {
                    comment_start = Some(i as u32);
                }
            } else if let Some(start) = comment_start {
                let end = (i as u32).saturating_sub(1);
                if end > start {
                    ranges.push(FoldingRange {
                        start_line: start,
                        start_character: None,
                        end_line: end,
                        end_character: None,
                        kind: Some(FoldingRangeKind::Comment),
                        collapsed_text: None,
                    });
                }
                comment_start = None;
            }
        }
        // Handle trailing comment block
        if let Some(start) = comment_start {
            let end = source.lines().count() as u32 - 1;
            if end > start {
                ranges.push(FoldingRange {
                    start_line: start,
                    start_character: None,
                    end_line: end,
                    end_character: None,
                    kind: Some(FoldingRangeKind::Comment),
                    collapsed_text: None,
                });
            }
        }

        ranges
    }

    /// Get selection ranges for smart expand/shrink selection.
    fn get_selection_ranges(&self, source: &str, positions: &[Position]) -> Vec<SelectionRange> {
        let module = match parse(source) {
            Ok(m) => m,
            Err(_) => return positions.iter().map(|p| SelectionRange {
                range: Range { start: *p, end: *p },
                parent: None,
            }).collect(),
        };

        positions
            .iter()
            .map(|pos| {
                let line = pos.line + 1; // 1-indexed
                let col = pos.character + 1;

                // Find the innermost declaration containing this position
                let mut best_decl: Option<&Decl> = None;
                for decl in &module.decls {
                    let span = decl.span();
                    if line >= span.line {
                        let end_line = Self::byte_offset_to_line(source, span.end.saturating_sub(1));
                        if line <= end_line + 1 || (line == span.line && col >= span.column) {
                            best_decl = Some(decl);
                        }
                    }
                }

                if let Some(decl) = best_decl {
                    let decl_range = Self::span_to_range_in(decl.span(), source);
                    // Full file as outermost range
                    let file_range = Range {
                        start: Position { line: 0, character: 0 },
                        end: Position {
                            line: source.lines().count() as u32,
                            character: 0,
                        },
                    };
                    let file_selection = Box::new(SelectionRange {
                        range: file_range,
                        parent: None,
                    });
                    SelectionRange {
                        range: decl_range,
                        parent: Some(file_selection),
                    }
                } else {
                    SelectionRange {
                        range: Range { start: *pos, end: *pos },
                        parent: None,
                    }
                }
            })
            .collect()
    }

    fn byte_offset_to_line(source: &str, byte_offset: usize) -> u32 {
        let (line, _) = Self::byte_offset_to_position(source, byte_offset);
        line + 1 // byte_offset_to_position returns 0-indexed, this returns 1-indexed
    }

    /// Convert a byte offset to an LSP Position (0-indexed line and character).
    fn byte_offset_to_position(source: &str, byte_offset: usize) -> (u32, u32) {
        let line_starts: Vec<usize> = std::iter::once(0)
            .chain(source.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        let line_idx = match line_starts.binary_search(&byte_offset) {
            Ok(i) => i,
            Err(i) => i.saturating_sub(1),
        };
        let line_start = line_starts[line_idx];
        let col = byte_offset.saturating_sub(line_start) as u32;
        (line_idx as u32, col)
    }

    /// Semantic token type indices (must match SEMANTIC_TOKEN_TYPES order).
    const TT_KEYWORD: u32 = 0;
    const TT_TYPE: u32 = 1;
    const TT_VARIABLE: u32 = 2;
    const TT_FUNCTION: u32 = 3;
    const TT_NUMBER: u32 = 4;
    const TT_STRING: u32 = 5;
    const TT_COMMENT: u32 = 6;
    const TT_OPERATOR: u32 = 7;

    /// Get semantic tokens for syntax highlighting.
    fn get_semantic_tokens(&self, source: &str) -> Vec<SemanticToken> {
        let tokens = Lexer::new(source).tokenize();

        let mut var_names = std::collections::HashSet::new();
        let mut func_names = std::collections::HashSet::new();
        if let Ok(module) = parse(source) {
            for decl in &module.decls {
                match decl {
                    Decl::Var(d) => { var_names.insert(d.name.name.clone()); }
                    Decl::Const(d) => { var_names.insert(d.name.name.clone()); }
                    Decl::Action(d) => { func_names.insert(d.name.name.clone()); }
                    Decl::Func(d) => { func_names.insert(d.name.name.clone()); }
                    _ => {}
                }
            }
        }

        let mut result = Vec::new();
        let mut prev_line: u32 = 0;
        let mut prev_start: u32 = 0;

        for token in &tokens {
            let token_type = match &token.kind {
                TokenKind::Module | TokenKind::Use | TokenKind::Const | TokenKind::Var
                | TokenKind::Type | TokenKind::Init | TokenKind::Action | TokenKind::Invariant
                | TokenKind::Property | TokenKind::Fairness | TokenKind::Func
                | TokenKind::And | TokenKind::Or | TokenKind::Not | TokenKind::Implies
                | TokenKind::Iff | TokenKind::All | TokenKind::Any | TokenKind::Choose
                | TokenKind::In | TokenKind::For | TokenKind::If | TokenKind::Then
                | TokenKind::Else | TokenKind::Let | TokenKind::With | TokenKind::Require
                | TokenKind::Changes | TokenKind::Always | TokenKind::Eventually
                | TokenKind::LeadsTo | TokenKind::Enabled | TokenKind::WeakFair
                | TokenKind::StrongFair | TokenKind::True | TokenKind::False => Self::TT_KEYWORD,

                TokenKind::Nat | TokenKind::Int | TokenKind::Bool | TokenKind::String_
                | TokenKind::Set | TokenKind::Seq | TokenKind::Dict | TokenKind::Option_
                | TokenKind::Some_ | TokenKind::None_ => Self::TT_TYPE,

                TokenKind::Union | TokenKind::Intersect | TokenKind::Diff
                | TokenKind::SubsetOf | TokenKind::Head | TokenKind::Tail
                | TokenKind::Len | TokenKind::Keys | TokenKind::Values
                | TokenKind::Powerset | TokenKind::UnionAll => Self::TT_OPERATOR,

                TokenKind::Integer(_) => Self::TT_NUMBER,
                TokenKind::StringLit(_) => Self::TT_STRING,
                TokenKind::Comment(_) | TokenKind::DocComment(_) => Self::TT_COMMENT,

                TokenKind::Ident(name) => {
                    if func_names.contains(name.as_str()) {
                        Self::TT_FUNCTION
                    } else if var_names.contains(name.as_str()) {
                        Self::TT_VARIABLE
                    } else {
                        continue;
                    }
                }

                _ => continue,
            };

            let line = token.span.line.saturating_sub(1);
            let start_char = token.span.column.saturating_sub(1);
            let length = token.span.len() as u32;

            if length == 0 {
                continue;
            }

            let delta_line = line - prev_line;
            let delta_start = if delta_line == 0 {
                start_char - prev_start
            } else {
                start_char
            };

            result.push(SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type,
                token_modifiers_bitset: 0,
            });

            prev_line = line;
            prev_start = start_char;
        }

        result
    }

    fn get_workspace_symbols(&self, query: &str) -> Vec<SymbolInformation> {
        let mut result = Vec::new();

        for entry in self.documents.iter() {
            let uri = entry.key().clone();
            let content = entry.value().content.to_string();

            let module = match parse(&content) {
                Ok(m) => m,
                Err(_) => continue,
            };

            for decl in &module.decls {
                let (name, kind, span) = match decl {
                    Decl::Var(d) => (d.name.name.clone(), SymbolKind::VARIABLE, d.span),
                    Decl::Const(d) => (d.name.name.clone(), SymbolKind::CONSTANT, d.span),
                    Decl::Action(d) => (d.name.name.clone(), SymbolKind::FUNCTION, d.span),
                    Decl::Invariant(d) => (d.name.name.clone(), SymbolKind::BOOLEAN, d.span),
                    Decl::Func(d) => (d.name.name.clone(), SymbolKind::FUNCTION, d.span),
                    Decl::Type(d) => (d.name.name.clone(), SymbolKind::TYPE_PARAMETER, d.span),
                    Decl::Property(d) => (d.name.name.clone(), SymbolKind::PROPERTY, d.span),
                    _ => continue,
                };

                // Filter by query (case-insensitive substring match)
                if !query.is_empty() {
                    let name_lower = name.to_lowercase();
                    let query_lower = query.to_lowercase();
                    if !name_lower.contains(&query_lower) {
                        continue;
                    }
                }

                #[allow(deprecated)]
                result.push(SymbolInformation {
                    name,
                    kind,
                    tags: None,
                    deprecated: None,
                    location: Location {
                        uri: uri.clone(),
                        range: Self::span_to_range_in(span, &content),
                    },
                    container_name: None,
                });
            }
        }

        result
    }

    fn get_code_actions(
        &self,
        source: &str,
        uri: &Url,
        diagnostics: &[Diagnostic],
    ) -> Vec<CodeActionOrCommand> {
        let module = match parse(source) {
            Ok(m) => m,
            Err(_) => return vec![],
        };

        let mut actions = Vec::new();

        // Diagnostic-associated quick fixes
        for diag in diagnostics {
            // "undefined variable: foo" → offer to declare it
            if let Some(name) = diag.message.strip_prefix("undefined variable: ") {
                // Find the last var/const declaration to insert after
                let mut insert_line = 0u32;
                for decl in &module.decls {
                    match decl {
                        Decl::Var(d) => {
                            let l = d.span.line.saturating_sub(1);
                            if l >= insert_line {
                                insert_line = l + 1;
                            }
                        }
                        Decl::Const(d) => {
                            let l = d.span.line.saturating_sub(1);
                            if l >= insert_line {
                                insert_line = l + 1;
                            }
                        }
                        _ => {}
                    }
                }

                let snippet = format!("var {name}: ???\n");
                let pos = Position {
                    line: insert_line,
                    character: 0,
                };
                let mut changes = std::collections::HashMap::new();
                changes.insert(
                    uri.clone(),
                    vec![TextEdit {
                        range: Range { start: pos, end: pos },
                        new_text: snippet,
                    }],
                );
                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: format!("Declare variable '{name}'"),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![diag.clone()]),
                    edit: Some(WorkspaceEdit {
                        changes: Some(changes),
                        ..Default::default()
                    }),
                    ..Default::default()
                }));
            }
        }

        // Find insertion point: after the last declaration
        let last_line = source.lines().count() as u32;
        let insert_pos = Position {
            line: last_line,
            character: 0,
        };

        // Offer "Add init block" if none exists
        let has_init = module.decls.iter().any(|d| matches!(d, Decl::Init(_)));
        if !has_init {
            let has_vars = module.decls.iter().any(|d| matches!(d, Decl::Var(_)));
            if has_vars {
                // Build init template from declared variables
                let var_names: Vec<&str> = module
                    .decls
                    .iter()
                    .filter_map(|d| match d {
                        Decl::Var(v) => Some(v.name.name.as_str()),
                        _ => None,
                    })
                    .collect();
                let init_body = var_names
                    .iter()
                    .enumerate()
                    .map(|(i, name)| {
                        let prefix = if i == 0 { "    " } else { "    and " };
                        format!("{prefix}{name} = ???")
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                let snippet = format!("\ninit {{\n{init_body}\n}}\n");

                let mut changes = std::collections::HashMap::new();
                changes.insert(
                    uri.clone(),
                    vec![TextEdit {
                        range: Range {
                            start: insert_pos,
                            end: insert_pos,
                        },
                        new_text: snippet,
                    }],
                );
                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: "Add init block".to_string(),
                    kind: Some(CodeActionKind::REFACTOR),
                    edit: Some(WorkspaceEdit {
                        changes: Some(changes),
                        ..Default::default()
                    }),
                    ..Default::default()
                }));
            }
        }

        // Offer "Add invariant" template
        {
            let snippet = "\ninvariant Name {\n    true\n}\n".to_string();
            let mut changes = std::collections::HashMap::new();
            changes.insert(
                uri.clone(),
                vec![TextEdit {
                    range: Range {
                        start: insert_pos,
                        end: insert_pos,
                    },
                    new_text: snippet,
                }],
            );
            actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                title: "Add invariant".to_string(),
                kind: Some(CodeActionKind::REFACTOR),
                edit: Some(WorkspaceEdit {
                    changes: Some(changes),
                    ..Default::default()
                }),
                ..Default::default()
            }));
        }

        // Offer "Add action" template
        {
            let snippet = "\naction Name() {\n    require true\n}\n".to_string();
            let mut changes = std::collections::HashMap::new();
            changes.insert(
                uri.clone(),
                vec![TextEdit {
                    range: Range {
                        start: insert_pos,
                        end: insert_pos,
                    },
                    new_text: snippet,
                }],
            );
            actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                title: "Add action".to_string(),
                kind: Some(CodeActionKind::REFACTOR),
                edit: Some(WorkspaceEdit {
                    changes: Some(changes),
                    ..Default::default()
                }),
                ..Default::default()
            }));
        }

        actions
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for SpeclLanguageServer {
    async fn initialize(&self, _params: InitializeParams) -> Result<InitializeResult> {
        info!("Specl language server initializing");
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
                    ..Default::default()
                }),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec!["(".to_string(), ",".to_string()]),
                    ..Default::default()
                }),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                inlay_hint_provider: Some(OneOf::Left(true)),
                folding_range_provider: Some(FoldingRangeProviderCapability::Simple(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            legend: SemanticTokensLegend {
                                token_types: vec![
                                    SemanticTokenType::KEYWORD,    // 0
                                    SemanticTokenType::TYPE,       // 1
                                    SemanticTokenType::VARIABLE,   // 2
                                    SemanticTokenType::FUNCTION,   // 3
                                    SemanticTokenType::NUMBER,     // 4
                                    SemanticTokenType::STRING,     // 5
                                    SemanticTokenType::COMMENT,    // 6
                                    SemanticTokenType::OPERATOR,   // 7
                                ],
                                token_modifiers: vec![],
                            },
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                            range: None,
                            ..Default::default()
                        },
                    ),
                ),
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
                workspace_symbol_provider: Some(OneOf::Left(true)),
                document_highlight_provider: Some(OneOf::Left(true)),
                selection_range_provider: Some(SelectionRangeProviderCapability::Simple(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "specl-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _params: InitializedParams) {
        info!("Specl language server initialized");
    }

    async fn shutdown(&self) -> Result<()> {
        info!("Specl language server shutting down");
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        debug!("document opened: {}", params.text_document.uri);
        let uri = params.text_document.uri;
        let content = Rope::from_str(&params.text_document.text);
        let version = params.text_document.version;

        self.documents
            .insert(uri.clone(), Document { content, version });
        self.analyze_document(&uri).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        debug!("document changed: {}", params.text_document.uri);
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        if let Some(change) = params.content_changes.into_iter().next_back() {
            let content = Rope::from_str(&change.text);
            self.documents
                .insert(uri.clone(), Document { content, version });
            self.analyze_document(&uri).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        debug!("document closed: {}", params.text_document.uri);
        self.documents.remove(&params.text_document.uri);
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        Ok(self.get_hover(&content, position))
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let items = self.get_completions(&content, position);
        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        Ok(self.get_signature_help(&content, position))
    }

    async fn selection_range(
        &self,
        params: SelectionRangeParams,
    ) -> Result<Option<Vec<SelectionRange>>> {
        let uri = &params.text_document.uri;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let ranges = self.get_selection_ranges(&content, &params.positions);
        Ok(Some(ranges))
    }

    async fn symbol(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Result<Option<Vec<SymbolInformation>>> {
        let symbols = self.get_workspace_symbols(&params.query);
        Ok(if symbols.is_empty() {
            None
        } else {
            Some(symbols)
        })
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = &params.text_document.uri;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let actions = self.get_code_actions(&content, uri, &params.context.diagnostics);
        Ok(if actions.is_empty() {
            None
        } else {
            Some(actions)
        })
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        Ok(self
            .get_definition(&content, position, uri)
            .map(GotoDefinitionResponse::Scalar))
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let refs = self.get_references(&content, position, uri);
        Ok(if refs.is_empty() { None } else { Some(refs) })
    }

    async fn document_highlight(
        &self,
        params: DocumentHighlightParams,
    ) -> Result<Option<Vec<DocumentHighlight>>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let highlights = self.get_document_highlights(&content, position);
        Ok(if highlights.is_empty() {
            None
        } else {
            Some(highlights)
        })
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = &params.text_document.uri;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let symbols = self.get_document_symbols(&content);
        Ok(Some(DocumentSymbolResponse::Nested(symbols)))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(content) = self.get_content(uri) else { return Ok(None) };

        let refs = self.get_references(&content, position, uri);
        if refs.is_empty() {
            return Ok(None);
        }

        let edits: Vec<TextEdit> = refs
            .into_iter()
            .map(|loc| TextEdit {
                range: loc.range,
                new_text: params.new_name.clone(),
            })
            .collect();

        let mut changes = std::collections::HashMap::new();
        changes.insert(uri.clone(), edits);
        Ok(Some(WorkspaceEdit {
            changes: Some(changes),
            ..Default::default()
        }))
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let uri = &params.text_document.uri;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let hints = self.get_inlay_hints(&content);
        Ok(if hints.is_empty() { None } else { Some(hints) })
    }

    async fn folding_range(&self, params: FoldingRangeParams) -> Result<Option<Vec<FoldingRange>>> {
        let uri = &params.text_document.uri;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let ranges = self.get_folding_ranges(&content);
        Ok(if ranges.is_empty() { None } else { Some(ranges) })
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = &params.text_document.uri;

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };

        let content = doc.content.to_string();

        let Ok(module) = parse(&content) else {
            return Ok(None);
        };

        let formatted = pretty_print(&module);

        let line_count = doc.content.len_lines();
        let last_line_len = doc.content.line(line_count.saturating_sub(1)).len_chars();

        Ok(Some(vec![TextEdit {
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: line_count as u32,
                    character: last_line_len as u32,
                },
            },
            new_text: formatted,
        }]))
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = &params.text_document.uri;
        let Some(content) = self.get_content(uri) else { return Ok(None) };
        let tokens = self.get_semantic_tokens(&content);
        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data: tokens,
        })))
    }
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive(tracing::Level::INFO.into()),
        )
        .with_writer(std::io::stderr)
        .init();

    info!("Starting Specl language server");

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(SpeclLanguageServer::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE_SPEC: &str = r#"module Test

const N: 0..5

var x: 0..10
var flag: Bool

init {
    x = 0
    and flag = false
}

action Step(p: 0..N) {
    require x < 10
    x = x + 1
}

action Toggle() {
    flag = not flag
}

func Double(v) {
    v * 2
}

invariant Safe {
    x >= 0 and x <= 10
}
"#;

    #[test]
    fn diagnostics_valid_spec() {
        let diags = SpeclLanguageServer::get_diagnostics(SAMPLE_SPEC);
        assert!(diags.is_empty(), "valid spec should have no diagnostics");
    }

    #[test]
    fn diagnostics_parse_error() {
        let diags = SpeclLanguageServer::get_diagnostics("module Test\nvar x:");
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("unexpected"));
    }

    #[test]
    fn diagnostics_type_error() {
        // Use an undefined variable reference to trigger a type error
        let src = r#"module Test
var x: 0..10
init { x = 0 }
action A() { x = y }
"#;
        let diags = SpeclLanguageServer::get_diagnostics(src);
        assert!(!diags.is_empty(), "undefined variable should produce diagnostics");
    }

    #[test]
    fn word_at_position_identifier() {
        let src = "var hello: Bool";
        let word = SpeclLanguageServer::word_at_position(src, Position { line: 0, character: 5 });
        assert_eq!(word, Some("hello".to_string()));
    }

    #[test]
    fn word_at_position_at_boundary() {
        let src = "var x: Bool";
        let word = SpeclLanguageServer::word_at_position(src, Position { line: 0, character: 4 });
        assert_eq!(word, Some("x".to_string()));
    }

    #[test]
    fn word_at_position_whitespace() {
        let src = "var x: Bool";
        let word = SpeclLanguageServer::word_at_position(src, Position { line: 0, character: 3 });
        assert_eq!(word, None);
    }

    #[test]
    fn position_in_span_hit() {
        let span = Span {
            start: 0,
            end: 5,
            line: 3,
            column: 5,
        };
        assert!(SpeclLanguageServer::position_in_span(3, 5, &span));
        assert!(SpeclLanguageServer::position_in_span(3, 7, &span));
    }

    #[test]
    fn position_in_span_miss() {
        let span = Span {
            start: 0,
            end: 5,
            line: 3,
            column: 5,
        };
        assert!(!SpeclLanguageServer::position_in_span(2, 5, &span));
        assert!(!SpeclLanguageServer::position_in_span(3, 4, &span));
        assert!(!SpeclLanguageServer::position_in_span(3, 10, &span));
    }

    #[test]
    fn span_to_range_conversion() {
        let span = Span {
            start: 10,
            end: 15,
            line: 3,
            column: 5,
        };
        let range = SpeclLanguageServer::span_to_range(span);
        assert_eq!(range.start.line, 2); // 1-indexed to 0-indexed
        assert_eq!(range.start.character, 4);
        assert_eq!(range.end.line, 2);
        assert_eq!(range.end.character, 9); // 4 + 5
    }

    #[test]
    fn decl_hover_text_var() {
        let module = parse(SAMPLE_SPEC).unwrap();
        let var_decl = module.decls.iter().find(|d| matches!(d, Decl::Var(v) if v.name.name == "x")).unwrap();
        let text = decl_hover_text(var_decl).unwrap();
        assert!(text.contains("**var**") && text.contains("x"), "got: {text}");
    }

    #[test]
    fn decl_hover_text_action() {
        let module = parse(SAMPLE_SPEC).unwrap();
        let action_decl = module.decls.iter().find(|d| matches!(d, Decl::Action(a) if a.name.name == "Step")).unwrap();
        let text = decl_hover_text(action_decl).unwrap();
        assert!(text.contains("**action**") && text.contains("Step"), "got: {text}");
    }

    #[test]
    fn decl_hover_text_func() {
        let module = parse(SAMPLE_SPEC).unwrap();
        let func_decl = module.decls.iter().find(|d| matches!(d, Decl::Func(f) if f.name.name == "Double")).unwrap();
        let text = decl_hover_text(func_decl).unwrap();
        assert!(text.contains("**func**") && text.contains("Double"), "got: {text}");
    }

    #[test]
    fn decl_hover_text_invariant() {
        let module = parse(SAMPLE_SPEC).unwrap();
        let inv_decl = module.decls.iter().find(|d| matches!(d, Decl::Invariant(i) if i.name.name == "Safe")).unwrap();
        let text = decl_hover_text(inv_decl).unwrap();
        assert!(text.contains("**invariant**") && text.contains("Safe"), "got: {text}");
    }

    #[test]
    fn document_symbols_complete() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let symbols = server.get_document_symbols(SAMPLE_SPEC);
        let names: Vec<&str> = symbols.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"N"), "should contain const N");
        assert!(names.contains(&"x"), "should contain var x");
        assert!(names.contains(&"flag"), "should contain var flag");
        assert!(names.contains(&"Step"), "should contain action Step");
        assert!(names.contains(&"Toggle"), "should contain action Toggle");
        assert!(names.contains(&"Double"), "should contain func Double");
        assert!(names.contains(&"Safe"), "should contain invariant Safe");
    }

    #[test]
    fn completions_include_keywords_and_symbols() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let items = server.get_completions(SAMPLE_SPEC, Position { line: 0, character: 0 });
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        // Should include keywords
        assert!(labels.contains(&"action"), "should contain keyword 'action'");
        assert!(labels.contains(&"invariant"), "should contain keyword 'invariant'");
        // Should include user-defined symbols
        assert!(labels.contains(&"x"), "should contain var 'x'");
        assert!(labels.contains(&"Step"), "should contain action 'Step'");
        assert!(labels.contains(&"Double"), "should contain func 'Double'");
    }

    #[test]
    fn signature_help_action() {
        let src = r#"module Test
var x: 0..10
init { x = 0 }
action Foo(a: 0..3, b: 0..5) { x = a + b }
action Bar() { Foo(1, 2) }
"#;
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        // Position inside the Foo(1, 2) call — on the '1' after 'Foo('
        // Line 4 (0-indexed): "action Bar() { Foo(1, 2) }"
        let help = server.get_signature_help(src, Position { line: 4, character: 19 });
        assert!(help.is_some(), "should get signature help inside Foo() call");
        let help = help.unwrap();
        assert_eq!(help.signatures.len(), 1);
        assert!(help.signatures[0].label.contains("Foo"));
    }

    #[test]
    fn inlay_hints_show_param_names() {
        // Use a func call inside an invariant (where func calls commonly appear)
        let src = r#"module Test
var x: 0..10
init { x = 0 }
func Add(a, b) { a + b }
invariant Check { Add(1, 2) > 0 }
"#;
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let hints = server.get_inlay_hints(src);
        let labels: Vec<String> = hints
            .iter()
            .map(|h| match &h.label {
                InlayHintLabel::String(s) => s.clone(),
                InlayHintLabel::LabelParts(parts) => {
                    parts.iter().map(|p| p.value.as_str()).collect()
                }
            })
            .collect();
        assert!(labels.contains(&"a: ".to_string()), "should hint 'a: ', got: {:?}", labels);
        assert!(labels.contains(&"b: ".to_string()), "should hint 'b: ', got: {:?}", labels);
    }

    #[test]
    fn folding_ranges_cover_declarations() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let ranges = server.get_folding_ranges(SAMPLE_SPEC);
        // Should have folding ranges for init, Step, Toggle, Double, Safe
        assert!(
            ranges.len() >= 4,
            "should have at least 4 folding ranges, got {}",
            ranges.len()
        );
    }

    #[test]
    fn semantic_tokens_produced() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let tokens = server.get_semantic_tokens(SAMPLE_SPEC);
        assert!(!tokens.is_empty(), "should produce semantic tokens");
    }

    #[test]
    fn definition_finds_var() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let uri = Url::parse("file:///test.specl").unwrap();
        // Position on 'x' in "require x < 10" — line 13 (0-indexed), char ~12
        let loc = server.get_definition(SAMPLE_SPEC, Position { line: 13, character: 12 }, &uri);
        assert!(loc.is_some(), "should find definition of x");
    }

    #[test]
    fn references_finds_uses() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let uri = Url::parse("file:///test.specl").unwrap();
        // Position on 'x' in "var x: 0..10" — line 4 (0-indexed), char 4
        let refs = server.get_references(SAMPLE_SPEC, Position { line: 4, character: 4 }, &uri);
        assert!(
            refs.len() >= 3,
            "x should be referenced at least 3 times, found {}",
            refs.len()
        );
    }

    #[test]
    fn empty_source_no_panic() {
        let diags = SpeclLanguageServer::get_diagnostics("");
        assert!(!diags.is_empty(), "empty source should produce diagnostic");

        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let symbols = server.get_document_symbols("");
        assert!(symbols.is_empty());
        let tokens = server.get_semantic_tokens("");
        assert!(tokens.is_empty());
        let hints = server.get_inlay_hints("");
        assert!(hints.is_empty());
        let ranges = server.get_folding_ranges("");
        assert!(ranges.is_empty());
    }

    #[test]
    fn code_actions_offer_init_when_missing() {
        let src = r#"module Test
var x: 0..10
"#;
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let uri = Url::parse("file:///test.specl").unwrap();
        let actions = server.get_code_actions(src, &uri, &[]);
        let titles: Vec<&str> = actions
            .iter()
            .filter_map(|a| match a {
                CodeActionOrCommand::CodeAction(ca) => Some(ca.title.as_str()),
                _ => None,
            })
            .collect();
        assert!(titles.contains(&"Add init block"), "should offer 'Add init block'");
        assert!(titles.contains(&"Add invariant"), "should offer 'Add invariant'");
        assert!(titles.contains(&"Add action"), "should offer 'Add action'");
    }

    #[test]
    fn code_actions_no_init_when_present() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let uri = Url::parse("file:///test.specl").unwrap();
        let actions = server.get_code_actions(SAMPLE_SPEC, &uri, &[]);
        let titles: Vec<&str> = actions
            .iter()
            .filter_map(|a| match a {
                CodeActionOrCommand::CodeAction(ca) => Some(ca.title.as_str()),
                _ => None,
            })
            .collect();
        assert!(!titles.contains(&"Add init block"), "should NOT offer init when present");
        assert!(titles.contains(&"Add invariant"), "should still offer 'Add invariant'");
    }

    #[test]
    fn byte_offset_to_position_basic() {
        let src = "line0\nline1\nline2";
        // 'l' of line0 is at (0, 0)
        assert_eq!(SpeclLanguageServer::byte_offset_to_position(src, 0), (0, 0));
        // 'l' of line1 is at byte 6 -> (1, 0)
        assert_eq!(SpeclLanguageServer::byte_offset_to_position(src, 6), (1, 0));
        // 'n' of line1 is at byte 8 -> (1, 2)
        assert_eq!(SpeclLanguageServer::byte_offset_to_position(src, 8), (1, 2));
        // 'l' of line2 is at byte 12 -> (2, 0)
        assert_eq!(SpeclLanguageServer::byte_offset_to_position(src, 12), (2, 0));
    }

    #[test]
    fn span_to_range_in_multiline() {
        let src = "module Test\naction Foo() {\n    require true\n}\n";
        // "module Test\n" = 12 bytes (0..12)
        // "action Foo() {\n" = 15 bytes (12..27)
        // "    require true\n" = 16 bytes (27..43)
        // "}\n" = 2 bytes (43..45)
        // Span covering the action declaration: bytes 12..45
        let span = Span { start: 12, end: 45, line: 2, column: 1 };
        let range = SpeclLanguageServer::span_to_range_in(span, src);
        assert_eq!(range.start.line, 1); // 0-indexed
        assert_eq!(range.start.character, 0);
        assert_eq!(range.end.line, 3); // closing brace line (0-indexed: 3)
        assert!(range.end.line > range.start.line, "multi-line span end should be on later line");
    }

    #[test]
    fn document_highlights_find_all() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        // 'x' on line 4 (0-indexed), char 4 in SAMPLE_SPEC
        let highlights = server.get_document_highlights(SAMPLE_SPEC, Position { line: 4, character: 4 });
        assert!(
            highlights.len() >= 3,
            "x should be highlighted at least 3 times, found {}",
            highlights.len()
        );
        // Declaration site should be WRITE
        let write_count = highlights.iter().filter(|h| h.kind == Some(DocumentHighlightKind::WRITE)).count();
        assert!(write_count >= 1, "should have at least one WRITE highlight for declaration");
    }

    #[test]
    fn document_symbols_multiline_range() {
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let symbols = server.get_document_symbols(SAMPLE_SPEC);
        // Find the "Step" action symbol — it spans multiple lines
        let step = symbols.iter().find(|s| s.name == "Step").unwrap();
        assert!(
            step.range.end.line > step.range.start.line,
            "multi-line action should have range spanning multiple lines: start={}, end={}",
            step.range.start.line, step.range.end.line
        );
    }

    #[test]
    fn code_action_quickfix_undefined_var() {
        let src = r#"module Test
var x: 0..10
init { x = 0 }
action A() { x = y }
"#;
        let (service, _) = LspService::new(SpeclLanguageServer::new);
        let server = service.inner();
        let uri = Url::parse("file:///test.specl").unwrap();

        // Simulate the diagnostic that the type checker would produce
        let diag = Diagnostic {
            range: Range {
                start: Position { line: 3, character: 17 },
                end: Position { line: 3, character: 18 },
            },
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some("specl".to_string()),
            message: "undefined variable: y".to_string(),
            ..Default::default()
        };

        let actions = server.get_code_actions(src, &uri, &[diag]);
        let titles: Vec<&str> = actions
            .iter()
            .filter_map(|a| match a {
                CodeActionOrCommand::CodeAction(ca) => Some(ca.title.as_str()),
                _ => None,
            })
            .collect();
        assert!(
            titles.contains(&"Declare variable 'y'"),
            "should offer to declare undefined variable 'y', got: {:?}",
            titles
        );
    }
}
