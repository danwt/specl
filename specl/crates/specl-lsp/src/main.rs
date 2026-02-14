//! Specl Language Server Protocol implementation.

use dashmap::DashMap;
use ropey::Rope;
use specl_syntax::{parse, pretty_print, Decl, Lexer, Span, TokenKind};
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

    /// Convert a Span to an LSP Range.
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
            let (name, kind, detail, range) = match decl {
                Decl::Var(d) => {
                    let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                    (d.name.name.clone(), SymbolKind::VARIABLE, Some(type_str), d.span)
                }
                Decl::Const(d) => {
                    let val_str = specl_syntax::pretty::pretty_print_const_value(&d.value);
                    (d.name.name.clone(), SymbolKind::CONSTANT, Some(val_str), d.span)
                }
                Decl::Action(d) => {
                    let params = format_action_params(&d.params);
                    let detail = if params.is_empty() { None } else { Some(format!("({params})")) };
                    (d.name.name.clone(), SymbolKind::FUNCTION, detail, d.span)
                }
                Decl::Invariant(d) => {
                    (d.name.name.clone(), SymbolKind::BOOLEAN, Some("invariant".into()), d.span)
                }
                Decl::Func(d) => {
                    let params = format_func_params(&d.params);
                    (d.name.name.clone(), SymbolKind::FUNCTION, Some(format!("({params})")), d.span)
                }
                Decl::Type(d) => {
                    let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                    (d.name.name.clone(), SymbolKind::TYPE_PARAMETER, Some(type_str), d.span)
                }
                Decl::Init(_) => {
                    ("init".into(), SymbolKind::CONSTRUCTOR, None, decl.span())
                }
                Decl::Property(d) => {
                    (d.name.name.clone(), SymbolKind::PROPERTY, Some("property".into()), d.span)
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
                range: Self::span_to_range(range),
                selection_range: Self::span_to_range(range),
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
