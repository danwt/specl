//! Specl Language Server Protocol implementation.

use dashmap::DashMap;
use ropey::Rope;
use specl_syntax::{parse, pretty_print, Decl, Span};
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

impl SpeclLanguageServer {
    fn new(client: Client) -> Self {
        Self {
            client,
            documents: DashMap::new(),
        }
    }

    /// Analyze a document and publish diagnostics.
    async fn analyze_document(&self, uri: &Url) {
        let Some(doc) = self.documents.get(uri) else {
            return;
        };

        let content = doc.content.to_string();
        let version = doc.version;
        drop(doc);

        let diagnostics = self.get_diagnostics(&content);

        self.client
            .publish_diagnostics(uri.clone(), diagnostics, Some(version))
            .await;
    }

    /// Get diagnostics for source code.
    fn get_diagnostics(&self, source: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Parse
        let module = match parse(source) {
            Ok(m) => m,
            Err(e) => {
                let msg = e.to_string();
                let span = e.span();
                diagnostics.push(Diagnostic {
                    range: Self::span_to_range(span),
                    severity: Some(DiagnosticSeverity::ERROR),
                    source: Some("specl".to_string()),
                    message: msg,
                    ..Default::default()
                });
                return diagnostics;
            }
        };

        // Type check
        if let Err(e) = check_module(&module) {
            let msg = e.to_string();
            let span = e.span();
            diagnostics.push(Diagnostic {
                range: Self::span_to_range(span),
                severity: Some(DiagnosticSeverity::ERROR),
                source: Some("specl".to_string()),
                message: msg,
                ..Default::default()
            });
        }

        diagnostics
    }

    /// Convert a Span to an LSP Range.
    /// Note: Span only tracks start position, so we extend the range by the byte length.
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

        // Find what's at the position
        let line = position.line + 1;
        let col = position.character + 1;

        // Check declarations
        for decl in &module.decls {
            match decl {
                Decl::Var(d) => {
                    if Self::position_in_span(line, col, &d.name.span) {
                        let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**var** `{}`: `{}`", d.name.name, type_str),
                            }),
                            range: Some(Self::span_to_range(d.name.span)),
                        });
                    }
                }
                Decl::Const(d) => {
                    if Self::position_in_span(line, col, &d.name.span) {
                        let value_str = specl_syntax::pretty::pretty_print_const_value(&d.value);
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**const** `{}`: `{}`", d.name.name, value_str),
                            }),
                            range: Some(Self::span_to_range(d.name.span)),
                        });
                    }
                }
                Decl::Action(d) => {
                    if Self::position_in_span(line, col, &d.name.span) {
                        let params: Vec<_> = d
                            .params
                            .iter()
                            .map(|p| {
                                format!(
                                    "{}: {}",
                                    p.name.name,
                                    specl_syntax::pretty::pretty_print_type(&p.ty)
                                )
                            })
                            .collect();
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!(
                                    "**action** `{}({})`",
                                    d.name.name,
                                    params.join(", ")
                                ),
                            }),
                            range: Some(Self::span_to_range(d.name.span)),
                        });
                    }
                }
                Decl::Invariant(d) => {
                    if Self::position_in_span(line, col, &d.name.span) {
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**invariant** `{}`", d.name.name),
                            }),
                            range: Some(Self::span_to_range(d.name.span)),
                        });
                    }
                }
                Decl::Func(d) => {
                    if Self::position_in_span(line, col, &d.name.span) {
                        let params: Vec<_> =
                            d.params.iter().map(|p| p.name.name.as_str()).collect();
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!(
                                    "**func** `{}({})`",
                                    d.name.name,
                                    params.join(", ")
                                ),
                            }),
                            range: Some(Self::span_to_range(d.name.span)),
                        });
                    }
                }
                Decl::Type(d) => {
                    if Self::position_in_span(line, col, &d.name.span) {
                        let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**type** `{}` = `{}`", d.name.name, type_str),
                            }),
                            range: Some(Self::span_to_range(d.name.span)),
                        });
                    }
                }
                Decl::Property(d) => {
                    if Self::position_in_span(line, col, &d.name.span) {
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**property** `{}`", d.name.name),
                            }),
                            range: Some(Self::span_to_range(d.name.span)),
                        });
                    }
                }
                _ => {}
            }
        }

        // If not on a declaration name, try to find the identifier at cursor
        // and show the declaration's hover info
        if let Some(word) = Self::word_at_position(source, position) {
            for decl in &module.decls {
                match decl {
                    Decl::Var(d) if d.name.name == word => {
                        let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**var** `{}`: `{}`", d.name.name, type_str),
                            }),
                            range: None,
                        });
                    }
                    Decl::Const(d) if d.name.name == word => {
                        let value_str =
                            specl_syntax::pretty::pretty_print_const_value(&d.value);
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**const** `{}`: `{}`", d.name.name, value_str),
                            }),
                            range: None,
                        });
                    }
                    Decl::Action(d) if d.name.name == word => {
                        let params: Vec<_> = d
                            .params
                            .iter()
                            .map(|p| {
                                format!(
                                    "{}: {}",
                                    p.name.name,
                                    specl_syntax::pretty::pretty_print_type(&p.ty)
                                )
                            })
                            .collect();
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!(
                                    "**action** `{}({})`",
                                    d.name.name,
                                    params.join(", ")
                                ),
                            }),
                            range: None,
                        });
                    }
                    Decl::Func(d) if d.name.name == word => {
                        let params: Vec<_> =
                            d.params.iter().map(|p| p.name.name.as_str()).collect();
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!(
                                    "**func** `{}({})`",
                                    d.name.name,
                                    params.join(", ")
                                ),
                            }),
                            range: None,
                        });
                    }
                    Decl::Invariant(d) if d.name.name == word => {
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**invariant** `{}`", d.name.name),
                            }),
                            range: None,
                        });
                    }
                    Decl::Type(d) if d.name.name == word => {
                        let type_str = specl_syntax::pretty::pretty_print_type(&d.ty);
                        return Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: format!("**type** `{}` = `{}`", d.name.name, type_str),
                            }),
                            range: None,
                        });
                    }
                    _ => {}
                }
            }
        }

        None
    }

    fn position_in_span(line: u32, col: u32, span: &Span) -> bool {
        // Span only has start position, so check if position is within the span length
        if line != span.line {
            return false;
        }
        let span_len = span.len() as u32;
        col >= span.column && col < span.column + span_len
    }

    /// Get completions at a position.
    fn get_completions(&self, source: &str, _position: Position) -> Vec<CompletionItem> {
        let mut items = Vec::new();

        // Keywords
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

        // Types
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

        // Add declarations from the current file
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

        // Extract the identifier word at cursor position from source text
        let word = Self::word_at_position(source, position)?;

        // Build declaration name → definition span map
        let mut defs: Vec<(&str, Span)> = Vec::new();
        for decl in &module.decls {
            match decl {
                Decl::Var(d) => defs.push((&d.name.name, d.name.span)),
                Decl::Const(d) => defs.push((&d.name.name, d.name.span)),
                Decl::Action(d) => defs.push((&d.name.name, d.name.span)),
                Decl::Invariant(d) => defs.push((&d.name.name, d.name.span)),
                Decl::Func(d) => defs.push((&d.name.name, d.name.span)),
                Decl::Type(d) => defs.push((&d.name.name, d.name.span)),
                Decl::Property(d) => defs.push((&d.name.name, d.name.span)),
                _ => {}
            }
        }

        // Look up the word
        for (name, span) in &defs {
            if *name == word {
                // Don't jump if already at the definition
                let line = position.line + 1;
                let col = position.character + 1;
                if Self::position_in_span(line, col, span) {
                    return None;
                }
                return Some(Location {
                    uri: uri.clone(),
                    range: Self::span_to_range(*span),
                });
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

        // Check if cursor is on an identifier character
        let bytes = line.as_bytes();
        if col < bytes.len() && !Self::is_ident_char(bytes[col]) {
            return None;
        }

        // Expand left
        let mut start = col;
        while start > 0 && Self::is_ident_char(bytes[start - 1]) {
            start -= 1;
        }

        // Expand right
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
                definition_provider: Some(OneOf::Left(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                // Note: We use push-based diagnostics via publish_diagnostics
                // rather than pull-based textDocument/diagnostic
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

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };

        let content = doc.content.to_string();
        Ok(self.get_hover(&content, position))
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };

        let content = doc.content.to_string();
        let items = self.get_completions(&content, position);
        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };

        let content = doc.content.to_string();
        if let Some(location) = self.get_definition(&content, position, uri) {
            Ok(Some(GotoDefinitionResponse::Scalar(location)))
        } else {
            Ok(None)
        }
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = &params.text_document.uri;

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };

        let content = doc.content.to_string();

        // Parse and pretty print
        let Ok(module) = parse(&content) else {
            return Ok(None);
        };

        let formatted = pretty_print(&module);

        // Replace entire document
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
