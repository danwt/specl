# Specl for Visual Studio Code

Language support for [Specl](https://github.com/danwt/specl) — a specification language and model checker for concurrent and distributed systems.

## Features

- **Diagnostics** — real-time parse and type error reporting
- **Hover** — type and declaration info on mouse-over
- **Completion** — keywords, types, and declarations from the current file
- **Format document** — reformat via `Shift+Option+F` (macOS) or `Shift+Alt+F` (Linux/Windows)
- **Go-to-definition** — `Cmd+Click` or `F12`
- **Syntax highlighting** — full TextMate grammar for Specl

## Requirements

The `specl-lsp` binary must be on your PATH:

```bash
cd specl
cargo install --path crates/specl-lsp
```

Or set the path manually in settings: `specl.serverPath`.

## Settings

| Setting | Default | Description |
|---------|---------|-------------|
| `specl.serverPath` | `""` (searches PATH) | Path to `specl-lsp` binary |
| `specl.trace.server` | `"off"` | LSP trace level: `off`, `messages`, `verbose` |

## Format on Save

Add to your VSCode `settings.json`:

```json
{
  "[specl]": {
    "editor.formatOnSave": true
  }
}
```

## Commands

Open the command palette (`Cmd+Shift+P`) and search:

| Command | Description |
|---------|-------------|
| `Specl: Restart Language Server` | Restart the LSP (useful after rebuilding `specl-lsp`) |
