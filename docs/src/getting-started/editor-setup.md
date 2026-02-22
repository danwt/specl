# Editor Setup

## VSCode

Install the Specl extension from the [VS Marketplace](https://marketplace.visualstudio.com/items?itemName=specl.specl).

### Features

- **Diagnostics** — parse and type errors as you type
- **Hover** — type information on mouse-over
- **Completion** — keywords, types, and declarations
- **Go-to-definition** — `Cmd+Click` / `F12`
- **Find all references** — `Shift+F12`
- **Rename** — `F2`
- **Format** — `Shift+Option+F` (macOS) / `Shift+Alt+F` (Linux/Windows)
- **Document symbols** — outline view of all declarations
- **Inlay hints** — parameter names shown inline at call sites
- **Code lens** — reference counts above action and function declarations
- **Signature help** — parameter info when typing action/function calls
- **Call hierarchy** — incoming/outgoing call relationships
- **Semantic highlighting** — keywords, types, variables, functions

### Format on save

Add to your `settings.json`:

```json
{
    "[specl]": {
        "editor.formatOnSave": true
    }
}
```

### Building from source

If you prefer to build locally:

```bash
cargo install --path crates/specl-lsp
cd editors/vscode && npm install && npm run bundle
npx vsce package && code --install-extension specl-*.vsix
```
