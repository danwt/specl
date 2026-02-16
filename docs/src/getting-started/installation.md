# Installation

Specl is distributed as a Rust crate. You need a working [Rust toolchain](https://rustup.rs/).

## Install from source

```bash
git clone https://github.com/danwt/specl.git
cd specl/specl
cargo install --path crates/specl-cli
```

This gives you the `specl` command.

## Verify the installation

```bash
specl --version
```

## VSCode extension

For editor support (diagnostics, hover, completion, formatting), install from the [VS Marketplace](https://marketplace.visualstudio.com/items?itemName=specl.specl).

Or build from source:

```bash
cargo install --path crates/specl-lsp
cd editors/vscode && npm install && npm run bundle
npx vsce package && code --install-extension specl-*.vsix
```

See [Editor Setup](./editor-setup.md) for configuration details.
