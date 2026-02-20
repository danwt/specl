# Advanced Commands

Beyond `specl check`, the CLI provides several additional commands.

## `specl info` — spec analysis and performance guide

Analyze a spec: state space breakdown, time/memory estimates, optimization recommendations:

```bash
specl info spec.specl -c N=3
```

Without a file, prints a comprehensive performance and strategy guide:

```bash
specl info
```

## `specl fmt` — format, lint, and check

Format, lint, or validate a spec file:

```bash
specl fmt spec.specl --write     # format in place
specl fmt spec.specl             # print formatted output to stdout
specl fmt spec.specl --check     # exit 1 if not formatted (CI)
specl fmt spec.specl --lint      # syntax + type + compile check
```

## `specl simulate` — random trace simulation

Generate random execution traces without exhaustive exploration:

```bash
specl simulate spec.specl -c N=3
```

Useful for quick smoke testing and understanding system behavior before running the full checker.

## `specl watch` — file watcher

Re-run the check automatically when the file changes:

```bash
specl watch spec.specl -c N=3
```

## `specl translate` — TLA+ conversion

Convert a TLA+ specification to Specl:

```bash
specl translate spec.tla -o spec.specl
```

Or check a TLA+ file directly (auto-translates then checks):

```bash
specl check spec.tla -c N=3
```

See [TLA+ Comparison](../tla-comparison/index.md) for details on the translation.
