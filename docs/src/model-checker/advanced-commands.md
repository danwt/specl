# Advanced Commands

Beyond `specl check`, the CLI provides several additional commands.

## `specl info` — spec analysis

Analyze a spec without running the full model checker:

```bash
specl info spec.specl -c N=3
```

Reports actions, variables, constants, state space characteristics, and which optimizations apply.

## `specl estimate` — state space estimation

Estimate the state space size and required resources before committing to a full run:

```bash
specl estimate spec.specl -c N=3
```

## `specl simulate` — random trace simulation

Generate random execution traces without exhaustive exploration:

```bash
specl simulate spec.specl -c N=3
```

Useful for quick smoke testing and understanding system behavior before running the full checker.

## `specl test` — batch checking

Check all `.specl` files in a directory using `// Use:` comments embedded in each file:

```bash
specl test examples/
```

Each spec file contains a comment like:

```specl
// Use: specl check this.specl -c N=2 --no-deadlock
```

The `test` command reads these comments and runs each spec with the specified flags. Useful for CI and regression testing.

## `specl lint` — fast validation

Quick syntax and type check without running the model checker:

```bash
specl lint spec.specl
```

Catches parse errors and type errors without exploring any states.

## `specl format` — code formatter

Format a spec file:

```bash
specl format spec.specl --write    # format in place
specl format spec.specl            # print formatted output to stdout
```

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

See [TLA+ Comparison](../tla-comparison/index.md) for details on the translation.
