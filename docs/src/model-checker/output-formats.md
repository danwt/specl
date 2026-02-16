# Output Formats

Specl supports several output formats for integration with other tools.

## Default (text)

Human-readable output. This is the default.

```bash
specl check spec.specl -c N=3
```

## JSON

Machine-readable JSON output.

```bash
specl check spec.specl -c N=3 --output json
```

Useful for CI pipelines, scripts, and programmatic analysis of results.

## ITF (Informal Trace Format)

Apalache-compatible trace format.

```bash
specl check spec.specl -c N=3 --output itf
```

This produces traces in the [ITF format](https://apalache-mc.org/docs/adr/015adr-trace.html) used by the Apalache model checker, enabling interoperability between tools.

## Mermaid

Generates Mermaid sequence diagrams from violation traces.

```bash
specl check spec.specl -c N=3 --output mermaid
```

The output can be pasted into any Mermaid-compatible renderer (GitHub markdown, Mermaid Live Editor, etc.) to visualize the sequence of actions.

## Graphviz DOT

Generates a full state graph in DOT format.

```bash
specl check spec.specl -c N=2 --output dot
```

Only practical for small state spaces (< 100 states). Render with:

```bash
specl check spec.specl -c N=2 --output dot | dot -Tpng -o states.png
```

## Diff mode

Not an output format per se, but `--diff` modifies the default text output to show only changed variables in each trace step:

```bash
specl check spec.specl --diff
```

Useful for specs with many variables where full state dumps are hard to read.

## Profiling

`--profile` adds per-action firing counts and timing to the output:

```bash
specl check spec.specl -c N=3 --profile
```
