//! Command-line interface for Specl model checker.

// False positive: thiserror/miette derive macros generate code that triggers this
#![allow(unused_assignments)]

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use clap::{CommandFactory, Parser, Subcommand, ValueEnum};
use indicatif::{ProgressBar, ProgressStyle};
use miette::{Diagnostic, NamedSource, SourceSpan};
use notify::{RecursiveMode, Watcher};
use serde::Serialize;
use specl_eval::{Value, VK};
use specl_ir::analyze::analyze;
use specl_ir::compile;
use specl_mc::{
    CheckConfig, CheckOutcome, Explorer, Fingerprint, ProgressCounters, SimulateOutcome, State,
    StateStore,
};
use specl_symbolic::{SpacerProfile, SymbolicConfig, SymbolicError, SymbolicMode, SymbolicOutcome};
use specl_syntax::{parse, pretty_print};
use std::collections::BTreeMap;
use std::fs;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};
use thiserror::Error;
use tracing::info;
use tracing_subscriber::EnvFilter;

/// Output format for check results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum OutputFormat {
    Text,
    Json,
    /// Informal Trace Format (Apalache-compatible trace interchange)
    Itf,
    /// Mermaid sequence diagram (for trace visualization)
    Mermaid,
    /// Graphviz DOT state graph (BFS exploration tree)
    Dot,
}

/// Top-level JSON output for `specl check --output json`.
#[derive(Serialize)]
struct JsonOutput {
    result: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    invariant: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    trace: Option<Vec<JsonTraceStep>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    states_explored: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_depth: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory_mb: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    method: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
    duration_secs: f64,
}

impl JsonOutput {
    fn new(result: &'static str, duration_secs: f64) -> Self {
        Self {
            result,
            invariant: None,
            trace: None,
            states_explored: None,
            max_depth: None,
            memory_mb: None,
            method: None,
            reason: None,
            error: None,
            duration_secs,
        }
    }

    fn with_states(mut self, states: usize, depth: usize) -> Self {
        self.states_explored = Some(states);
        self.max_depth = Some(depth);
        self
    }

    fn with_invariant(mut self, inv: String) -> Self {
        self.invariant = Some(inv);
        self
    }

    fn with_trace(mut self, trace: Vec<JsonTraceStep>) -> Self {
        self.trace = Some(trace);
        self
    }

    fn with_memory(mut self, mb: usize) -> Self {
        self.memory_mb = Some(mb);
        self
    }

    fn with_method(mut self, method: String) -> Self {
        self.method = Some(method);
        self
    }

    fn with_reason(mut self, reason: String) -> Self {
        self.reason = Some(reason);
        self
    }

    fn with_error(mut self, error: String) -> Self {
        self.error = Some(error);
        self
    }
}

/// A single trace step in JSON output.
#[derive(Serialize)]
struct JsonTraceStep {
    step: usize,
    action: String,
    state: BTreeMap<String, serde_json::Value>,
}

/// CLI error with source context for pretty printing.
#[derive(Debug, Error, Diagnostic)]
pub enum CliError {
    #[error("failed to read file: {message}")]
    IoError { message: String },

    #[error("parse error: {message}")]
    #[diagnostic(code(specl::parse_error))]
    ParseError {
        message: String,
        #[source_code]
        src: NamedSource<Arc<String>>,
        #[label("here")]
        span: SourceSpan,
    },

    #[error("type error: {message}")]
    #[diagnostic(code(specl::type_error))]
    TypeError {
        message: String,
        #[source_code]
        src: NamedSource<Arc<String>>,
        #[label("here")]
        span: SourceSpan,
    },

    #[error("compile error: {message}")]
    CompileError { message: String },

    #[error("check error: {message}")]
    CheckError { message: String },

    #[error("{message}")]
    Other { message: String },

    #[error("translation error: {message}")]
    TranslateError { message: String },
}

impl CliError {
    fn from_parse_error(e: specl_syntax::ParseError, source: Arc<String>, filename: &str) -> Self {
        let span = e.span();
        CliError::ParseError {
            message: e.to_string(),
            src: NamedSource::new(filename, source),
            span: (span.start, span.len()).into(),
        }
    }

    fn from_type_error(e: specl_types::TypeError, source: Arc<String>, filename: &str) -> Self {
        let span = e.span();
        CliError::TypeError {
            message: e.to_string(),
            src: NamedSource::new(filename, source),
            span: (span.start, span.len()).into(),
        }
    }
}

type CliResult<T> = Result<T, CliError>;

#[derive(Parser)]
#[command(name = "specl", version)]
#[command(about = "Specl specification language model checker", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse a Specl file and show the AST
    Parse {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },

    /// Type check a Specl file
    Typecheck {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,
    },

    /// Analyze a spec and show profile, recommendations, and action details
    Info {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Constant assignments (name=value)
        #[arg(short, long, value_name = "CONST=VALUE")]
        constant: Vec<String>,
    },

    /// Model check a Specl file
    #[command(
        disable_help_flag = true,
        after_help = "\
Use -v with -h for detailed explanations of every flag and a strategy guide.",
        after_long_help = "\
CHOOSING A STRATEGY
  1. Start small:       specl check spec.specl -c N=2
  2. Analyze first:     specl info spec.specl -c N=2
     Shows state space estimates and recommended flags.
  3. Specl auto-selects BFS or symbolic, and auto-enables POR + symmetry.
  4. For large state spaces (>10M states): add --fast
  5. Scale up gradually: N=2 first, then N=3. State spaces grow exponentially.

EXPLICIT-STATE vs SYMBOLIC
  Explicit-state (default for finite specs): explores every state one by one.
  Guaranteed to find bugs if they exist. Memory-bound by the number of states.

  Symbolic (for large/unbounded specs): encodes the spec as math formulas and
  uses a solver (Z3) to reason about all states at once. Can prove properties
  hold for unbounded state spaces, but may fail or be slow on complex specs.

  Specl picks the right mode automatically. Override with --bfs or --symbolic.

EXAMPLES
  Basic check:          specl check raft.specl -c N=3
  Quick large check:    specl check raft.specl -c N=3 --fast
  Prove unbounded:      specl check raft.specl --symbolic --ic3
  Find bugs fast:       specl check raft.specl -c N=3 --directed
  Debug a specific inv: specl check raft.specl -c N=3 --check-only ElectionSafety
  CI pipeline:          specl check raft.specl -c N=2 --max-time 60 --output json"
    )]
    Check {
        /// Print help (use -v for detailed flag explanations)
        #[arg(short = 'h', long)]
        help: bool,

        /// Input file
        #[arg(value_name = "FILE", required_unless_present = "help")]
        file: Option<PathBuf>,

        /// Constant assignments (name=value)
        #[arg(short, long, value_name = "CONST=VALUE",
            long_help = "\
Set compile-time constants defined in your spec. Repeatable.

Most specs define constants like `const N: Int` for the number of processes.
You must supply values for all unset constants at check time.

Example: specl check raft.specl -c N=3 -c MAX_TERM=5")]
        constant: Vec<String>,

        // -- Mode selection --
        /// Force BFS explicit-state checking
        #[arg(long, help_heading = "Mode",
            long_help = "\
Force explicit-state checking using breadth-first search (BFS).

Explicit-state checking visits every reachable state one by one. It is the
default for specs with finite state spaces. It guarantees finding the shortest
counterexample trace if a bug exists.

You normally don't need this flag — Specl auto-selects the best mode. Use it
to override auto-selection when you want exhaustive exploration even if Specl
would choose symbolic mode.")]
        bfs: bool,

        /// Force symbolic checking (auto-cascades: induction → k-induction → IC3 → BMC)
        #[arg(long, help_heading = "Mode",
            long_help = "\
Force symbolic checking using the Z3 SMT solver.

Instead of visiting states one by one, symbolic checking encodes your entire
spec as mathematical formulas and uses Z3 to reason about all states at once.
This can handle state spaces that are too large or even unbounded for
explicit-state checking.

When you use --symbolic without specifying a technique (--bmc, --inductive,
--k-induction, --ic3), Specl automatically tries techniques in order of
increasing power:
  1. Induction — fastest, proves many simple invariants
  2. k-induction (K=2..5) — stronger, handles more invariants
  3. IC3 — most powerful, can prove almost anything provable
  4. BMC fallback — searches for bugs up to a bounded depth

You can also pick a specific technique with the flags below.")]
        symbolic: bool,

        // -- Explicit-state options --
        /// Maximum states to explore (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State",
            long_help = "\
Stop exploration after visiting this many states. 0 means no limit.

Useful for bounding long-running checks. If the limit is hit before all
states are explored, the result is \"OK (bounded)\" — meaning no bug was
found within the explored portion, but unexplored states may still contain
bugs.

Example: specl check spec.specl -c N=3 --max-states 1000000")]
        max_states: usize,

        /// Maximum depth to explore (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State",
            long_help = "\
Stop exploration at this BFS depth. 0 means no limit.

Depth is the number of action steps from the initial state. A depth limit
of 20 means the checker will explore all states reachable within 20 steps,
but not beyond. Useful for bounding the search when you only care about
short-horizon bugs.")]
        max_depth: usize,

        /// Maximum memory in MB (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State",
            long_help = "\
Stop exploration if memory usage exceeds this limit (in megabytes). 0 means
no limit.

The checker stores every visited state in memory to avoid re-exploring it.
For large state spaces this can use many gigabytes. Set a memory limit to
prevent the checker from consuming all available RAM.

If you're hitting memory limits, consider --fast (10x less memory per state),
--collapse, or --tree for compression.")]
        memory_limit: usize,

        /// Maximum time in seconds (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State",
            long_help = "\
Stop exploration after this many seconds. 0 means no limit.

Useful for CI pipelines or quick smoke checks. If the time limit is hit,
the result is \"OK (bounded)\" — no bug was found within the time budget.

Example: specl check spec.specl -c N=3 --max-time 60")]
        max_time: u64,

        /// Disable deadlock checking
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Don't report states where no action can fire (deadlocks).

A deadlock is a reachable state where none of your actions are enabled — the
system is stuck. By default the checker reports these because they can
indicate bugs (e.g., a lock protocol that gets stuck).

However, most protocol specs naturally have \"finished\" states where nothing
happens (e.g., consensus reached, all messages delivered). These are harmless
deadlocks. Use --no-deadlock to suppress these false positives.

This is one of the most commonly needed flags for protocol specs.")]
        no_deadlock: bool,

        /// Disable parallel exploration
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Run the checker on a single thread instead of using all available cores.

By default the checker parallelizes BFS exploration across all CPU cores for
speed. Single-threaded mode produces deterministic results and is useful for
debugging or benchmarking.")]
        no_parallel: bool,

        /// Number of threads (0 = all available)
        #[arg(long, default_value = "0", help_heading = "Explicit-State",
            long_help = "\
Set the number of threads for parallel exploration. 0 means use all
available CPU cores (the default).

Use this to limit CPU usage, e.g., --threads 4 to use only 4 cores.")]
        threads: usize,

        /// Partial order reduction — skip redundant interleavings
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Skip redundant orderings of independent actions.

When two actions don't affect each other (e.g., process A updates its own
local state, process B updates its own local state), the checker normally
explores both orderings: A-then-B and B-then-A. Since both lead to the
same result, one exploration is wasted work.

POR detects these independent action pairs and only explores one ordering,
without missing any bugs.

  Typical reduction: 2-10x fewer states
  Best for: specs where processes mostly update their own state
  Safe to always enable — no overhead when actions are all dependent
  Auto-enabled when Specl detects >30% of action pairs are independent")]
        por: bool,

        /// Symmetry reduction — collapse equivalent process permutations
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Group equivalent states that differ only in process identity.

When your spec models N identical processes (e.g., Dict[0..N, State]),
many states are just rearrangements of each other. For example, with 3
processes: \"process 0 is leader, 1 and 2 are followers\" is equivalent to
\"process 2 is leader, 0 and 1 are followers\". The bug-finding power is
the same — only the label on the leader differs.

Symmetry reduction detects these equivalent states and only explores one
representative from each group.

  Typical reduction: up to N! (factorial). For N=4 that's 24x fewer states
  Best for: specs using Dict[0..N, T] where processes are interchangeable
  Auto-enabled when Specl detects symmetric Dict patterns")]
        symmetry: bool,

        /// Fingerprint-only mode — 10x less memory, re-explores for traces on violation
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Store only a compact 8-byte hash (fingerprint) per state instead of the
full state data.

Normally the checker stores the complete data for every visited state so it
can reconstruct the exact sequence of steps leading to a bug. This uses a
lot of memory (typically 100-500 bytes per state).

Fast mode stores only an 8-byte fingerprint per state, using roughly 10x
less memory. The tradeoff: if a bug is found, the checker must re-run with
full storage to reconstruct the counterexample trace. This re-run happens
automatically.

  Best for: large state spaces where you're running out of memory
  Example: specl check spec.specl -c N=3 --fast")]
        fast: bool,

        /// Bloom filter — fixed memory, probabilistic. UNSOUND: may miss bugs
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Use a bloom filter for visited-state tracking instead of a hash table.

A bloom filter uses a fixed amount of memory (set by --bloom-bits) regardless
of how many states are explored. It can tell you \"definitely not visited\" or
\"probably visited\" — meaning it may occasionally think a state was already
visited when it wasn't, causing that state to be skipped.

WARNING: This makes the checker UNSOUND — it may miss bugs because skipped
states could contain violations. Use this only for exploratory bug-hunting
on very large state spaces where you can't afford the memory for exact
tracking. Never rely on a bloom-filter OK result as proof of correctness.

  Memory: fixed at 2^bloom-bits bits (default: 128 MiB)
  Use with: --bloom-bits to control memory/accuracy tradeoff")]
        bloom: bool,

        /// Bloom filter size as log2(bits). Only with --bloom
        #[arg(long, default_value = "30", help_heading = "Explicit-State",
            long_help = "\
Set the bloom filter size as log2(number of bits). Only used with --bloom.

  --bloom-bits 27 = 16 MiB
  --bloom-bits 28 = 32 MiB
  --bloom-bits 29 = 64 MiB
  --bloom-bits 30 = 128 MiB (default)
  --bloom-bits 31 = 256 MiB
  --bloom-bits 32 = 512 MiB

Larger filters have lower false-positive rates (fewer skipped states) but
use more memory. The default of 128 MiB works well for most exploratory
checks.")]
        bloom_bits: u32,

        /// Collapse compression — per-variable interning, traces supported
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Compress stored states by interning each variable's value separately.

Instead of storing the full state as one block, collapse compression stores
each variable's value in a shared pool and references it by index. States
that share many variable values (common in practice) use significantly less
memory.

  Memory savings: typically 2-5x vs full storage
  Traces: fully supported (unlike --fast)
  Best for: specs with many variables where most don't change each step")]
        collapse: bool,

        /// Tree compression — hierarchical hash table, best compression, traces supported
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Compress stored states using a hierarchical hash table (LTSmin-style tree
compression).

This is the most memory-efficient storage mode that still supports full
counterexample traces. It groups variable values hierarchically and shares
common subtrees across states.

  Memory savings: typically 3-10x vs full storage
  Traces: fully supported
  Overhead: slightly slower than uncompressed due to tree lookups
  Best for: very large state spaces where you need both memory efficiency
  and counterexample traces")]
        tree: bool,

        /// Directed checking — prioritize states closest to violation
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Use a priority queue instead of a plain FIFO queue for BFS exploration,
exploring states that look closest to an invariant violation first.

The checker uses heuristics to estimate how \"close\" each state is to
violating an invariant and explores the most promising states first. This
can find bugs much faster than standard BFS for specs where violations
require specific combinations of variable values.

  Best for: finding bugs quickly in large state spaces
  Tradeoff: if no bug exists, explores the same number of states as BFS
  Note: counterexample traces may not be the shortest possible")]
        directed: bool,

        /// Incremental checking — cache fingerprints to disk across runs
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Save explored state fingerprints to disk so subsequent runs can skip
previously explored states.

When you re-run the checker after making small changes to your spec, most
states are the same as before. Incremental mode loads the fingerprints
from the previous run and skips any states that were already explored.

  Best for: iterative development where you check, edit, re-check
  Cache location: .specl-cache/ in the current directory
  Note: only valid if spec semantics haven't changed; Specl invalidates
  the cache when it detects structural spec changes")]
        incremental: bool,

        /// Swarm verification — N parallel instances with shuffled action orders
        #[arg(long, value_name = "N", help_heading = "Explicit-State",
            long_help = "\
Run N independent checker instances in parallel, each exploring actions in
a different random order.

Standard BFS always explores actions in the same order, which means it
finds bugs along one particular exploration path first. Swarm verification
shuffles the action order for each instance, covering different parts of
the state space in parallel. The first instance to find a bug reports it.

  Best for: large state spaces where you suspect a bug exists but standard
  BFS is too slow to reach it
  Example: specl check spec.specl -c N=3 --swarm 8")]
        swarm: Option<usize>,

        // -- Symbolic (Z3) options --
        /// Bounded model checking — search for bugs up to K steps deep
        #[arg(long, help_heading = "Symbolic (Z3)",
            long_help = "\
Search for invariant violations within a bounded number of steps.

BMC encodes the question \"can a bug happen within K steps?\" as a formula
and asks the Z3 solver to find an assignment that makes it true. If Z3
finds one, you get a counterexample trace. If not, no bug exists within
K steps — but bugs at deeper steps might still exist.

Set the depth bound with --bmc-depth (default: unlimited, meaning the
checker incrementally increases K until it finds a bug or times out).

  Best for: finding bugs quickly, especially shallow ones (< 20 steps)
  Does NOT prove correctness — only that no bug exists within K steps
  Example: specl check spec.specl --bmc --bmc-depth 10")]
        bmc: bool,

        /// BMC depth bound (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Symbolic (Z3)",
            long_help = "\
Maximum depth for bounded model checking (number of transition steps to
unroll). 0 means no limit — the checker increases depth incrementally
until a bug is found or the solver times out.

Only used with --bmc or when symbolic auto-cascade falls back to BMC.

Example: --bmc --bmc-depth 20 checks all executions up to 20 steps.")]
        bmc_depth: usize,

        /// Inductive invariant checking — single-step proof
        #[arg(long, help_heading = "Symbolic (Z3)",
            long_help = "\
Try to prove your invariant holds forever using a single induction step.

The idea: if the invariant holds in the initial state AND any single action
taken from an invariant-satisfying state produces another invariant-satisfying
state, then the invariant holds in ALL reachable states forever.

This is the fastest symbolic technique when it works. However, many real
invariants aren't \"inductive\" — the induction step fails because the solver
considers unreachable states that satisfy the invariant but lead to a
violation. In practice, you often need to add strengthening invariants to
make the main invariant inductive, or use a more powerful technique like
k-induction or IC3.

  Speed: very fast (single solver call)
  Proves: invariant holds forever (all reachable states, any depth)
  Limitation: fails for non-inductive invariants (common in practice)")]
        inductive: bool,

        /// k-induction — stronger induction with K-step base case
        #[arg(long, value_name = "K", help_heading = "Symbolic (Z3)",
            long_help = "\
Prove your invariant holds forever using k-step induction.

Regular induction assumes the invariant held for 1 step, then checks the
next step. k-induction assumes the invariant held for K consecutive steps,
then checks step K+1. This extra context rules out more unreachable states,
making the proof succeed for invariants that plain induction can't handle.

If k-induction succeeds at any K, the invariant is guaranteed to hold in
ALL reachable states at ANY depth — it's a complete proof of correctness.

  Try K=2 first, then increase to 3, 4, 5 if it fails
  Proves: invariant holds forever (complete proof)
  Slower than plain induction, faster than IC3
  Example: specl check spec.specl --k-induction 3")]
        k_induction: Option<usize>,

        /// IC3 — unbounded verification, most powerful symbolic technique
        #[arg(long, help_heading = "Symbolic (Z3)",
            long_help = "\
Prove your invariant holds forever using IC3 (also called PDR / Property
Directed Reachability).

IC3 is the most powerful automated verification technique available. It
works by building up a proof layer by layer, progressively discovering
which states are reachable and which are not. Unlike BMC, it doesn't need
a depth bound — it either proves the invariant holds forever, finds a
counterexample, or reports \"unknown\".

IC3 can prove invariants that induction and k-induction cannot, but it is
slower and may time out on very complex specs. Use --timeout to limit how
long the solver runs.

  Proves: invariant holds forever (complete proof, no depth bound)
  May return \"unknown\" for very complex specs
  Use --timeout to limit solver time
  Example: specl check spec.specl --ic3 --timeout 300")]
        ic3: bool,

        /// Portfolio — run BMC, k-induction, IC3 in parallel, first result wins
        #[arg(long, help_heading = "Symbolic (Z3)",
            long_help = "\
Run BMC, k-induction, and IC3 simultaneously in parallel. The first
technique to produce a result (either a proof or a counterexample) wins,
and the others are cancelled.

This is useful when you don't know which technique will work best for your
spec. It uses more CPU but minimizes wall-clock time.

  Best for: when you want the fastest possible answer and have CPU to spare
  Example: specl check spec.specl --portfolio --timeout 300")]
        portfolio: bool,

        /// Golem CHC solver — external alternative to Z3 Spacer
        #[arg(long, help_heading = "Symbolic (Z3)",
            long_help = "\
Use the Golem CHC solver instead of Z3's built-in Spacer engine for IC3.

Golem is an external solver that sometimes succeeds where Z3 Spacer fails
(and vice versa). Requires the `golem` binary to be installed and on your
PATH.

  Best for: specs where --ic3 returns \"unknown\" — try Golem as an alternative")]
        golem: bool,

        /// Max sequence length for symbolic Seq[T] encoding
        #[arg(long, default_value = "5", help_heading = "Symbolic (Z3)",
            long_help = "\
Maximum length of Seq[T] (list) values in symbolic mode.

Symbolic solvers can't handle unbounded-length sequences, so Specl encodes
them as fixed-capacity arrays. This sets the maximum length. Increase if
your spec uses longer sequences; decrease for faster solving.")]
        seq_bound: usize,

        /// Spacer parameter profile: default, fast, or thorough
        #[arg(long, default_value = "default", help_heading = "Symbolic (Z3)",
            long_help = "\
Tuning profile for Z3's Spacer engine, used by --ic3.

  default  — balanced settings, good for most specs
  fast     — aggressive timeouts, less thorough but faster
  thorough — more patient, explores more proof strategies

Only affects --ic3 and --portfolio modes.")]
        spacer_profile: String,

        /// Symbolic solver timeout in seconds (0 = no timeout)
        #[arg(long, default_value = "0", help_heading = "Symbolic (Z3)",
            long_help = "\
Time limit for the Z3 symbolic solver, in seconds. 0 means no limit.

When using symbolic techniques (especially --ic3), the solver may run for
a very long time without producing a result. Set a timeout to get back
control. If the solver times out, the result is \"unknown\".

Example: specl check spec.specl --ic3 --timeout 60")]
        timeout: u64,

        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,

        /// Suppress spec analysis and recommendations
        #[arg(short, long,
            long_help = "\
Suppress the spec analysis summary that is printed before checking begins.

By default, Specl prints a brief analysis of your spec (number of variables,
actions, estimated state space) and recommends optimization flags. Use -q
to hide this and only show the check result.")]
        quiet: bool,

        /// Disable auto-enabling of optimizations (POR, symmetry)
        #[arg(long,
            long_help = "\
Prevent Specl from automatically enabling POR and symmetry reduction.

By default, Specl analyzes your spec and automatically enables --por when
it detects independent actions, and --symmetry when it detects symmetric
process patterns. Use --no-auto to disable this behavior and only use
optimizations you explicitly request.

Useful for benchmarking or when auto-detection makes incorrect choices.")]
        no_auto: bool,

        /// Output format: text, json, itf, mermaid, dot
        #[arg(long, value_enum, default_value = "text",
            long_help = "\
Choose the output format for check results and counterexample traces.

  text    — human-readable (default)
  json    — machine-readable JSON for CI/scripting
  itf     — Informal Trace Format, compatible with Apalache tooling
  mermaid — Mermaid sequence diagram for visualizing traces
  dot     — Graphviz DOT graph of the explored state space (small specs only)")]
        output: OutputFormat,

        /// Show per-action firing counts and phase timing
        #[arg(long, help_heading = "Explicit-State",
            long_help = "\
Print a profiling breakdown after checking completes.

Shows how many times each action fired, how much time was spent in each
phase (compilation, exploration, trace reconstruction), and per-action
timing. Useful for understanding which actions dominate the state space
and where time is spent.")]
        profile: bool,

        /// Only check specific invariants (repeatable, by name)
        #[arg(
            long = "check-only",
            value_name = "INVARIANT",
            help_heading = "Explicit-State",
            long_help = "\
Check only the named invariant(s), skipping all others. Repeatable.

Useful when your spec has many invariants but you want to focus on one,
or when some invariants are known to be violated and you want to check
others independently.

Example: specl check spec.specl --check-only Safety --check-only Liveness"
        )]
        check_only: Vec<String>,

        /// Show only changed variables in traces
        #[arg(long,
            long_help = "\
In counterexample traces, only show variables whose values changed in each
step, rather than printing the full state.

Makes long traces much easier to read by highlighting what actually changed
at each action step. Unchanged variables are omitted.")]
        diff: bool,
    },

    /// Format a Specl file
    Format {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Write output to file instead of stdout
        #[arg(short, long)]
        write: bool,
    },

    /// Watch a Specl file and re-check on changes
    Watch {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Constant assignments (name=value)
        #[arg(short, long, value_name = "CONST=VALUE")]
        constant: Vec<String>,

        /// Maximum number of states to explore (0 = unlimited)
        #[arg(long, default_value = "0")]
        max_states: usize,

        /// Maximum depth to explore (0 = unlimited)
        #[arg(long, default_value = "0")]
        max_depth: usize,

        /// Disable deadlock checking
        #[arg(long)]
        no_deadlock: bool,
    },

    /// Translate a TLA+ specification to Specl
    Translate {
        /// Input TLA+ file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Output file (default: stdout)
        #[arg(short, long, value_name = "OUTPUT")]
        output: Option<PathBuf>,
    },

    /// Fast syntax, type, and compile check without model checking
    Lint {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Constant assignments (name=value)
        #[arg(short, long, value_name = "CONST=VALUE")]
        constant: Vec<String>,

        /// Output format (text or json)
        #[arg(long, value_enum, default_value = "text")]
        output: OutputFormat,
    },

    /// Simulate a random trace through the state space
    Simulate {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Constant assignments (name=value)
        #[arg(short, long, value_name = "CONST=VALUE")]
        constant: Vec<String>,

        /// Maximum number of steps to simulate
        #[arg(long, default_value = "100")]
        steps: usize,

        /// Random seed for reproducibility
        #[arg(long, default_value = "0")]
        seed: u64,

        /// Output format (text or json)
        #[arg(long, value_enum, default_value = "text")]
        output: OutputFormat,
    },

    /// Show comprehensive performance guide for writing fast specs and choosing flags
    PerfGuide,

    /// Estimate state space size and resource requirements before checking
    Estimate {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Constant assignments (name=value)
        #[arg(short, long, value_name = "CONST=VALUE")]
        constant: Vec<String>,
    },

    /// Batch check all .specl files in a directory using their // Use: comments
    Test {
        /// Directory containing .specl files (default: examples/)
        #[arg(value_name = "DIR")]
        dir: Option<PathBuf>,

        /// Maximum states per spec (overrides // Use: comment, 0 = use comment value)
        #[arg(long, default_value = "0")]
        max_states: usize,

        /// Maximum time per spec in seconds (0 = unlimited)
        #[arg(long, default_value = "60")]
        max_time: u64,
    },
}

fn main() {
    // Install miette's fancy error handler
    miette::set_hook(Box::new(|_| {
        Box::new(
            miette::MietteHandlerOpts::new()
                .terminal_links(true)
                .unicode(true)
                .context_lines(2)
                .build(),
        )
    }))
    .ok();

    let cli = Cli::parse();

    // Initialize logging
    let filter = if matches!(
        &cli.command,
        Commands::Parse { verbose: true, .. } | Commands::Check { verbose: true, .. }
    ) {
        EnvFilter::new("debug")
    } else if matches!(&cli.command, Commands::Test { .. }) {
        EnvFilter::new("error")
    } else {
        EnvFilter::new("info")
    };

    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_writer(std::io::stderr)
        .with_target(false)
        .without_time()
        .init();

    let result = match cli.command {
        Commands::Parse { file, verbose } => cmd_parse(&file, verbose),
        Commands::Typecheck { file } => cmd_typecheck(&file),
        Commands::Info { file, constant } => cmd_info(&file, &constant),
        Commands::Check {
            help,
            file,
            constant,
            bfs,
            symbolic,
            max_states,
            max_depth,
            memory_limit,
            max_time,
            no_deadlock,
            no_parallel,
            threads,
            por,
            symmetry,
            fast,
            bloom,
            bloom_bits,
            collapse,
            tree,
            directed,
            incremental,
            swarm,
            bmc,
            bmc_depth,
            inductive,
            k_induction,
            ic3,
            portfolio,
            golem,
            seq_bound,
            spacer_profile,
            timeout,
            verbose,
            quiet,
            no_auto,
            output,
            profile,
            check_only,
            diff,
        } if help => {
            let mut cmd = Cli::command();
            let check_cmd = cmd.find_subcommand_mut("check").unwrap();
            if verbose {
                check_cmd.write_long_help(&mut std::io::stdout()).unwrap();
            } else {
                check_cmd.write_help(&mut std::io::stdout()).unwrap();
            }
            println!();
            Ok(())
        }
        Commands::Check {
            file,
            constant,
            bfs,
            symbolic,
            max_states,
            max_depth,
            memory_limit,
            max_time,
            no_deadlock,
            no_parallel,
            threads,
            por,
            symmetry,
            fast,
            bloom,
            bloom_bits,
            collapse,
            tree,
            directed,
            incremental,
            swarm,
            bmc,
            bmc_depth,
            inductive,
            k_induction,
            ic3,
            portfolio,
            golem,
            seq_bound,
            spacer_profile,
            timeout,
            verbose,
            quiet,
            no_auto,
            output,
            profile,
            check_only,
            diff,
            ..
        } => {
            let file = file.unwrap();
            let json = output == OutputFormat::Json;
            let quiet = quiet || output != OutputFormat::Text;

            let specific_symbolic =
                bmc || inductive || k_induction.is_some() || ic3 || portfolio || golem;
            let specific_explicit = por
                || symmetry
                || fast
                || bloom
                || collapse
                || tree
                || directed
                || incremental
                || swarm.is_some()
                || max_states > 0
                || max_depth > 0
                || memory_limit > 0
                || max_time > 0
                || !check_only.is_empty();

            let use_symbolic = symbolic || specific_symbolic;
            let use_bfs = bfs || specific_explicit;

            if use_symbolic && use_bfs {
                if output != OutputFormat::Text {
                    let out = JsonOutput::new("error", 0.0).with_error(
                        "cannot combine --symbolic/--bfs flags or their sub-options".into(),
                    );
                    println!("{}", serde_json::to_string(&out).unwrap());
                } else {
                    eprintln!("Error: cannot combine --symbolic/--bfs flags or their sub-options");
                }
                std::process::exit(1);
            }

            let sp = match spacer_profile.as_str() {
                "fast" => SpacerProfile::Fast,
                "thorough" => SpacerProfile::Thorough,
                "mbp" | "mbp-aggressive" => SpacerProfile::MbpAggressive,
                "pdr" | "pdr-flexible" => SpacerProfile::PdrFlexible,
                s if s.starts_with("seed:") => {
                    let seed = s[5..].parse::<u32>().unwrap_or(42);
                    SpacerProfile::Seeded(seed)
                }
                _ => SpacerProfile::Default,
            };

            let inner = if use_symbolic {
                cmd_check_symbolic(
                    &file,
                    &constant,
                    bmc_depth,
                    bmc,
                    inductive,
                    k_induction,
                    ic3,
                    portfolio,
                    golem,
                    seq_bound,
                    sp,
                    timeout,
                    json,
                )
            } else if use_bfs {
                cmd_check(
                    &file,
                    &constant,
                    max_states,
                    max_depth,
                    memory_limit,
                    max_time,
                    !no_deadlock,
                    !no_parallel,
                    threads,
                    por,
                    symmetry,
                    fast,
                    bloom,
                    bloom_bits,
                    collapse,
                    tree,
                    directed,
                    incremental,
                    verbose,
                    quiet,
                    no_auto,
                    output,
                    swarm,
                    profile,
                    check_only.clone(),
                    diff,
                )
            } else {
                // Auto-select: analyze spec to decide BFS vs symbolic
                let auto_symbolic = auto_select_symbolic(&file, &constant);
                if auto_symbolic {
                    if !quiet {
                        println!("Auto-selected: symbolic checking (unbounded types detected)");
                    }
                    cmd_check_symbolic(
                        &file, &constant, bmc_depth, false, false, None, false, false, false,
                        seq_bound, sp, timeout, json,
                    )
                } else {
                    cmd_check(
                        &file,
                        &constant,
                        max_states,
                        max_depth,
                        memory_limit,
                        max_time,
                        !no_deadlock,
                        !no_parallel,
                        threads,
                        por,
                        symmetry,
                        fast,
                        bloom,
                        bloom_bits,
                        collapse,
                        tree,
                        directed,
                        incremental,
                        verbose,
                        quiet,
                        no_auto,
                        output,
                        swarm,
                        profile,
                        check_only,
                        diff,
                    )
                }
            };
            // In non-text mode, emit errors as JSON instead of miette
            if output != OutputFormat::Text {
                if let Err(e) = inner {
                    let out = JsonOutput::new("error", 0.0).with_error(e.to_string());
                    println!("{}", serde_json::to_string(&out).unwrap());
                    std::process::exit(1);
                }
                Ok(())
            } else {
                inner
            }
        }
        Commands::Lint {
            file,
            constant,
            output,
        } => cmd_lint(&file, &constant, output),
        Commands::Simulate {
            file,
            constant,
            steps,
            seed,
            output,
        } => cmd_simulate(&file, &constant, steps, seed, output),
        Commands::Format { file, write } => cmd_format(&file, write),
        Commands::Watch {
            file,
            constant,
            max_states,
            max_depth,
            no_deadlock,
        } => cmd_watch(&file, &constant, max_states, max_depth, !no_deadlock),
        Commands::Translate { file, output } => cmd_translate(&file, output.as_ref()),
        Commands::PerfGuide => cmd_perf_guide(),
        Commands::Estimate { file, constant } => cmd_estimate(&file, &constant),
        Commands::Test {
            dir,
            max_states,
            max_time,
        } => cmd_test(dir.as_ref(), max_states, max_time),
    };

    if let Err(e) = result {
        eprintln!("{:?}", miette::Report::new(e));
        std::process::exit(1);
    }
}

fn cmd_parse(file: &PathBuf, verbose: bool) -> CliResult<()> {
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;

    if verbose {
        println!("{:#?}", module);
    } else {
        println!("module {}", module.name.name);
        println!("  {} declarations", module.decls.len());

        for decl in &module.decls {
            match decl {
                specl_syntax::Decl::Const(d) => println!("    const {}", d.name.name),
                specl_syntax::Decl::Var(d) => println!("    var {}", d.name.name),
                specl_syntax::Decl::Type(d) => println!("    type {}", d.name.name),
                specl_syntax::Decl::Action(d) => println!("    action {}", d.name.name),
                specl_syntax::Decl::Func(d) => println!("    func {}", d.name.name),
                specl_syntax::Decl::Init(_) => println!("    init"),
                specl_syntax::Decl::Invariant(d) => println!("    invariant {}", d.name.name),
                specl_syntax::Decl::Property(d) => println!("    property {}", d.name.name),
                specl_syntax::Decl::Fairness(d) => {
                    println!("    fairness ({} constraints)", d.constraints.len())
                }
                specl_syntax::Decl::Use(_) => println!("    use"),
                specl_syntax::Decl::View(d) => {
                    let names: Vec<_> = d.variables.iter().map(|v| v.name.as_str()).collect();
                    println!("    view {{ {} }}", names.join(", "))
                }
            }
        }
    }

    println!("parse: ok");
    Ok(())
}

fn cmd_typecheck(file: &PathBuf) -> CliResult<()> {
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;

    specl_types::check_module(&module)
        .map_err(|e| CliError::from_type_error(e, source.clone(), &filename))?;

    println!("typecheck: ok");
    Ok(())
}

fn cmd_info(file: &PathBuf, constants: &[String]) -> CliResult<()> {
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;
    specl_types::check_module(&module)
        .map_err(|e| CliError::from_type_error(e, source.clone(), &filename))?;
    let spec = compile(&module).map_err(|e| CliError::CompileError {
        message: e.to_string(),
    })?;
    let consts = parse_constants(constants, &spec)?;

    let profile = analyze(&spec);

    // Header
    println!();
    println!("Module: {}", module.name.name);
    println!("  Variables: {}", profile.num_vars);
    println!("  Actions: {}", profile.num_actions);
    println!("  Invariants: {}", profile.num_invariants);
    if !spec.invariants.is_empty() {
        let inv_names: Vec<&str> = spec
            .invariants
            .iter()
            .map(|inv| inv.name.as_str())
            .collect();
        println!("    Names: {}", inv_names.join(", "));
    }

    // Constants
    if !spec.consts.is_empty() {
        let const_strs: Vec<String> = spec
            .consts
            .iter()
            .map(|c| format!("{}={}", c.name, consts[c.index]))
            .collect();
        println!("  Constants: {}", const_strs.join(", "));
    }

    // Per-variable state space breakdown
    println!();
    println!("State Space Breakdown:");
    let total_bound = profile.state_space_bound;
    // log(total) for computing contribution percentages (multiplicative -> log-additive)
    let log_total = total_bound.map(|t| (t as f64).ln());
    for (name, ty, domain) in &profile.var_domain_sizes {
        match domain {
            Some(size) => {
                let pct_str = match log_total {
                    Some(lt) if lt > 0.0 && *size > 1 => {
                        let pct = ((*size as f64).ln() / lt) * 100.0;
                        format!("  ({:.0}% of state space)", pct)
                    }
                    _ => String::new(),
                };
                println!(
                    "  {}: {}  {} values{}",
                    name,
                    ty,
                    format_large_number(*size),
                    pct_str
                );
            }
            None => {
                println!("  {}: {}  unbounded", name, ty);
            }
        }
    }
    match total_bound {
        Some(b) => println!("  Total: ~{} states", format_large_number(b)),
        None => println!("  Total: unbounded"),
    }

    // Action details with hottest action identification
    println!();
    println!("Action Analysis:");
    let total_combos: u64 = profile
        .action_param_counts
        .iter()
        .filter_map(|(_, c)| *c)
        .sum();
    for (name, combos) in &profile.action_param_counts {
        let combo_str = match combos {
            Some(c) => format_large_number(*c as u128),
            None => "unbounded".to_string(),
        };
        let pct_str = match (combos, total_combos) {
            (Some(c), t) if t > 0 => format!("  ({:.0}%)", *c as f64 / t as f64 * 100.0),
            _ => String::new(),
        };
        println!("  {:30} {} param combos{}", name, combo_str, pct_str);
    }
    if total_combos > 0 {
        if let Some((hottest, Some(hot_combos))) = profile
            .action_param_counts
            .iter()
            .max_by_key(|(_, c)| c.unwrap_or(0))
        {
            let hot_pct = *hot_combos as f64 / total_combos as f64 * 100.0;
            if hot_pct > 40.0 && profile.action_param_counts.len() > 1 {
                println!(
                    "  Tip: '{}' dominates ({:.0}%) — ensure it has selective require guards",
                    hottest, hot_pct
                );
            }
        }
    }

    // Nesting depth analysis
    if !profile.var_nesting_depths.is_empty() {
        println!();
        println!("Nesting Analysis:");
        for (name, depth) in &profile.var_nesting_depths {
            let severity = if *depth >= 3 { "WARNING" } else { "Note" };
            println!(
                "  {}: '{}' has {}-level dict nesting",
                severity, name, depth
            );
            if *depth >= 3 {
                println!("    Dict[K1, Dict[K2, Dict[K3, V]]] has |V|^(K1*K2*K3) states");
                println!(
                    "    Consider flattening to Dict[(K1,K2,K3), V] or using a simpler encoding"
                );
            } else {
                println!("    OK for most specs, but watch state space with large ranges");
            }
        }
    }

    // Storage mode recommendation
    if let Some(ref rec) = profile.storage_recommendation {
        println!();
        println!("Storage: {}", rec);
    }

    // Independence / symmetry
    println!();
    println!("Optimizations:");
    let independence_pct = (profile.independence_ratio * 100.0) as u32;
    println!("  POR: {}% independent pairs", independence_pct);
    if profile.has_symmetry {
        let sizes: Vec<String> = profile
            .symmetry_domain_sizes
            .iter()
            .map(|s| s.to_string())
            .collect();
        println!("  Symmetry: domains of size {}", sizes.join(", "));
    } else {
        println!("  Symmetry: none detected");
    }
    if profile.has_refinable_pairs {
        println!("  Instance POR: refinable pairs detected (keyed Dict access)");
    }

    // Warnings with fix hints
    if !profile.warnings.is_empty() {
        println!();
        println!("Warnings:");
        for w in &profile.warnings {
            println!("  {}", w);
            println!("    Fix: {}", w.fix_hint());
        }
    }

    // Recommendations
    if !profile.recommendations.is_empty() {
        println!();
        println!("Recommendations:");
        for r in &profile.recommendations {
            println!("  {}", r);
        }
    }

    // Suggested command — derive flags from recommendations
    println!();
    let const_flags: Vec<String> = spec
        .consts
        .iter()
        .map(|c| format!("-c {}={}", c.name, consts[c.index]))
        .collect();
    let mut flags = const_flags;
    for r in &profile.recommendations {
        match r {
            specl_ir::analyze::Recommendation::EnablePor { .. } => {
                flags.push("--por".to_string());
            }
            specl_ir::analyze::Recommendation::EnableSymmetry { .. } => {
                flags.push("--symmetry".to_string());
            }
            specl_ir::analyze::Recommendation::EnableFast { .. } => {
                flags.push("--fast".to_string());
            }
            specl_ir::analyze::Recommendation::UseSymbolic { .. } => {
                flags.push("--bmc".to_string());
            }
        }
    }
    println!("Suggested: specl check {} {}", filename, flags.join(" "));

    println!();
    Ok(())
}

/// Quick analysis pass to determine if symbolic checking should be auto-selected.
/// Returns true if the spec has unbounded types. Falls back to false on any error
/// (the actual check command will report the error properly).
fn auto_select_symbolic(file: &PathBuf, constants: &[String]) -> bool {
    let source = match fs::read_to_string(file) {
        Ok(s) => Arc::new(s),
        Err(_) => return false,
    };
    let module = match parse(&source) {
        Ok(m) => m,
        Err(_) => return false,
    };
    if specl_types::check_module(&module).is_err() {
        return false;
    }
    let spec = match compile(&module) {
        Ok(s) => s,
        Err(_) => return false,
    };
    if parse_constants(constants, &spec).is_err() {
        return false;
    }
    let profile = analyze(&spec);
    profile
        .warnings
        .iter()
        .any(|w| matches!(w, specl_ir::analyze::Warning::UnboundedType { .. }))
}

fn cmd_check(
    file: &PathBuf,
    constants: &[String],
    max_states: usize,
    max_depth: usize,
    memory_limit_mb: usize,
    max_time_secs: u64,
    check_deadlock: bool,
    parallel: bool,
    num_threads: usize,
    use_por: bool,
    use_symmetry: bool,
    fast_check: bool,
    bloom: bool,
    bloom_bits: u32,
    collapse: bool,
    tree: bool,
    directed: bool,
    incremental: bool,
    _verbose: bool,
    quiet: bool,
    no_auto: bool,
    output_format: OutputFormat,
    swarm: Option<usize>,
    profile: bool,
    check_only_invariants: Vec<String>,
    diff_traces: bool,
) -> CliResult<()> {
    let json = output_format != OutputFormat::Text;
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    info!("parsing...");
    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;

    info!("type checking...");
    specl_types::check_module(&module)
        .map_err(|e| CliError::from_type_error(e, source.clone(), &filename))?;

    info!("compiling...");
    let spec = compile(&module).map_err(|e| CliError::CompileError {
        message: e.to_string(),
    })?;

    // Parse constants
    let consts = parse_constants(constants, &spec)?;

    // Extract variable and action names for trace formatting
    let var_names: Vec<String> = spec.vars.iter().map(|v| v.name.clone()).collect();
    let action_names: Vec<String> = spec.actions.iter().map(|a| a.name.clone()).collect();

    // Spec analysis, recommendations, and auto-enable
    let spec_profile = analyze(&spec);
    if !quiet {
        print_profile(&spec_profile, use_por, use_symmetry);
    }

    // Warn about unbounded types (BFS may still work if runtime values are bounded by init/actions)
    let unbounded_warnings: Vec<_> = spec_profile
        .warnings
        .iter()
        .filter(|w| matches!(w, specl_ir::analyze::Warning::UnboundedType { .. }))
        .collect();
    if !unbounded_warnings.is_empty() && !quiet {
        eprintln!("Note: spec has types the checker considers unbounded (Dict[Int, ...]).");
        eprintln!(
            "  BFS proceeds because runtime values are bounded by init and action parameters."
        );
        eprintln!("  If checking hangs, use --bmc for symbolic checking instead.");
    }

    let mut actual_por = use_por;
    let mut actual_symmetry = use_symmetry;
    let mut actual_fast = fast_check;
    let mut actual_collapse = collapse;

    // Check if user set any explicit storage/strategy flags
    let user_has_explicit_storage = fast_check || bloom || collapse || tree || directed;

    if !no_auto {
        if !use_por && spec_profile.independence_ratio > 0.3 {
            actual_por = true;
            if !quiet {
                let pct = (spec_profile.independence_ratio * 100.0) as u32;
                println!("Auto-enabled: --por ({}% independent actions)", pct);
            }
        }
        if !use_symmetry && spec_profile.has_symmetry {
            let sym_warnings = specl_mc::Explorer::find_symmetry_warnings(&spec);
            if sym_warnings.is_empty() {
                actual_symmetry = true;
                if !quiet {
                    let sizes: Vec<String> = spec_profile
                        .symmetry_domain_sizes
                        .iter()
                        .map(|s| s.to_string())
                        .collect();
                    println!(
                        "Auto-enabled: --symmetry (symmetric domains: {})",
                        sizes.join(", ")
                    );
                }
            } else if !quiet {
                let sizes: Vec<String> = spec_profile
                    .symmetry_domain_sizes
                    .iter()
                    .map(|s| s.to_string())
                    .collect();
                println!(
                    "Skipped auto --symmetry (domains: {}): spec has asymmetric patterns",
                    sizes.join(", ")
                );
            }
        }

        // Auto-select storage mode based on estimated state space
        if !user_has_explicit_storage {
            if let Some(estimated) = spec_profile.state_space_bound {
                if estimated > 50_000_000 {
                    actual_fast = true;
                    if !quiet {
                        println!(
                            "Auto-enabled: --fast (estimated {} states, fingerprint-only saves memory). Traces unavailable in this mode.",
                            format_large_number(estimated)
                        );
                    }
                } else if estimated > 5_000_000 {
                    actual_collapse = true;
                    if !quiet {
                        println!(
                            "Auto-enabled: --collapse (estimated {} states, compressed storage)",
                            format_large_number(estimated)
                        );
                    }
                }
            }
        }

        if !quiet
            && (actual_por != use_por
                || actual_symmetry != use_symmetry
                || actual_fast != fast_check
                || actual_collapse != collapse)
        {
            println!();
        }
    }

    // --- Validate incompatible explicit-state flag combinations (#25) ---
    let storage_modes: Vec<&str> = [
        (actual_fast, "--fast"),
        (bloom, "--bloom"),
        (actual_collapse, "--collapse"),
        (tree, "--tree"),
    ]
    .iter()
    .filter(|(flag, _)| *flag)
    .map(|(_, name)| *name)
    .collect();
    if storage_modes.len() > 1 {
        let msg = format!(
            "Error: incompatible storage modes: {}. Pick one.",
            storage_modes.join(", ")
        );
        if output_format != OutputFormat::Text {
            let out = JsonOutput::new("error", 0.0).with_error(msg);
            println!("{}", serde_json::to_string(&out).unwrap());
        } else {
            eprintln!("{msg}");
        }
        std::process::exit(1);
    }

    if directed && (actual_fast || bloom || actual_collapse || tree) {
        let other = if actual_fast {
            "--fast"
        } else if bloom {
            "--bloom"
        } else if actual_collapse {
            "--collapse"
        } else {
            "--tree"
        };
        let msg = format!(
            "Error: --directed is incompatible with {other} (directed uses its own priority queue)"
        );
        if output_format != OutputFormat::Text {
            let out = JsonOutput::new("error", 0.0).with_error(msg);
            println!("{}", serde_json::to_string(&out).unwrap());
        } else {
            eprintln!("{msg}");
        }
        std::process::exit(1);
    }

    // --- Auto-correct flags that only work in sequential mode (#22, #23) ---
    let mut parallel = parallel;
    if profile && parallel {
        if !quiet {
            eprintln!("Note: --profile requires sequential mode, disabling parallel exploration");
        }
        parallel = false;
    }

    // --- Decouple --bloom from fast_check (#24) ---
    // bloom is a storage backend, not a checking strategy
    // do NOT silently force fast_check when bloom is set

    // --- Warn that --directed is always sequential (#21) ---
    if directed && parallel && !quiet {
        eprintln!("Note: --directed uses priority BFS which is sequential");
    }

    // --- Warn that --bloom is probabilistic/unsound ---
    if bloom && !quiet {
        eprintln!("Warning: --bloom is probabilistic and may miss bugs. For exhaustive verification use --fast or default mode.");
    }

    // Swarm verification: run N independent instances with shuffled action orders
    if let Some(n) = swarm {
        return cmd_check_swarm(
            spec,
            consts,
            &var_names,
            n,
            check_deadlock,
            max_states,
            max_depth,
            memory_limit_mb,
            actual_por,
            actual_symmetry,
            output_format,
            diff_traces,
        );
    }

    // Set up shared progress counters + spinner on its own timer thread
    let progress = Arc::new(ProgressCounters::new());
    let start = Instant::now();

    let spinner = if std::io::stderr().is_terminal() && !quiet {
        let pb = ProgressBar::new_spinner();
        pb.set_style(
            ProgressStyle::with_template("{spinner:.cyan} {msg}")
                .unwrap()
                .tick_chars("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"),
        );
        pb.enable_steady_tick(Duration::from_millis(100));
        pb.set_message("starting...");
        // Spinner reads from shared atomics on its own 100ms tick — never blocks
        let p = progress.clone();
        let pb2 = pb.clone();
        let start2 = start;
        std::thread::spawn(move || loop {
            std::thread::sleep(Duration::from_millis(100));
            let checked = p.checked.load(std::sync::atomic::Ordering::Relaxed);
            if checked == 0 {
                continue;
            }
            let states = p.states.load(std::sync::atomic::Ordering::Relaxed);
            let depth = p.depth.load(std::sync::atomic::Ordering::Relaxed);
            let elapsed = start2.elapsed().as_secs_f64();
            let rate = if elapsed > 0.0 {
                checked as f64 / elapsed
            } else {
                0.0
            };
            pb2.set_message(format!(
                "{} found | {} checked | depth {} | {} states/s",
                format_large_number(states as u128),
                format_large_number(checked as u128),
                depth,
                format_large_number(rate as u128),
            ));
            if pb2.is_finished() {
                break;
            }
        });
        Some(pb)
    } else {
        None
    };

    let config = CheckConfig {
        check_deadlock,
        max_states,
        max_depth,
        memory_limit_mb,
        parallel,
        num_threads,
        use_por: actual_por,
        use_symmetry: actual_symmetry,
        fast_check: actual_fast,
        progress: Some(progress),
        action_shuffle_seed: None,
        profile,
        bloom,
        bloom_bits,
        directed,
        max_time_secs,
        check_only_invariants,
        collapse: actual_collapse,
        tree,
    };

    // Incremental cache: compute spec hash and load cached fingerprints
    let (cache_hash, cached_fps) = if incremental {
        let const_pairs = parse_constants_as_pairs(constants);
        let hash = specl_mc::cache::spec_hash(&source, &const_pairs);
        let fps = specl_mc::cache::load_fingerprints(file.as_path(), hash);
        if let Some(ref fps) = fps {
            if !quiet {
                println!(
                    "Incremental: loaded {} cached states",
                    format_large_number(fps.len() as u128)
                );
            }
        }
        (Some(hash), fps)
    } else {
        (None, None)
    };

    let mut explorer = Explorer::new(spec, consts, config);

    if let Some(ref fps) = cached_fps {
        explorer.pre_seed_fingerprints(fps);
    }

    let result = explorer.check().map_err(|e| CliError::CheckError {
        message: e.to_string(),
    })?;

    // Save fingerprints for incremental re-use
    if let Some(hash) = cache_hash {
        let fps = explorer.store().seen_fingerprints();
        if let Err(e) = specl_mc::cache::save_fingerprints(file.as_path(), hash, &fps) {
            if !quiet {
                eprintln!("Warning: failed to save incremental cache: {e}");
            }
        }
        specl_mc::cache::cleanup_old_caches(file.as_path(), hash);
    }

    let elapsed = start.elapsed();

    if let Some(ref pb) = spinner {
        pb.finish_and_clear();
    }

    let secs = elapsed.as_secs_f64();

    if output_format == OutputFormat::Dot {
        // DOT state graph output (BFS exploration tree)
        let store = explorer.store();
        if !store.has_full_tracking() {
            eprintln!(
                "Error: --output dot requires full tracking (incompatible with --fast and --bloom)"
            );
            std::process::exit(1);
        }
        let max_dot_states = 10_000;
        let n_states = store.len();
        if n_states > max_dot_states {
            eprintln!(
                "Error: state graph has {} states (max {} for DOT output). Use smaller constants.",
                n_states, max_dot_states
            );
            std::process::exit(1);
        }

        // Determine violation fingerprint (if any) for highlighting
        let violation_fp = match &result {
            CheckOutcome::InvariantViolation { trace, .. } | CheckOutcome::Deadlock { trace } => {
                trace.last().map(|(s, _)| s.fingerprint())
            }
            _ => None,
        };

        println!(
            "{}",
            store_to_dot(store, &var_names, &action_names, violation_fp.as_ref())
        );

        match result {
            CheckOutcome::InvariantViolation { .. } | CheckOutcome::Deadlock { .. } => {
                std::process::exit(1);
            }
            CheckOutcome::StateLimitReached { .. }
            | CheckOutcome::MemoryLimitReached { .. }
            | CheckOutcome::TimeLimitReached { .. } => {
                std::process::exit(2);
            }
            _ => {}
        }
    } else if output_format == OutputFormat::Itf || output_format == OutputFormat::Mermaid {
        // Structured trace output (ITF or Mermaid)
        match result {
            CheckOutcome::InvariantViolation { invariant, trace } => {
                if output_format == OutputFormat::Mermaid {
                    println!(
                        "{}",
                        trace_to_mermaid(
                            &trace,
                            &var_names,
                            "invariant_violation",
                            Some(&invariant)
                        )
                    );
                } else {
                    let itf =
                        trace_to_itf(&trace, &var_names, "invariant_violation", Some(&invariant));
                    println!("{}", serde_json::to_string_pretty(&itf).unwrap());
                }
                std::process::exit(1);
            }
            CheckOutcome::Deadlock { trace } => {
                if output_format == OutputFormat::Mermaid {
                    println!("{}", trace_to_mermaid(&trace, &var_names, "deadlock", None));
                } else {
                    let itf = trace_to_itf(&trace, &var_names, "deadlock", None);
                    println!("{}", serde_json::to_string_pretty(&itf).unwrap());
                }
                std::process::exit(1);
            }
            CheckOutcome::Ok {
                states_explored, ..
            } => {
                eprintln!(
                    "Result: OK ({} states, no trace to export)",
                    states_explored
                );
            }
            CheckOutcome::StateLimitReached {
                states_explored, ..
            } => {
                eprintln!(
                    "Result: STATE LIMIT REACHED ({} states, no trace)",
                    states_explored
                );
                std::process::exit(2);
            }
            CheckOutcome::MemoryLimitReached {
                states_explored, ..
            } => {
                eprintln!(
                    "Result: MEMORY LIMIT REACHED ({} states, no trace)",
                    states_explored
                );
                std::process::exit(2);
            }
            CheckOutcome::TimeLimitReached {
                states_explored, ..
            } => {
                eprintln!(
                    "Result: TIME LIMIT REACHED ({} states, no trace)",
                    states_explored
                );
                std::process::exit(2);
            }
        }
    } else if json {
        let out =
            match result {
                CheckOutcome::Ok {
                    states_explored,
                    max_depth,
                } => JsonOutput::new("ok", secs).with_states(states_explored, max_depth),
                CheckOutcome::InvariantViolation { invariant, trace } => {
                    JsonOutput::new("invariant_violation", secs)
                        .with_invariant(invariant)
                        .with_trace(trace_to_json(&trace, &var_names))
                }
                CheckOutcome::Deadlock { trace } => {
                    JsonOutput::new("deadlock", secs).with_trace(trace_to_json(&trace, &var_names))
                }
                CheckOutcome::StateLimitReached {
                    states_explored,
                    max_depth,
                } => JsonOutput::new("state_limit_reached", secs)
                    .with_states(states_explored, max_depth),
                CheckOutcome::MemoryLimitReached {
                    states_explored,
                    max_depth,
                    memory_mb,
                } => JsonOutput::new("memory_limit_reached", secs)
                    .with_states(states_explored, max_depth)
                    .with_memory(memory_mb),
                CheckOutcome::TimeLimitReached {
                    states_explored,
                    max_depth,
                } => JsonOutput::new("time_limit_reached", secs)
                    .with_states(states_explored, max_depth),
            };
        println!("{}", serde_json::to_string(&out).unwrap());
        let exit_code = match out.result {
            "ok" => 0,
            "invariant_violation" | "deadlock" => 1,
            _ => 2,
        };
        if exit_code != 0 {
            std::process::exit(exit_code);
        }
    } else {
        let exit_code = match result {
            CheckOutcome::Ok {
                states_explored,
                max_depth,
            } => {
                println!();
                println!("Result: OK");
                println!(
                    "  States explored: {}",
                    format_large_number(states_explored as u128)
                );
                println!("  Max depth: {}", max_depth);
                println!("  Time: {:.1}s", secs);
                if secs > 0.001 {
                    println!(
                        "  Throughput: {} states/s",
                        format_large_number((states_explored as f64 / secs) as u128)
                    );
                }
                let mut opts = Vec::new();
                if actual_por {
                    opts.push("POR");
                }
                if actual_symmetry {
                    opts.push("symmetry");
                }
                if bloom {
                    opts.push("bloom");
                } else if actual_fast {
                    opts.push("fast");
                }
                if actual_collapse {
                    opts.push("collapse");
                }
                if directed {
                    opts.push("directed");
                }
                if !opts.is_empty() {
                    println!("  Optimizations: {}", opts.join(", "));
                }
                0
            }
            CheckOutcome::InvariantViolation { invariant, trace } => {
                println!();
                println!("Result: INVARIANT VIOLATION");
                println!("  Invariant: {}", invariant);
                print_text_trace(&trace, &var_names, diff_traces);
                1
            }
            CheckOutcome::Deadlock { trace } => {
                println!();
                println!("Result: DEADLOCK");
                print_text_trace(&trace, &var_names, diff_traces);
                1
            }
            CheckOutcome::StateLimitReached {
                states_explored,
                max_depth,
            } => {
                println!();
                println!("Result: STATE LIMIT REACHED");
                println!("  States explored: {}", states_explored);
                println!("  Max depth: {}", max_depth);
                println!("  Time: {:.2}s", secs);
                println!("  No violations found within this limit. Increase with --max-states <N> or use 0 for unlimited.");
                2
            }
            CheckOutcome::MemoryLimitReached {
                states_explored,
                max_depth,
                memory_mb,
            } => {
                println!();
                println!("Result: MEMORY LIMIT REACHED");
                println!("  Memory usage: {} MB", memory_mb);
                println!("  States explored: {}", states_explored);
                println!("  Max depth: {}", max_depth);
                println!("  Time: {:.2}s", secs);
                println!("  Try --fast (fingerprint-only, 10x less memory) or reduce constants.");
                2
            }
            CheckOutcome::TimeLimitReached {
                states_explored,
                max_depth,
            } => {
                println!();
                println!("Result: TIME LIMIT REACHED");
                println!("  States explored: {}", states_explored);
                println!("  Max depth: {}", max_depth);
                println!("  Time: {:.2}s", secs);
                println!("  Increase with --max-time <N> (seconds) or use 0 for unlimited.");
                2
            }
        };
        if exit_code != 0 {
            print_check_profile(&explorer);
            std::process::exit(exit_code);
        }
    }

    print_check_profile(&explorer);

    Ok(())
}

fn cmd_check_swarm(
    spec: specl_ir::CompiledSpec,
    consts: Vec<Value>,
    var_names: &[String],
    num_workers: usize,
    check_deadlock: bool,
    max_states: usize,
    max_depth: usize,
    memory_limit_mb: usize,
    use_por: bool,
    use_symmetry: bool,
    output_format: OutputFormat,
    diff_traces: bool,
) -> CliResult<()> {
    let json = output_format != OutputFormat::Text;
    use std::sync::atomic::AtomicBool;

    let n = num_workers.max(2);
    if !json {
        println!("Swarm verification: {} workers", n);
    }

    let stop = Arc::new(AtomicBool::new(false));
    let start = Instant::now();
    let spec = Arc::new(spec);
    let consts = Arc::new(consts);

    let handles: Vec<_> = (0..n)
        .map(|i| {
            let spec = Arc::clone(&spec);
            let consts = Arc::clone(&consts);
            let stop = Arc::clone(&stop);
            std::thread::spawn(move || {
                let config = CheckConfig {
                    check_deadlock,
                    max_states,
                    max_depth,
                    memory_limit_mb,
                    parallel: false, // each worker is single-threaded
                    num_threads: 1,
                    use_por,
                    use_symmetry,
                    fast_check: true, // fingerprint-only for speed
                    progress: None,
                    action_shuffle_seed: Some(i as u64),
                    profile: false,
                    bloom: false,
                    bloom_bits: 30,
                    directed: false,
                    max_time_secs: 0,
                    check_only_invariants: Vec::new(),
                    collapse: false,
                    tree: false,
                };
                let mut explorer = Explorer::new((*spec).clone(), (*consts).clone(), config);
                explorer.set_stop_flag(Arc::clone(&stop));
                let result = explorer.check();
                // Signal other workers to stop on violation
                if let Ok(CheckOutcome::InvariantViolation { .. } | CheckOutcome::Deadlock { .. }) =
                    &result
                {
                    stop.store(true, std::sync::atomic::Ordering::Relaxed);
                }
                result
            })
        })
        .collect();

    // Collect results
    let mut first_violation: Option<CheckOutcome> = None;
    let mut all_ok = true;
    for handle in handles {
        match handle.join() {
            Ok(Ok(outcome)) => match &outcome {
                CheckOutcome::InvariantViolation { .. } | CheckOutcome::Deadlock { .. } => {
                    if first_violation.is_none() {
                        first_violation = Some(outcome);
                    }
                    all_ok = false;
                }
                CheckOutcome::Ok { .. } => {}
                _ => {
                    all_ok = false;
                }
            },
            Ok(Err(_)) | Err(_) => {
                all_ok = false;
            }
        }
    }

    let secs = start.elapsed().as_secs_f64();

    // If a violation was found (fast mode), re-run with trace reconstruction
    if let Some(violation) = first_violation {
        match &violation {
            CheckOutcome::InvariantViolation { invariant, .. } => {
                if !json {
                    println!(
                        "Swarm: found invariant violation '{}', reconstructing trace...",
                        invariant
                    );
                }
                // Re-run with the same shuffled order but full tracking
                let config = CheckConfig {
                    check_deadlock,
                    max_states,
                    max_depth,
                    memory_limit_mb,
                    parallel: true,
                    num_threads: 0,
                    use_por,
                    use_symmetry,
                    fast_check: false,
                    progress: None,
                    action_shuffle_seed: None,
                    profile: false,
                    bloom: false,
                    bloom_bits: 30,
                    directed: false,
                    max_time_secs: 0,
                    check_only_invariants: Vec::new(),
                    collapse: false,
                    tree: false,
                };
                let mut explorer = Explorer::new((*spec).clone(), (*consts).clone(), config);
                let result = explorer.check().map_err(|e| CliError::CheckError {
                    message: e.to_string(),
                })?;
                let total_secs = start.elapsed().as_secs_f64();
                if let CheckOutcome::InvariantViolation { invariant, trace } = result {
                    match output_format {
                        OutputFormat::Mermaid => {
                            println!(
                                "{}",
                                trace_to_mermaid(
                                    &trace,
                                    var_names,
                                    "invariant_violation",
                                    Some(&invariant)
                                )
                            );
                        }
                        OutputFormat::Itf => {
                            let itf = trace_to_itf(
                                &trace,
                                var_names,
                                "invariant_violation",
                                Some(&invariant),
                            );
                            println!("{}", serde_json::to_string_pretty(&itf).unwrap());
                        }
                        OutputFormat::Json => {
                            let out = JsonOutput::new("invariant_violation", total_secs)
                                .with_invariant(invariant)
                                .with_trace(trace_to_json(&trace, var_names));
                            println!("{}", serde_json::to_string(&out).unwrap());
                        }
                        OutputFormat::Dot => {
                            // DOT output not meaningful for swarm (no full store)
                            eprintln!("Error: --output dot is not supported with --swarm");
                            std::process::exit(1);
                        }
                        OutputFormat::Text => {
                            println!();
                            println!(
                                "Result: INVARIANT VIOLATION (swarm found in {:.1}s, trace reconstructed)",
                                secs
                            );
                            println!("  Invariant: {}", invariant);
                            print_text_trace(&trace, var_names, diff_traces);
                            println!("  Total time: {:.1}s", total_secs);
                        }
                    }
                }
                std::process::exit(1);
            }
            CheckOutcome::Deadlock { .. } => {
                // Similar for deadlock — simplified: just report
                if json {
                    let out = JsonOutput::new("deadlock", secs);
                    println!("{}", serde_json::to_string(&out).unwrap());
                } else {
                    println!("Result: DEADLOCK (found by swarm in {:.1}s)", secs);
                }
                std::process::exit(1);
            }
            _ => {}
        }
    }

    if all_ok {
        if json {
            let out = JsonOutput::new("ok", secs);
            println!("{}", serde_json::to_string(&out).unwrap());
        } else {
            println!();
            println!("Result: OK (swarm, {} workers)", n);
            println!("  Time: {:.1}s", secs);
        }
    }

    Ok(())
}

fn cmd_check_symbolic(
    file: &PathBuf,
    constants: &[String],
    bmc_depth: usize,
    bmc: bool,
    inductive: bool,
    k_induction: Option<usize>,
    ic3: bool,
    portfolio: bool,
    golem: bool,
    seq_bound: usize,
    spacer_profile: SpacerProfile,
    timeout: u64,
    json: bool,
) -> CliResult<()> {
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    info!("parsing...");
    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;

    info!("type checking...");
    specl_types::check_module(&module)
        .map_err(|e| CliError::from_type_error(e, source.clone(), &filename))?;

    info!("compiling...");
    let spec = compile(&module).map_err(|e| CliError::CompileError {
        message: e.to_string(),
    })?;

    let consts = parse_constants(constants, &spec)?;

    let config = SymbolicConfig {
        mode: if portfolio {
            SymbolicMode::Portfolio
        } else if golem {
            SymbolicMode::Golem
        } else if ic3 {
            SymbolicMode::Ic3
        } else if let Some(k) = k_induction {
            SymbolicMode::KInduction(k)
        } else if inductive {
            SymbolicMode::Inductive
        } else if bmc {
            SymbolicMode::Bmc
        } else {
            SymbolicMode::Smart
        },
        depth: bmc_depth,
        seq_bound,
        spacer_profile,
        timeout_ms: if timeout == 0 {
            None
        } else {
            Some(timeout * 1000)
        },
    };

    let mode_str = if portfolio {
        "portfolio"
    } else if golem {
        "Golem"
    } else if ic3 {
        "IC3"
    } else if k_induction.is_some() {
        "k-induction"
    } else if inductive {
        "inductive"
    } else if bmc {
        "symbolic BMC"
    } else {
        "smart"
    };
    // Check for Seq variables and warn about seq-bound (#28)
    let has_seq_vars = spec
        .vars
        .iter()
        .any(|v| matches!(&v.ty, specl_types::Type::Seq(..)));
    if has_seq_vars && !json {
        eprintln!(
            "Note: Seq[T] variables bounded to length {}. Increase --seq-bound if sequences may be longer.",
            seq_bound
        );
    }

    info!(mode = mode_str, "checking...");
    let start = Instant::now();

    let result = specl_symbolic::check(&spec, &consts, &config).map_err(|e| {
        let hint = if matches!(
            e,
            SymbolicError::Unsupported(_) | SymbolicError::Encoding(_)
        ) {
            "\n  hint: use `--bfs` to check with explicit-state BFS instead"
        } else {
            ""
        };
        CliError::CheckError {
            message: format!("{e}{hint}"),
        }
    })?;

    let elapsed = start.elapsed();

    let secs = elapsed.as_secs_f64();

    if json {
        let out = match result {
            SymbolicOutcome::Ok { method } => {
                JsonOutput::new("ok", secs).with_method(method.to_string())
            }
            SymbolicOutcome::InvariantViolation { invariant, trace } => {
                let json_trace: Vec<JsonTraceStep> = trace
                    .iter()
                    .enumerate()
                    .map(|(i, step)| {
                        let mut state = BTreeMap::new();
                        for (name, val) in &step.state {
                            state.insert(name.clone(), serde_json::Value::String(val.clone()));
                        }
                        JsonTraceStep {
                            step: i,
                            action: step.action.clone().unwrap_or_else(|| "init".into()),
                            state,
                        }
                    })
                    .collect();
                let result = if inductive {
                    "not_inductive"
                } else {
                    "invariant_violation"
                };
                JsonOutput::new(result, secs)
                    .with_invariant(invariant)
                    .with_trace(json_trace)
            }
            SymbolicOutcome::Unknown { reason } => {
                JsonOutput::new("unknown", secs).with_reason(reason)
            }
        };
        println!("{}", serde_json::to_string(&out).unwrap());
        let exit_code = match out.result {
            "ok" => 0,
            "invariant_violation" | "not_inductive" => 1,
            _ => 2,
        };
        if exit_code != 0 {
            std::process::exit(exit_code);
        }
    } else {
        match result {
            SymbolicOutcome::Ok { method } => {
                println!();
                println!("Result: OK");
                println!("  Method: {}", method);
                if let Some(k) = k_induction {
                    println!("  K: {}", k);
                } else if !inductive && !ic3 && bmc_depth > 0 {
                    println!("  Depth: {}", bmc_depth);
                }
                println!("  Time: {:.2}s", secs);
            }
            SymbolicOutcome::InvariantViolation { invariant, trace } => {
                println!();
                if inductive {
                    println!("Result: NOT INDUCTIVE (counterexample to induction)");
                    println!("  Invariant: {}", invariant);
                    println!("  CTI trace: {} steps", trace.len());
                    println!("  Note: this is NOT a reachable violation. The invariant is not inductive,");
                    println!("  meaning it cannot be proved by single-step induction alone.");
                    println!("  Try --k-induction 3 or --ic3 for a stronger proof, or --bfs for exhaustive checking.");
                    std::process::exit(2);
                } else {
                    println!("Result: INVARIANT VIOLATION");
                    println!("  Invariant: {}", invariant);
                    println!("  Trace ({} steps):", trace.len());
                    for (i, step) in trace.iter().enumerate() {
                        let action_str = step.action.as_deref().unwrap_or("?");
                        let state_str = step
                            .state
                            .iter()
                            .map(|(name, val)| format!("{}={}", name, val))
                            .collect::<Vec<_>>()
                            .join(", ");
                        println!("    {}: {} -> {}", i, action_str, state_str);
                    }
                    std::process::exit(1);
                }
            }
            SymbolicOutcome::Unknown { reason } => {
                println!();
                println!("Result: UNKNOWN");
                println!("  Reason: {}", reason);
                println!("  hint: try --bfs for explicit-state checking, or increase --timeout");
                std::process::exit(2);
            }
        }
    }

    Ok(())
}

fn cmd_lint(file: &PathBuf, constants: &[String], output: OutputFormat) -> CliResult<()> {
    let json = output == OutputFormat::Json;
    let filename = file.display().to_string();
    let start = Instant::now();

    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    // Parse
    let module = match parse(&source) {
        Ok(m) => m,
        Err(e) => {
            let secs = start.elapsed().as_secs_f64();
            if json {
                let out = JsonOutput::new("error", secs).with_error(format!("parse error: {}", e));
                println!("{}", serde_json::to_string(&out).unwrap());
                std::process::exit(1);
            }
            return Err(CliError::from_parse_error(e, source.clone(), &filename));
        }
    };

    // Type check
    if let Err(e) = specl_types::check_module(&module) {
        let secs = start.elapsed().as_secs_f64();
        if json {
            let out = JsonOutput::new("error", secs).with_error(format!("type error: {}", e));
            println!("{}", serde_json::to_string(&out).unwrap());
            std::process::exit(1);
        }
        return Err(CliError::from_type_error(e, source.clone(), &filename));
    }

    // Compile
    let spec = match compile(&module) {
        Ok(s) => s,
        Err(e) => {
            let secs = start.elapsed().as_secs_f64();
            if json {
                let out =
                    JsonOutput::new("error", secs).with_error(format!("compile error: {}", e));
                println!("{}", serde_json::to_string(&out).unwrap());
                std::process::exit(1);
            }
            return Err(CliError::CompileError {
                message: e.to_string(),
            });
        }
    };

    // Validate constants if provided
    if !constants.is_empty() {
        if let Err(e) = parse_constants(constants, &spec) {
            let secs = start.elapsed().as_secs_f64();
            if json {
                let out = JsonOutput::new("error", secs).with_error(e.to_string());
                println!("{}", serde_json::to_string(&out).unwrap());
                std::process::exit(1);
            }
            return Err(e);
        }
    }

    let secs = start.elapsed().as_secs_f64();
    if json {
        let out = JsonOutput::new("ok", secs);
        println!("{}", serde_json::to_string(&out).unwrap());
    } else {
        let num_vars = spec.vars.len();
        let num_actions = spec.actions.len();
        let num_invariants = spec.invariants.len();
        println!(
            "lint: ok ({} vars, {} actions, {} invariants) {:.3}s",
            num_vars, num_actions, num_invariants, secs
        );
    }

    Ok(())
}

fn cmd_simulate(
    file: &PathBuf,
    constants: &[String],
    max_steps: usize,
    seed: u64,
    output: OutputFormat,
) -> CliResult<()> {
    let json = output == OutputFormat::Json;
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;
    specl_types::check_module(&module)
        .map_err(|e| CliError::from_type_error(e, source.clone(), &filename))?;
    let spec = compile(&module).map_err(|e| CliError::CompileError {
        message: e.to_string(),
    })?;
    let consts = parse_constants(constants, &spec)?;

    let config = CheckConfig {
        check_deadlock: false,
        ..Default::default()
    };

    let mut explorer = Explorer::new(spec, consts, config);
    let start = Instant::now();
    let result = explorer
        .simulate(max_steps, seed)
        .map_err(|e| CliError::CheckError {
            message: e.to_string(),
        })?;
    let secs = start.elapsed().as_secs_f64();

    if output == OutputFormat::Itf || output == OutputFormat::Mermaid {
        // Structured trace output (ITF or Mermaid)
        let (trace, var_names, result_kind, invariant) = match &result {
            SimulateOutcome::Ok {
                trace, var_names, ..
            } => (trace, var_names, "ok", None),
            SimulateOutcome::InvariantViolation {
                invariant,
                trace,
                var_names,
            } => (
                trace,
                var_names,
                "invariant_violation",
                Some(invariant.as_str()),
            ),
            SimulateOutcome::Deadlock { trace, var_names } => (trace, var_names, "deadlock", None),
        };
        if output == OutputFormat::Mermaid {
            println!(
                "{}",
                trace_to_mermaid(trace, var_names, result_kind, invariant)
            );
        } else {
            let itf = trace_to_itf(trace, var_names, result_kind, invariant);
            println!("{}", serde_json::to_string_pretty(&itf).unwrap());
        }
        match &result {
            SimulateOutcome::InvariantViolation { .. } | SimulateOutcome::Deadlock { .. } => {
                std::process::exit(1);
            }
            _ => {}
        }
        return Ok(());
    } else if json {
        let out = match &result {
            SimulateOutcome::Ok {
                steps,
                trace,
                var_names,
            } => JsonOutput::new("ok", secs)
                .with_states(*steps, 0)
                .with_trace(trace_to_json(trace, var_names)),
            SimulateOutcome::InvariantViolation {
                invariant,
                trace,
                var_names,
            } => JsonOutput::new("invariant_violation", secs)
                .with_invariant(invariant.clone())
                .with_trace(trace_to_json(trace, var_names)),
            SimulateOutcome::Deadlock { trace, var_names } => {
                JsonOutput::new("deadlock", secs).with_trace(trace_to_json(trace, var_names))
            }
        };
        println!("{}", serde_json::to_string(&out).unwrap());
    } else {
        match &result {
            SimulateOutcome::Ok {
                steps,
                trace,
                var_names,
            } => {
                println!("Simulation: {} steps, no violation (seed={})", steps, seed);
                println!();
                for (i, (state, action)) in trace.iter().enumerate() {
                    let action_str = action.as_deref().unwrap_or("init");
                    let state_str = format_state_with_names(state, var_names);
                    println!("  {}: {} -> {}", i, action_str, state_str);
                }
            }
            SimulateOutcome::InvariantViolation {
                invariant,
                trace,
                var_names,
            } => {
                println!("Simulation: INVARIANT VIOLATION");
                println!("  Invariant: {}", invariant);
                println!("  Trace ({} steps):", trace.len());
                for (i, (state, action)) in trace.iter().enumerate() {
                    let action_str = action.as_deref().unwrap_or("init");
                    let state_str = format_state_with_names(state, var_names);
                    println!("    {}: {} -> {}", i, action_str, state_str);
                }
                std::process::exit(1);
            }
            SimulateOutcome::Deadlock { trace, var_names } => {
                println!("Simulation: DEADLOCK after {} steps", trace.len() - 1);
                println!("  Trace ({} steps):", trace.len());
                for (i, (state, action)) in trace.iter().enumerate() {
                    let action_str = action.as_deref().unwrap_or("init");
                    let state_str = format_state_with_names(state, var_names);
                    println!("    {}: {} -> {}", i, action_str, state_str);
                }
                std::process::exit(1);
            }
        }
    }
    if !json {
        println!("  Time: {:.3}s", secs);
    }

    Ok(())
}

fn parse_constants(constants: &[String], spec: &specl_ir::CompiledSpec) -> CliResult<Vec<Value>> {
    let mut values = vec![Value::none(); spec.consts.len()];

    for constant in constants {
        let parts: Vec<&str> = constant.splitn(2, '=').collect();
        if parts.len() != 2 {
            return Err(CliError::Other {
                message: format!(
                    "invalid constant format '{}', expected NAME=VALUE",
                    constant
                ),
            });
        }

        let name = parts[0].trim();
        let value_str = parts[1].trim();

        // Find the constant
        let const_decl =
            spec.consts
                .iter()
                .find(|c| c.name == name)
                .ok_or_else(|| CliError::Other {
                    message: format!("unknown constant '{}'", name),
                })?;

        // Parse the value
        let value = parse_value(value_str)?;
        values[const_decl.index] = value;
    }

    // Check all constants are set - use default values for scalar constants
    let mut missing = Vec::new();
    for const_decl in &spec.consts {
        if values[const_decl.index].is_none() {
            if let Some(default_value) = const_decl.default_value {
                values[const_decl.index] = Value::int(default_value);
            } else {
                missing.push(const_decl.name.clone());
            }
        }
    }
    if !missing.is_empty() {
        let flags: Vec<String> = missing
            .iter()
            .map(|n| format!("  -c {}=VALUE", n))
            .collect();
        return Err(CliError::Other {
            message: format!(
                "missing constants (provide with -c NAME=VALUE):\n{}",
                flags.join("\n")
            ),
        });
    }

    Ok(values)
}

/// Parse constant strings into (name, value) pairs for cache hashing.
fn parse_constants_as_pairs(constants: &[String]) -> Vec<(String, i64)> {
    constants
        .iter()
        .filter_map(|c| {
            let parts: Vec<&str> = c.splitn(2, '=').collect();
            if parts.len() == 2 {
                parts[1]
                    .trim()
                    .parse::<i64>()
                    .ok()
                    .map(|v| (parts[0].trim().to_string(), v))
            } else {
                None
            }
        })
        .collect()
}

fn parse_value(s: &str) -> CliResult<Value> {
    // Try to parse as integer
    if let Ok(n) = s.parse::<i64>() {
        return Ok(Value::int(n));
    }

    // Try to parse as boolean
    if s == "true" {
        return Ok(Value::bool(true));
    }
    if s == "false" {
        return Ok(Value::bool(false));
    }

    // Try to parse as string (quoted)
    if s.starts_with('"') && s.ends_with('"') {
        return Ok(Value::string(s[1..s.len() - 1].to_string()));
    }

    Err(CliError::Other {
        message: format!("cannot parse value '{}'", s),
    })
}

/// Convert a BFS trace to JSON trace steps.
fn trace_to_json(trace: &[(State, Option<String>)], var_names: &[String]) -> Vec<JsonTraceStep> {
    trace
        .iter()
        .enumerate()
        .map(|(i, (state, action))| {
            let mut state_map = BTreeMap::new();
            for (j, v) in state.vars.iter().enumerate() {
                let name = var_names
                    .get(j)
                    .cloned()
                    .unwrap_or_else(|| format!("v{}", j));
                state_map.insert(name, value_to_json(v));
            }
            JsonTraceStep {
                step: i,
                action: action.clone().unwrap_or_else(|| "init".into()),
                state: state_map,
            }
        })
        .collect()
}

/// Convert a specl Value to a serde_json::Value.
fn value_to_json(v: &Value) -> serde_json::Value {
    match v.kind() {
        VK::Bool(b) => serde_json::Value::Bool(b),
        VK::Int(n) => serde_json::json!(n),
        VK::String(s) => serde_json::Value::String(s.to_string()),
        VK::Set(elems) => serde_json::Value::Array(elems.iter().map(value_to_json).collect()),
        VK::Seq(elems) => serde_json::Value::Array(elems.iter().map(value_to_json).collect()),
        VK::Fn(pairs) => {
            let obj: serde_json::Map<String, serde_json::Value> = pairs
                .iter()
                .map(|(k, v)| (format!("{}", k), value_to_json(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        VK::IntMap(vals) => {
            let obj: serde_json::Map<String, serde_json::Value> = vals
                .iter()
                .enumerate()
                .map(|(i, v)| (i.to_string(), value_to_json(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        VK::Record(fields) => {
            let obj: serde_json::Map<String, serde_json::Value> = fields
                .iter()
                .map(|(k, v)| (k.clone(), value_to_json(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        VK::Tuple(elems) => serde_json::Value::Array(elems.iter().map(value_to_json).collect()),
        VK::None => serde_json::Value::Null,
        VK::IntMap2(inner_size, data) => {
            let outer_size = if inner_size > 0 {
                data.len() / inner_size as usize
            } else {
                0
            };
            let obj: serde_json::Map<String, serde_json::Value> = (0..outer_size)
                .map(|i| {
                    let inner_obj: serde_json::Map<String, serde_json::Value> = (0..inner_size
                        as usize)
                        .map(|j| {
                            (
                                j.to_string(),
                                value_to_json(&data[i * inner_size as usize + j]),
                            )
                        })
                        .collect();
                    (i.to_string(), serde_json::Value::Object(inner_obj))
                })
                .collect();
            serde_json::Value::Object(obj)
        }
        VK::Some(inner) => value_to_json(inner),
    }
}

/// Convert a specl Value to ITF-encoded serde_json::Value.
/// ITF uses tagged objects for non-primitive types:
///   Int → {"#bigint": "42"}, Set → {"#set": [...]}, Map → {"#map": [[k,v],...]},
///   Tuple → {"#tup": [...]}, Seq → plain array, Record → plain object.
fn value_to_itf(v: &Value) -> serde_json::Value {
    match v.kind() {
        VK::Bool(b) => serde_json::Value::Bool(b),
        VK::Int(n) => serde_json::json!({"#bigint": n.to_string()}),
        VK::String(s) => serde_json::Value::String(s.to_string()),
        VK::Set(elems) => {
            serde_json::json!({"#set": elems.iter().map(value_to_itf).collect::<Vec<_>>()})
        }
        VK::Seq(elems) => serde_json::Value::Array(elems.iter().map(value_to_itf).collect()),
        VK::Fn(pairs) => {
            let entries: Vec<serde_json::Value> = pairs
                .iter()
                .map(|(k, v)| serde_json::json!([value_to_itf(k), value_to_itf(v)]))
                .collect();
            serde_json::json!({"#map": entries})
        }
        VK::IntMap(vals) => {
            let entries: Vec<serde_json::Value> = vals
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    serde_json::json!([
                        serde_json::json!({"#bigint": i.to_string()}),
                        serde_json::json!({"#bigint": v.to_string()})
                    ])
                })
                .collect();
            serde_json::json!({"#map": entries})
        }
        VK::Record(fields) => {
            let obj: serde_json::Map<String, serde_json::Value> = fields
                .iter()
                .map(|(k, v)| (k.clone(), value_to_itf(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        VK::Tuple(elems) => {
            serde_json::json!({"#tup": elems.iter().map(value_to_itf).collect::<Vec<_>>()})
        }
        VK::None => serde_json::json!({"tag": "None", "value": serde_json::json!({})}),
        VK::IntMap2(inner_size, data) => {
            let outer_size = if inner_size > 0 {
                data.len() / inner_size as usize
            } else {
                0
            };
            let entries: Vec<serde_json::Value> = (0..outer_size)
                .map(|i| {
                    let inner_entries: Vec<serde_json::Value> = (0..inner_size as usize)
                        .map(|j| {
                            serde_json::json!([
                                serde_json::json!({"#bigint": j.to_string()}),
                                value_to_itf(&data[i * inner_size as usize + j])
                            ])
                        })
                        .collect();
                    serde_json::json!([
                        serde_json::json!({"#bigint": i.to_string()}),
                        serde_json::json!({"#map": inner_entries})
                    ])
                })
                .collect();
            serde_json::json!({"#map": entries})
        }
        VK::Some(inner) => {
            serde_json::json!({"tag": "Some", "value": value_to_itf(inner)})
        }
    }
}

/// Build an ITF trace JSON object from a specl trace.
fn trace_to_itf(
    trace: &[(State, Option<String>)],
    var_names: &[String],
    result_kind: &str,
    invariant: Option<&str>,
) -> serde_json::Value {
    let states: Vec<serde_json::Value> = trace
        .iter()
        .enumerate()
        .map(|(i, (state, action))| {
            let mut obj = serde_json::Map::new();
            let mut meta = serde_json::Map::new();
            meta.insert(
                "index".into(),
                serde_json::Value::Number(serde_json::Number::from(i)),
            );
            if let Some(a) = action {
                meta.insert("action".into(), serde_json::Value::String(a.clone()));
            }
            obj.insert("#meta".into(), serde_json::Value::Object(meta));
            for (j, v) in state.vars.iter().enumerate() {
                let name = var_names
                    .get(j)
                    .cloned()
                    .unwrap_or_else(|| format!("v{}", j));
                obj.insert(name, value_to_itf(v));
            }
            serde_json::Value::Object(obj)
        })
        .collect();

    let mut meta = serde_json::Map::new();
    meta.insert("format".into(), "ITF".into());
    meta.insert(
        "format-description".into(),
        "https://apalache-mc.org/docs/adr/015adr-trace.html".into(),
    );
    meta.insert("source".into(), "specl".into());
    meta.insert("result".into(), result_kind.into());
    if let Some(inv) = invariant {
        meta.insert("invariant".into(), inv.into());
    }

    serde_json::json!({
        "#meta": meta,
        "vars": var_names,
        "states": states,
    })
}

/// Format a state with variable names for readable trace output.
fn format_state_with_names(state: &State, var_names: &[String]) -> String {
    state
        .vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let name = var_names.get(i).map(|s| s.as_str()).unwrap_or("?");
            format!("{}={}", name, v)
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Print a text trace to stdout.
/// In diff mode, only shows variables that changed from the previous step.
fn print_text_trace(trace: &[(State, Option<String>)], var_names: &[String], diff: bool) {
    println!("  Trace ({} steps):", trace.len());
    let mut prev_state: Option<&State> = None;
    for (i, (state, action)) in trace.iter().enumerate() {
        let action_str = action.as_deref().unwrap_or("init");
        if let Some(prev) = prev_state.filter(|_| diff) {
            let mut changes = Vec::new();
            for (idx, v) in state.vars.iter().enumerate() {
                if idx >= prev.vars.len() || *v != prev.vars[idx] {
                    let name = var_names.get(idx).map(|s| s.as_str()).unwrap_or("?");
                    changes.push(format!("{}={}", name, v));
                }
            }
            if changes.is_empty() {
                println!("    {}: {} -> (no change)", i, action_str);
            } else {
                println!("    {}: {} -> {}", i, action_str, changes.join(", "));
            }
        } else {
            let state_str = format_state_with_names(state, var_names);
            println!("    {}: {} -> {}", i, action_str, state_str);
        }
        prev_state = Some(state);
    }
}

/// Generate a Graphviz DOT graph from the BFS exploration tree.
///
/// Each state is a node, each transition (predecessor → state via action) is an edge.
/// Initial states have a double circle, violation states are colored red.
fn store_to_dot(
    store: &StateStore,
    var_names: &[String],
    action_names: &[String],
    violation_fp: Option<&Fingerprint>,
) -> String {
    let mut lines = vec![
        "digraph states {".to_string(),
        "    rankdir=TB;".to_string(),
        "    node [shape=box, fontname=\"monospace\", fontsize=10];".to_string(),
        "    edge [fontname=\"monospace\", fontsize=9];".to_string(),
    ];

    let raw_fps = store.seen_fingerprints();

    // Assign compact numeric IDs to fingerprints
    let mut fp_list: Vec<Fingerprint> = raw_fps.into_iter().map(Fingerprint::from_u64).collect();
    fp_list.sort_by_key(|fp| fp.as_u64());
    let fp_to_id: std::collections::HashMap<Fingerprint, usize> =
        fp_list.iter().enumerate().map(|(i, fp)| (*fp, i)).collect();

    // Emit nodes
    for &fp in &fp_list {
        let info = match store.get(&fp) {
            Some(i) => i,
            None => continue,
        };
        let id = fp_to_id[&fp];
        let is_initial = info.predecessor.is_none();
        let is_violation = violation_fp.is_some_and(|vfp| *vfp == fp);

        // Build compact label: "var1=val1\nvar2=val2"
        let label: String = info
            .state
            .vars
            .iter()
            .enumerate()
            .map(|(i, v)| {
                let name = var_names.get(i).map(|s| s.as_str()).unwrap_or("?");
                format!("{}={}", name, format_value_compact(v))
            })
            .collect::<Vec<_>>()
            .join("\\n");

        let mut attrs = vec![format!("label=\"S{}\\n{}\"", id, label)];
        if is_initial {
            attrs.push("shape=doubleoctagon".to_string());
            attrs.push("style=filled".to_string());
            attrs.push("fillcolor=\"#e8f5e9\"".to_string());
        }
        if is_violation {
            attrs.push("style=filled".to_string());
            attrs.push("fillcolor=\"#ffcdd2\"".to_string());
            attrs.push("penwidth=2".to_string());
        }

        lines.push(format!("    s{} [{}];", id, attrs.join(", ")));
    }

    // Emit edges (predecessor → state)
    for &fp in &fp_list {
        let info = match store.get(&fp) {
            Some(i) => i,
            None => continue,
        };
        let dst_id = fp_to_id[&fp];

        if let Some(pred_fp) = info.predecessor {
            if let Some(&src_id) = fp_to_id.get(&pred_fp) {
                let edge_label = info
                    .action_idx
                    .map(|idx| {
                        let base = action_names
                            .get(idx)
                            .cloned()
                            .unwrap_or_else(|| format!("action_{}", idx));
                        if let Some(ref params) = info.param_values {
                            if params.is_empty() {
                                base
                            } else {
                                let ps: Vec<String> =
                                    params.iter().map(|v| v.to_string()).collect();
                                format!("{}({})", base, ps.join(","))
                            }
                        } else {
                            base
                        }
                    })
                    .unwrap_or_default();
                lines.push(format!(
                    "    s{} -> s{} [label=\"{}\"];",
                    src_id, dst_id, edge_label
                ));
            }
        }
    }

    lines.push("}".to_string());
    lines.join("\n")
}

/// Format a Value compactly for DOT node labels.
fn format_value_compact(v: &Value) -> String {
    match v.kind() {
        VK::Int(n) => n.to_string(),
        VK::Bool(b) => if b { "T" } else { "F" }.to_string(),
        VK::String(s) => format!("\"{}\"", s),
        VK::Set(s) => {
            let inner: Vec<String> = s.iter().map(format_value_compact).collect();
            format!("{{{}}}", inner.join(","))
        }
        VK::Seq(s) => {
            let inner: Vec<String> = s.iter().map(format_value_compact).collect();
            format!("[{}]", inner.join(","))
        }
        VK::Fn(f) => {
            let inner: Vec<String> = f
                .iter()
                .map(|(k, v)| format!("{}:{}", format_value_compact(k), format_value_compact(v)))
                .collect();
            format!("{{{}}}", inner.join(","))
        }
        VK::IntMap(m) => {
            let inner: Vec<String> = m
                .iter()
                .enumerate()
                .map(|(i, v)| format!("{}:{}", i, v))
                .collect();
            format!("{{{}}}", inner.join(","))
        }
        VK::Record(r) => {
            let inner: Vec<String> = r
                .iter()
                .map(|(k, v)| format!("{}:{}", k, format_value_compact(v)))
                .collect();
            format!("{{{}}}", inner.join(","))
        }
        VK::Tuple(t) => {
            let inner: Vec<String> = t.iter().map(format_value_compact).collect();
            format!("({})", inner.join(","))
        }
        VK::None => "None".to_string(),
        VK::IntMap2(inner_size, data) => {
            let outer_size = if inner_size > 0 {
                data.len() / inner_size as usize
            } else {
                0
            };
            let inner: Vec<String> = (0..outer_size)
                .map(|i| {
                    let vals: Vec<String> = (0..inner_size as usize)
                        .map(|j| {
                            format!(
                                "{}:{}",
                                j,
                                format_value_compact(&data[i * inner_size as usize + j])
                            )
                        })
                        .collect();
                    format!("{}:{{{}}}", i, vals.join(","))
                })
                .collect();
            format!("{{{}}}", inner.join(","))
        }
        VK::Some(v) => format!("Some({})", format_value_compact(v)),
    }
}

/// Generate a Mermaid sequence diagram from a trace.
///
/// Parses action names to extract participants (process indices from parameters).
/// Actions like "LeaderPreAccept" become notes, "Accept(0, 1)" becomes 0->>1.
fn trace_to_mermaid(
    trace: &[(State, Option<String>)],
    var_names: &[String],
    result_kind: &str,
    invariant: Option<&str>,
) -> String {
    let mut lines = vec!["sequenceDiagram".to_string()];

    // Collect all participants from action parameters
    let mut participants: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();

    // Parse action names: "ActionName(p1, p2, ...)" -> extract integer params
    let mut steps: Vec<(String, Vec<i64>)> = Vec::new();
    for (_, action) in trace.iter() {
        if let Some(name) = action {
            let (action_name, params) = parse_action_params(name);
            for &p in &params {
                participants.insert(format!("P{}", p));
            }
            steps.push((action_name, params));
        } else {
            steps.push(("init".to_string(), vec![]));
        }
    }

    // If no participants found, use generic "System"
    if participants.is_empty() {
        participants.insert("System".to_string());
    }

    for p in &participants {
        lines.push(format!("    participant {}", p));
    }
    lines.push(String::new());

    // Generate diagram steps
    for (i, (state, _action)) in trace.iter().enumerate() {
        let (action_name, params) = &steps[i];

        match params.len() {
            0 => {
                // No params: note over first participant
                let first = participants.iter().next().unwrap();
                lines.push(format!("    Note over {}: {}", first, action_name));
            }
            1 => {
                // Single param: note over that participant
                let p = format!("P{}", params[0]);
                lines.push(format!("    Note over {}: {}", p, action_name));
            }
            _ => {
                // Multiple params: first param acts, message to second
                let src = format!("P{}", params[0]);
                let dst = format!("P{}", params[1]);
                if src == dst {
                    lines.push(format!("    Note over {}: {}", src, action_name));
                } else {
                    lines.push(format!("    {}->>{}: {}", src, dst, action_name));
                }
            }
        }

        // Show state changes as a note (only show changed vars compared to previous)
        if i > 0 {
            let prev_state = &trace[i - 1].0;
            let changes: Vec<String> = state
                .vars
                .iter()
                .enumerate()
                .filter(|(j, v)| *v != &prev_state.vars[*j])
                .map(|(j, v)| {
                    let name = var_names.get(j).map(|s| s.as_str()).unwrap_or("?");
                    format!("{}={}", name, v)
                })
                .collect();
            if !changes.is_empty() && changes.len() <= 3 {
                let actor = if !params.is_empty() {
                    format!("P{}", params[0])
                } else {
                    participants.iter().next().unwrap().clone()
                };
                lines.push(format!(
                    "    Note right of {}: {}",
                    actor,
                    changes.join(", ")
                ));
            }
        }
    }

    // Add violation marker
    if let Some(inv) = invariant {
        lines.push(String::new());
        let last_step = &steps.last().unwrap();
        let actor = if !last_step.1.is_empty() {
            format!("P{}", last_step.1[0])
        } else {
            participants.iter().next().unwrap().clone()
        };
        lines.push("    rect rgb(255, 200, 200)".to_string());
        lines.push(format!(
            "        Note over {}: {} VIOLATION: {}",
            actor,
            result_kind.to_uppercase(),
            inv
        ));
        lines.push("    end".to_string());
    }

    lines.join("\n")
}

/// Parse an action name like "Accept(0, 1)" into ("Accept", [0, 1]).
fn parse_action_params(name: &str) -> (String, Vec<i64>) {
    if let Some(paren_idx) = name.find('(') {
        let action_name = name[..paren_idx].to_string();
        let params_str = &name[paren_idx + 1..name.len().saturating_sub(1)];
        let params: Vec<i64> = params_str
            .split(',')
            .filter_map(|s| s.trim().parse().ok())
            .collect();
        (action_name, params)
    } else {
        (name.to_string(), vec![])
    }
}

/// Print spec profile, warnings, and recommendations.
/// Skips recommendations for optimizations already enabled.
fn print_profile(
    profile: &specl_ir::analyze::SpecProfile,
    por_enabled: bool,
    symmetry_enabled: bool,
) {
    use specl_ir::analyze::Recommendation;

    println!();
    let bound_str = match profile.state_space_bound {
        Some(b) => format!("~{}", format_large_number(b)),
        None => "unbounded".to_string(),
    };
    println!(
        "Spec: {} variables, {} actions, {} invariants, {} states (estimated)",
        profile.num_vars, profile.num_actions, profile.num_invariants, bound_str
    );

    // Warnings
    if !profile.warnings.is_empty() {
        println!();
        println!("Warnings:");
        for w in &profile.warnings {
            println!("  {}", w);
        }
    }

    // Recommendations (skip already-enabled)
    let filtered: Vec<_> = profile
        .recommendations
        .iter()
        .filter(|r| match r {
            Recommendation::EnablePor { .. } => !por_enabled,
            Recommendation::EnableSymmetry { .. } => !symmetry_enabled,
            _ => true,
        })
        .collect();

    if !filtered.is_empty() {
        println!();
        println!("Recommendations:");
        for r in &filtered {
            println!("  {}", r);
        }
    }

    println!();
}

fn print_check_profile(explorer: &Explorer) {
    if let Some(prof) = explorer.profile_data() {
        println!();
        println!("Profile:");
        let total = prof.time_invariants + prof.time_successors + prof.time_store;
        let total_secs = total.as_secs_f64().max(0.001);
        println!(
            "  Invariant checking: {:.1}% ({:.3}s)",
            prof.time_invariants.as_secs_f64() / total_secs * 100.0,
            prof.time_invariants.as_secs_f64()
        );
        println!(
            "  Successor generation: {:.1}% ({:.3}s)",
            prof.time_successors.as_secs_f64() / total_secs * 100.0,
            prof.time_successors.as_secs_f64()
        );
        println!(
            "  Store + queue: {:.1}% ({:.3}s)",
            prof.time_store.as_secs_f64() / total_secs * 100.0,
            prof.time_store.as_secs_f64()
        );

        let total_firings: usize = prof.action_fire_counts.iter().sum();
        if total_firings > 0 {
            println!();
            println!(
                "  Action firings ({} total):",
                format_large_number(total_firings as u128)
            );
            let mut sorted: Vec<(usize, &str, usize)> = prof
                .action_fire_counts
                .iter()
                .enumerate()
                .map(|(i, &count)| (i, prof.action_names[i].as_str(), count))
                .collect();
            sorted.sort_by(|a, b| b.2.cmp(&a.2));
            for (_idx, name, count) in &sorted {
                if *count == 0 {
                    continue;
                }
                let pct = *count as f64 / total_firings as f64 * 100.0;
                println!(
                    "    {}: {} ({:.1}%)",
                    name,
                    format_large_number(*count as u128),
                    pct
                );
            }
            let zero_count = sorted.iter().filter(|s| s.2 == 0).count();
            if zero_count > 0 {
                println!("    ({} actions never fired)", zero_count);
            }
        }
    }
}

fn format_large_number(n: u128) -> String {
    if n >= 1_000_000_000 {
        format!("{:.2}B", n as f64 / 1e9)
    } else if n >= 1_000_000 {
        format!("{:.2}M", n as f64 / 1e6)
    } else if n >= 1_000 {
        format!("{:.1}K", n as f64 / 1e3)
    } else {
        n.to_string()
    }
}

fn cmd_format(file: &PathBuf, write: bool) -> CliResult<()> {
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;

    let formatted = pretty_print(&module);

    if write {
        fs::write(file, &formatted).map_err(|e| CliError::IoError {
            message: e.to_string(),
        })?;
        println!("formatted: {}", file.display());
    } else {
        print!("{}", formatted);
    }

    Ok(())
}

fn cmd_watch(
    file: &PathBuf,
    constants: &[String],
    max_states: usize,
    max_depth: usize,
    check_deadlock: bool,
) -> CliResult<()> {
    println!(
        "Watching {} for changes... (Ctrl+C to stop)",
        file.display()
    );
    println!();

    // Set up file watcher
    let (tx, rx) = mpsc::channel();
    let mut watcher =
        notify::recommended_watcher(move |res: Result<notify::Event, notify::Error>| {
            if let Ok(event) = res {
                if event.kind.is_modify() {
                    let _ = tx.send(());
                }
            }
        })
        .map_err(|e| CliError::Other {
            message: format!("failed to create file watcher: {}", e),
        })?;

    watcher
        .watch(file, RecursiveMode::NonRecursive)
        .map_err(|e| CliError::Other {
            message: format!("failed to watch file: {}", e),
        })?;

    // Run initial check
    run_check_iteration(file, constants, max_states, max_depth, check_deadlock);

    // Watch loop
    loop {
        // Wait for file change
        if rx.recv().is_err() {
            break;
        }

        // Debounce: wait a bit and drain any additional events
        std::thread::sleep(Duration::from_millis(100));
        while rx.try_recv().is_ok() {}

        // Clear screen
        print!("\x1B[2J\x1B[H");

        // Re-run check
        run_check_iteration(file, constants, max_states, max_depth, check_deadlock);
    }

    Ok(())
}

/// Run a single check iteration, printing results (doesn't return error, prints it instead).
fn run_check_iteration(
    file: &PathBuf,
    constants: &[String],
    max_states: usize,
    max_depth: usize,
    check_deadlock: bool,
) {
    let filename = file.display().to_string();
    let source = match fs::read_to_string(file) {
        Ok(s) => Arc::new(s),
        Err(e) => {
            eprintln!("Error: failed to read file: {}", e);
            return;
        }
    };

    // Parse
    let module = match parse(&source) {
        Ok(m) => m,
        Err(e) => {
            let err = CliError::from_parse_error(e, source.clone(), &filename);
            eprintln!("{:?}", miette::Report::new(err));
            return;
        }
    };

    // Type check
    if let Err(e) = specl_types::check_module(&module) {
        let err = CliError::from_type_error(e, source.clone(), &filename);
        eprintln!("{:?}", miette::Report::new(err));
        return;
    }

    // Compile
    let spec = match compile(&module) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Compile error: {}", e);
            return;
        }
    };

    // Parse constants
    let consts = match parse_constants(constants, &spec) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{:?}", miette::Report::new(e));
            return;
        }
    };

    // Reject unbounded types for explicit-state checking
    let profile = analyze(&spec);
    let unbounded_warnings: Vec<_> = profile
        .warnings
        .iter()
        .filter(|w| matches!(w, specl_ir::analyze::Warning::UnboundedType { .. }))
        .collect();
    if !unbounded_warnings.is_empty() {
        eprintln!("Note: spec has types the checker considers unbounded (Dict[Int, ...]).");
        eprintln!(
            "  BFS proceeds because runtime values are bounded by init and action parameters."
        );
    }

    let progress = Arc::new(ProgressCounters::new());
    let start = Instant::now();

    let spinner = if std::io::stderr().is_terminal() {
        let pb = ProgressBar::new_spinner();
        pb.set_style(
            ProgressStyle::with_template("{spinner:.cyan} {msg}")
                .unwrap()
                .tick_chars("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"),
        );
        pb.enable_steady_tick(Duration::from_millis(100));
        pb.set_message("starting...");
        let p = progress.clone();
        let pb2 = pb.clone();
        let start2 = start;
        std::thread::spawn(move || loop {
            std::thread::sleep(Duration::from_millis(100));
            let checked = p.checked.load(std::sync::atomic::Ordering::Relaxed);
            if checked == 0 {
                continue;
            }
            let states = p.states.load(std::sync::atomic::Ordering::Relaxed);
            let depth = p.depth.load(std::sync::atomic::Ordering::Relaxed);
            let elapsed = start2.elapsed().as_secs_f64();
            let rate = if elapsed > 0.0 {
                checked as f64 / elapsed
            } else {
                0.0
            };
            pb2.set_message(format!(
                "{} found | {} checked | depth {} | {} states/s",
                format_large_number(states as u128),
                format_large_number(checked as u128),
                depth,
                format_large_number(rate as u128),
            ));
            if pb2.is_finished() {
                break;
            }
        });
        Some(pb)
    } else {
        None
    };

    let config = CheckConfig {
        check_deadlock,
        max_states,
        max_depth,
        progress: Some(progress),
        ..Default::default()
    };

    let mut explorer = Explorer::new(spec, consts, config);
    let result = match explorer.check() {
        Ok(r) => r,
        Err(e) => {
            if let Some(ref pb) = spinner {
                pb.finish_and_clear();
            }
            eprintln!("Check error: {}", e);
            return;
        }
    };

    let elapsed = start.elapsed();
    if let Some(ref pb) = spinner {
        pb.finish_and_clear();
    }

    match result {
        CheckOutcome::Ok {
            states_explored,
            max_depth,
        } => {
            println!("Result: OK");
            println!("  States explored: {}", states_explored);
            println!("  Max depth: {}", max_depth);
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
            println!(
                "  States/sec: {:.0}",
                states_explored as f64 / elapsed.as_secs_f64()
            );
        }
        CheckOutcome::InvariantViolation { invariant, trace } => {
            println!("Result: INVARIANT VIOLATION");
            println!("  Invariant: {}", invariant);
            println!("  Trace ({} steps):", trace.len());
            for (i, (state, action)) in trace.iter().enumerate() {
                let action_str = action.as_deref().unwrap_or("init");
                println!("    {}: {} -> {}", i, action_str, state);
            }
        }
        CheckOutcome::Deadlock { trace } => {
            println!("Result: DEADLOCK");
            println!("  Trace ({} steps):", trace.len());
            for (i, (state, action)) in trace.iter().enumerate() {
                let action_str = action.as_deref().unwrap_or("init");
                println!("    {}: {} -> {}", i, action_str, state);
            }
        }
        CheckOutcome::StateLimitReached {
            states_explored,
            max_depth,
        } => {
            println!("Result: STATE LIMIT REACHED");
            println!("  States explored: {}", states_explored);
            println!("  Max depth: {}", max_depth);
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
        }
        CheckOutcome::MemoryLimitReached {
            states_explored,
            max_depth,
            memory_mb,
        } => {
            println!("Result: MEMORY LIMIT REACHED");
            println!("  Memory usage: {} MB", memory_mb);
            println!("  States explored: {}", states_explored);
            println!("  Max depth: {}", max_depth);
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
        }
        CheckOutcome::TimeLimitReached {
            states_explored,
            max_depth,
        } => {
            println!("Result: TIME LIMIT REACHED");
            println!("  States explored: {}", states_explored);
            println!("  Max depth: {}", max_depth);
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
        }
    }

    println!();
    println!("Watching for changes...");
}

fn cmd_estimate(file: &PathBuf, constants: &[String]) -> CliResult<()> {
    let filename = file.display().to_string();
    let source = Arc::new(fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?);

    let module =
        parse(&source).map_err(|e| CliError::from_parse_error(e, source.clone(), &filename))?;
    specl_types::check_module(&module)
        .map_err(|e| CliError::from_type_error(e, source.clone(), &filename))?;
    let spec = compile(&module).map_err(|e| CliError::CompileError {
        message: e.to_string(),
    })?;
    let consts = parse_constants(constants, &spec)?;

    let profile = analyze(&spec);

    // Header with constants
    let const_strs: Vec<String> = spec
        .consts
        .iter()
        .map(|c| format!("{}={}", c.name, consts[c.index]))
        .collect();
    println!();
    if const_strs.is_empty() {
        println!("Estimated state space: {} ({})", module.name.name, filename);
    } else {
        println!(
            "Estimated state space: {} ({})",
            module.name.name,
            const_strs.join(", ")
        );
    }

    // Variable breakdown
    println!("  Variables: {}, avg domain size: {}", profile.num_vars, {
        let bounded: Vec<f64> = profile
            .var_domain_sizes
            .iter()
            .filter_map(|(_, _, d)| d.map(|s| s as f64))
            .collect();
        if bounded.is_empty() {
            "unbounded".to_string()
        } else {
            let avg = bounded.iter().sum::<f64>() / bounded.len() as f64;
            format!("{:.1}", avg)
        }
    });

    // Action branching
    let total_combos: Option<u64> = {
        let mut sum = 0u64;
        let mut all_bounded = true;
        for (_, c) in &profile.action_param_counts {
            match c {
                Some(n) => sum = sum.saturating_add(*n),
                None => all_bounded = false,
            }
        }
        if all_bounded {
            Some(sum)
        } else {
            None
        }
    };
    match total_combos {
        Some(c) => println!(
            "  Actions: {}, total branching factor: ~{}",
            profile.num_actions, c
        ),
        None => println!(
            "  Actions: {}, branching factor: unbounded",
            profile.num_actions
        ),
    }

    // State space estimate
    match profile.state_space_bound {
        Some(bound) => {
            println!("  Estimated states: ~{}", format_large_number(bound));

            // Time estimate: assume 80K states/s single-thread, ~300K multi-thread
            let secs_single = bound as f64 / 80_000.0;
            let secs_multi = bound as f64 / 300_000.0;
            println!(
                "  Estimated time: ~{} (single-threaded) / ~{} (parallel)",
                format_duration(secs_single),
                format_duration(secs_multi)
            );

            // Memory estimate: ~80 bytes/state full tracking, 8 bytes/state fast
            let mem_full_mb = (bound as f64 * 80.0) / (1024.0 * 1024.0);
            let mem_fast_mb = (bound as f64 * 8.0) / (1024.0 * 1024.0);
            println!(
                "  Memory estimate: ~{} (full tracking) / ~{} (--fast)",
                format_memory(mem_full_mb),
                format_memory(mem_fast_mb)
            );
        }
        None => {
            println!("  Estimated states: unbounded (cannot estimate)");
            println!();
            println!("  Tip: Use --bmc for symbolic bounded model checking with unbounded types,");
            println!("       or add range bounds to variables for exhaustive checking.");
        }
    }

    // Per-variable breakdown
    println!();
    println!("  Variable breakdown:");
    for (name, ty, domain) in &profile.var_domain_sizes {
        match domain {
            Some(size) => println!(
                "    {}: {} ({} values)",
                name,
                ty,
                format_large_number(*size)
            ),
            None => println!("    {}: {} (unbounded)", name, ty),
        }
    }

    // Tips
    if let Some(bound) = profile.state_space_bound {
        println!();
        if bound > 100_000_000 {
            println!("  Tip: Use --fast for fingerprint-only mode (10x less memory, no traces)");
            println!("       Use --bloom for fixed-memory probabilistic mode (UNSOUND: bug finding only)");
        }
        if bound > 10_000_000 {
            if profile.has_symmetry {
                let factors: Vec<String> = profile
                    .symmetry_domain_sizes
                    .iter()
                    .map(|s| format!("{}x", factorial(*s as u64)))
                    .collect();
                println!(
                    "  Tip: Use --symmetry for up to {} reduction",
                    factors.join(", ")
                );
            }
            let independence_pct = (profile.independence_ratio * 100.0) as u32;
            if independence_pct >= 20 {
                println!(
                    "  Tip: Use --por ({}% of action pairs are independent)",
                    independence_pct
                );
            }
        }
    }

    println!();
    Ok(())
}

/// Parse a `// Use:` comment line from a specl file to extract check arguments.
struct UseComment {
    constants: Vec<String>,
    no_deadlock: bool,
    fast: bool,
    max_states: usize,
}

fn parse_use_comment(source: &str) -> Option<UseComment> {
    for line in source.lines() {
        if !line.starts_with("// Use:") {
            continue;
        }
        let rest = line.trim_start_matches("// Use:").trim();

        // "No constants needed" case
        if rest.contains("No constants needed") {
            return Some(UseComment {
                constants: Vec::new(),
                no_deadlock: false,
                fast: false,
                max_states: 0,
            });
        }

        let mut constants = Vec::new();
        let mut no_deadlock = false;
        let mut fast = false;
        let mut max_states: usize = 0;

        let parts: Vec<&str> = rest.split_whitespace().collect();
        let mut i = 0;
        while i < parts.len() {
            match parts[i] {
                "-c" => {
                    if i + 1 < parts.len() {
                        constants.push(parts[i + 1].to_string());
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                "--no-deadlock" => {
                    no_deadlock = true;
                    i += 1;
                }
                "--fast" => {
                    fast = true;
                    i += 1;
                }
                "--max-states" => {
                    if i + 1 < parts.len() {
                        max_states = parts[i + 1].parse().unwrap_or(0);
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                p if p.starts_with("-c") => {
                    // Handle -cN=3 style (no space)
                    constants.push(p.trim_start_matches("-c").to_string());
                    i += 1;
                }
                _ => {
                    i += 1;
                }
            }
        }

        return Some(UseComment {
            constants,
            no_deadlock,
            fast,
            max_states,
        });
    }
    None
}

fn find_specl_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if dir.is_dir() {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    files.extend(find_specl_files(&path));
                } else if path.extension().is_some_and(|e| e == "specl") {
                    files.push(path);
                }
            }
        }
    }
    files.sort();
    files
}

/// Skip specs that are known to be too large for quick testing
/// or have Use: comments with intentionally small parameters.
const TEST_SKIP: &[&str] = &[
    "RaftMongo.specl",
    "ChainReplication.specl",
    "sem-santa_claus.specl", // Use: params too small for invariant (NUM_ELVES=2 < 3)
];

fn cmd_test(
    dir: Option<&PathBuf>,
    override_max_states: usize,
    max_time_per_spec: u64,
) -> CliResult<()> {
    let test_dir = dir.cloned().unwrap_or_else(|| {
        // Default: look for examples/ relative to current dir
        PathBuf::from("examples")
    });

    if !test_dir.is_dir() {
        return Err(CliError::IoError {
            message: format!("directory not found: {}", test_dir.display()),
        });
    }

    let files = find_specl_files(&test_dir);
    if files.is_empty() {
        println!("No .specl files found in {}", test_dir.display());
        return Ok(());
    }

    println!("Testing {} specs in {}", files.len(), test_dir.display());
    println!();

    let mut passed = 0;
    let mut failed = 0;
    let mut skipped = 0;
    let mut failures: Vec<String> = Vec::new();
    let total_start = Instant::now();

    for file in &files {
        let filename = file.file_name().unwrap().to_str().unwrap();

        // Skip known large specs
        if TEST_SKIP.contains(&filename) {
            println!("  SKIP  {}", file.display());
            skipped += 1;
            continue;
        }

        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                println!("  FAIL  {} (read error: {})", file.display(), e);
                failures.push(format!("{}: read error: {}", file.display(), e));
                failed += 1;
                continue;
            }
        };

        // Parse Use: comment for constants and flags
        let use_comment = parse_use_comment(&source);
        let (constants, no_deadlock, fast, comment_max_states) = match &use_comment {
            Some(uc) => (uc.constants.clone(), uc.no_deadlock, uc.fast, uc.max_states),
            None => {
                // No Use: comment — skip (can't know constants)
                println!("  SKIP  {} (no // Use: comment)", file.display());
                skipped += 1;
                continue;
            }
        };

        // Parse
        let module = match parse(&source) {
            Ok(m) => m,
            Err(e) => {
                println!("  FAIL  {} (parse: {})", file.display(), e);
                failures.push(format!("{}: parse error: {}", file.display(), e));
                failed += 1;
                continue;
            }
        };

        // Type check
        if let Err(e) = specl_types::check_module(&module) {
            println!("  FAIL  {} (typecheck: {})", file.display(), e);
            failures.push(format!("{}: typecheck error: {}", file.display(), e));
            failed += 1;
            continue;
        }

        // Compile
        let spec = match compile(&module) {
            Ok(s) => s,
            Err(e) => {
                println!("  FAIL  {} (compile: {})", file.display(), e);
                failures.push(format!("{}: compile error: {}", file.display(), e));
                failed += 1;
                continue;
            }
        };

        // Resolve constants (default unspecified ones to 1)
        let mut const_values = vec![Value::none(); spec.consts.len()];
        for const_decl in &spec.consts {
            let mut found = false;
            for c in &constants {
                if let Some((name, val)) = c.split_once('=') {
                    if name == const_decl.name {
                        if let Ok(v) = val.parse::<i64>() {
                            const_values[const_decl.index] = Value::int(v);
                            found = true;
                            break;
                        }
                    }
                }
            }
            if !found {
                const_values[const_decl.index] = Value::int(1);
            }
        }
        let consts = const_values;

        let effective_max_states = if override_max_states > 0 {
            override_max_states
        } else if comment_max_states > 0 {
            comment_max_states
        } else {
            1_000_000 // Default limit for testing
        };

        let config = CheckConfig {
            check_deadlock: !no_deadlock,
            max_states: effective_max_states,
            max_depth: 0,
            fast_check: fast,
            max_time_secs: max_time_per_spec,
            ..Default::default()
        };

        let start = Instant::now();
        let mut explorer = Explorer::new(spec, consts, config);
        let result = match explorer.check() {
            Ok(r) => r,
            Err(e) => {
                println!("  FAIL  {} (check error: {})", file.display(), e);
                failures.push(format!("{}: check error: {}", file.display(), e));
                failed += 1;
                continue;
            }
        };

        let elapsed = start.elapsed();
        let secs = elapsed.as_secs_f64();

        match &result {
            CheckOutcome::Ok {
                states_explored, ..
            } => {
                println!(
                    "  PASS  {} ({} states, {:.1}s)",
                    file.display(),
                    format_large_number(*states_explored as u128),
                    secs
                );
                passed += 1;
            }
            CheckOutcome::StateLimitReached {
                states_explored, ..
            } => {
                println!(
                    "  PASS  {} ({} states [limit], {:.1}s)",
                    file.display(),
                    format_large_number(*states_explored as u128),
                    secs
                );
                passed += 1;
            }
            CheckOutcome::MemoryLimitReached {
                states_explored, ..
            } => {
                println!(
                    "  PASS  {} ({} states [mem limit], {:.1}s)",
                    file.display(),
                    format_large_number(*states_explored as u128),
                    secs
                );
                passed += 1;
            }
            CheckOutcome::TimeLimitReached {
                states_explored, ..
            } => {
                println!(
                    "  PASS  {} ({} states [time limit], {:.1}s)",
                    file.display(),
                    format_large_number(*states_explored as u128),
                    secs
                );
                passed += 1;
            }
            CheckOutcome::InvariantViolation { invariant, .. } => {
                // Some examples intentionally have bugs
                if source.contains("intentional")
                    || source.contains("bug")
                    || source.contains("BUG")
                {
                    println!(
                        "  PASS  {} (expected violation: {}, {:.1}s)",
                        file.display(),
                        invariant,
                        secs
                    );
                    passed += 1;
                } else {
                    println!(
                        "  FAIL  {} (invariant violation: {})",
                        file.display(),
                        invariant
                    );
                    failures.push(format!(
                        "{}: invariant violation: {}",
                        file.display(),
                        invariant
                    ));
                    failed += 1;
                }
            }
            CheckOutcome::Deadlock { .. } => {
                println!("  PASS  {} (deadlock found, {:.1}s)", file.display(), secs);
                passed += 1;
            }
        }
    }

    let total_secs = total_start.elapsed().as_secs_f64();
    println!();
    println!(
        "Results: {} passed, {} failed, {} skipped ({:.1}s)",
        passed, failed, skipped, total_secs
    );

    if !failures.is_empty() {
        println!();
        println!("Failures:");
        for f in &failures {
            println!("  {}", f);
        }
        std::process::exit(1);
    }

    Ok(())
}

fn format_duration(secs: f64) -> String {
    if secs < 1.0 {
        format!("{:.0}ms", secs * 1000.0)
    } else if secs < 60.0 {
        format!("{:.1}s", secs)
    } else if secs < 3600.0 {
        format!("{:.0}min", secs / 60.0)
    } else if secs < 86400.0 {
        format!("{:.1}h", secs / 3600.0)
    } else {
        format!("{:.0}d", secs / 86400.0)
    }
}

fn format_memory(mb: f64) -> String {
    if mb < 1.0 {
        format!("{:.0} KB", mb * 1024.0)
    } else if mb < 1024.0 {
        format!("{:.0} MB", mb)
    } else {
        format!("{:.1} GB", mb / 1024.0)
    }
}

fn factorial(n: u64) -> u64 {
    (1..=n).fold(1u64, |acc, x| acc.saturating_mul(x))
}

fn cmd_translate(file: &PathBuf, output: Option<&PathBuf>) -> CliResult<()> {
    let source = fs::read_to_string(file).map_err(|e| CliError::IoError {
        message: e.to_string(),
    })?;

    let specl_source = specl_tla::translate(&source).map_err(|e| CliError::TranslateError {
        message: e.to_string(),
    })?;

    if let Some(output_path) = output {
        fs::write(output_path, &specl_source).map_err(|e| CliError::IoError {
            message: e.to_string(),
        })?;
        println!(
            "translated: {} -> {}",
            file.display(),
            output_path.display()
        );
    } else {
        print!("{}", specl_source);
    }

    Ok(())
}

fn cmd_perf_guide() -> CliResult<()> {
    print!(
        "\
SPECL PERFORMANCE GUIDE
=======================

1. STATE SPACE DRIVERS
   Every variable adds a multiplicative factor to the total state space.
   The key driver is the number of distinct values each variable can hold.

   Type                          Distinct values (approx)
   -------------------------------------------------------
   Bool                          2
   0..K                          K+1
   Set[0..K]                     2^(K+1)             (powerset!)
   Seq[0..K] up to length L      sum_i (K+1)^i for i=0..L
   Dict[0..N, 0..K]              (K+1)^(N+1)
   Dict[0..N, Dict[0..M, V]]     |V|^((N+1)*(M+1))  (nested = exponent of exponent)
   Option[T]                      |T| + 1

   Total state space ~= product of |V_i| for each variable V_i.

   Action parameter explosion:
   An action with P parameters of sizes D1, D2, ..., DP generates
   D1 * D2 * ... * DP parameter combinations per state. Each combination
   is a potential transition the checker must evaluate.

   Example: Transfer(from: 0..N, to: 0..N, amount: 1..MAX)
   = (N+1) * (N+1) * MAX combinations per state.

2. WRITING FAST SPECS
   a) Minimize variable domains
      Use the smallest type that captures your intent.
      Dict[Int, Bool] has 2^N states vs Dict[Int, 0..K] with (K+1)^N.

   b) Avoid deep nesting
      Dict[0..N, Dict[0..M, V]] has |V|^(N*M) states.
      If the inner dict models per-pair state, consider whether you really
      need all N*M entries, or whether a Set of pairs suffices.

   c) Separate message types
      var msgs: Set[Seq[Int]] (one bag for all message types) means every
      message type interferes with every other. Instead use separate
      variables per message type:
        var voteReqs: Set[(Int, Int)]
        var voteResps: Set[(Int, Int, Bool)]
      This also improves POR (more independent actions).

   d) Use selective guards
      The checker evaluates guards to prune parameter combinations early.
      A require that references a dict lookup (e.g., require state[i] == 1)
      is scored ~10x more selective than a simple comparison. The checker
      automatically reorders parameter binding to evaluate the most selective
      guards first. Help it by writing guards that reference action parameters.

   e) Prefer Dict[Int, V] over Dict[String, V]
      Integer-keyed dicts with keys 0..N are stored as dense arrays (IntMap)
      internally. String or sparse keys fall back to sorted-pair representation,
      which is slower to hash, clone, and compare.

   f) Avoid powerset quantifiers
      Expressions like: any s in powerset(0..N): ... enumerate 2^N subsets.
      Restructure as existential quantifiers over individual elements when
      possible.

   g) Use bounded constants
      0..V+1 is invalid in parameter ranges. Define a const MaxVal and use
      0..MaxVal. Start with small constants (N=2, MAX=3) and scale up.

3. INVARIANT PERFORMANCE
   The checker tracks which variables each invariant depends on (inv_dep_masks).
   After each state transition, only invariants whose dependencies changed are
   rechecked. This is automatic — no user action needed.

   To benefit most:
   - Write invariants that reference few variables.
   - Avoid invariants with O(N^2) quantifiers when O(N) suffices.
   - Use --check-only Name to focus on a specific invariant during debugging.

4. STORAGE MODE GUIDE
   Storage modes control how visited states are stored for deduplication.
   Only one mode is active at a time. Each has different memory/trace tradeoffs.

   Mode        Memory/state   Traces?   Notes
   ---------------------------------------------------------------
   default     80-200 bytes   Yes       Full state stored. Sound.
   --fast      8 bytes        No        Fingerprint only. Sound (2^-64 collision).
                                        If violation found, re-run without --fast for trace.
   --collapse  30-60 bytes    Yes       Per-variable interning. Sound.
                                        Good balance of memory and trace support.
   --tree      20-50 bytes    Yes       Hierarchical subtree sharing (LTSmin-style). Sound.
                                        Best compression for specs with many similar states.
   --bloom     Fixed total    No        Probabilistic. UNSOUND: false positives skip states.
                                        For bug finding only, not verification.

   Decision tree:
   - State space < 5M states?     -> default (full storage, best debugging)
   - 5M-50M states?               -> --collapse (3x less memory, keeps traces)
   - 50M+ states or OOM?          -> --fast (10x less memory, no traces)
   - Want bug finding, not proof?  -> --fast or --bloom
   - Many similar states?          -> --tree (best compression ratio)

5. OPTIMIZATION FLAGS
   --por              Partial Order Reduction. Skips redundant action interleavings
                      when actions are independent (don't read/write overlapping vars).
                      Auto-enabled when >30%% of action pairs are independent.
                      Forces single-threaded exploration (sequential BFS).
                      Typical reduction: 2-10x.

   --symmetry         Symmetry Reduction. Groups equivalent states that differ only
                      in process identity. Auto-enabled when symmetric Dict patterns
                      are detected. Reduction up to N! (e.g., 24x for N=4).

   --directed         Priority BFS. Explores states closer to invariant violations
                      first. Finds bugs faster but does not guarantee shortest trace.
                      Uses directed mode's OpCache (32K-entry direct-mapped cache)
                      to skip redundant action evaluations.

   --swarm N          Parallel random exploration. Launches N instances with shuffled
                      action orderings. Good for bug hunting in very large state spaces.

   --incremental      Caches the set of visited state fingerprints between runs.
                      Subsequent runs skip already-explored states. Invalidates
                      automatically if the spec changes (content hash).

   --no-parallel      Force single-threaded. Useful for deterministic debugging
                      or when combined with --por (which is already single-threaded).

   --threads N        Set thread count for parallel BFS (default: all cores).

6. PRACTICAL BOUNDS
   N=2:  Always start here.    Typical: 10K-2M states. Seconds.
   N=3:  For confidence.       Typical: 100K-100M states. Seconds to minutes.
   N=4+: Large state spaces.   Use --fast + --por + --symmetry.
   N=5+: Usually requires      --fast + --por + --symmetry + --max-states.

   Use --max-states to cap exploration when iterating on a spec.
   Use --max-time for CI pipelines (e.g., --max-time 60 for 1-minute budget).

7. PROFILING YOUR SPEC
   specl info FILE -c N=2
     Static analysis: state space estimates per variable, action parameter
     combination counts, recommended flags, detected optimizations (POR %%,
     symmetry candidates).

   specl estimate FILE -c N=2
     Estimate total states, time, and memory requirements without running
     the full check.

   specl check FILE -c N=2 --profile
     After checking, prints per-action firing counts and timing breakdown.
     Shows which actions dominate exploration time.

8. SOUNDNESS
   Sound modes (can prove absence of bugs):
     default, --fast, --collapse, --tree, --por, --symmetry, --incremental

   --fast has a theoretical 2^-64 hash collision probability per state pair.
   The checker detects collisions when possible and warns.

   --bloom is UNSOUND: false positives cause states to be skipped entirely.
   Use only for bug hunting, never for verification.

   --symmetry is sound only if your spec is truly symmetric with respect to
   the process identities. An asymmetric spec (e.g., process 0 is special)
   with --symmetry may miss bugs.

9. PARALLEL MODE
   The default parallel BFS distributes states across threads using rayon.
   Each thread maintains its own evaluation buffers (VmBufs) — no contention
   on the hot path. State deduplication uses lock-free structures (DashMap for
   full storage, AtomicFPSet for fingerprint mode).

   Optimizations active in parallel mode:
     - Incremental fingerprint hashing (XOR-decomposable, O(changed vars))
     - inv_dep_masks (skip unchanged invariants)
     - NaN-boxed Values (8-byte inline, no allocation for ints/bools)
     - IntMap dense storage for Dict[Int, V]
     - Superinstruction fusion in bytecode VM

   Not active in parallel mode:
     - POR (requires sequential BFS for sleep set propagation)
     - OpCache (directed mode only)

   Parallel mode scales near-linearly up to ~8 cores, then memory bandwidth
   becomes the bottleneck. Use --threads to control.
"
    );
    Ok(())
}
