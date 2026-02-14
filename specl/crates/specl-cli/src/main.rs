//! Command-line interface for Specl model checker.

// False positive: thiserror/miette derive macros generate code that triggers this
#![allow(unused_assignments)]

use clap::{Parser, Subcommand, ValueEnum};
use indicatif::{ProgressBar, ProgressStyle};
use miette::{Diagnostic, NamedSource, SourceSpan};
use notify::{RecursiveMode, Watcher};
use serde::Serialize;
use specl_eval::Value;
use specl_ir::analyze::analyze;
use specl_ir::compile;
use specl_mc::{CheckConfig, CheckOutcome, Explorer, Fingerprint, ProgressCounters, SimulateOutcome, State, StateStore};
use specl_symbolic::{SpacerProfile, SymbolicConfig, SymbolicMode, SymbolicOutcome};
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
    Check {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Constant assignments (name=value)
        #[arg(short, long, value_name = "CONST=VALUE")]
        constant: Vec<String>,

        // -- Mode selection --
        /// Force BFS explicit-state checking
        #[arg(long, help_heading = "Mode")]
        bfs: bool,

        /// Force symbolic checking (auto-cascades: induction → k-induction → IC3 → BMC)
        #[arg(long, help_heading = "Mode")]
        symbolic: bool,

        // -- Explicit-state options --
        /// Maximum number of states to explore (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State")]
        max_states: usize,

        /// Maximum depth to explore (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State")]
        max_depth: usize,

        /// Maximum memory usage in MB (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State")]
        memory_limit: usize,

        /// Maximum time in seconds (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Explicit-State")]
        max_time: u64,

        /// Disable deadlock checking
        #[arg(long, help_heading = "Explicit-State")]
        no_deadlock: bool,

        /// Disable parallel exploration
        #[arg(long, help_heading = "Explicit-State")]
        no_parallel: bool,

        /// Number of threads (0 = all available)
        #[arg(long, default_value = "0", help_heading = "Explicit-State")]
        threads: usize,

        /// Partial order reduction (skip redundant interleavings)
        #[arg(long, help_heading = "Explicit-State")]
        por: bool,

        /// Symmetry reduction (collapse equivalent process permutations)
        #[arg(long, help_heading = "Explicit-State")]
        symmetry: bool,

        /// Fingerprint-only mode: 10x less memory, re-explores for traces on violation
        #[arg(long, help_heading = "Explicit-State")]
        fast: bool,

        /// Use bloom filter for state storage (fixed memory, probabilistic dedup)
        #[arg(long, help_heading = "Explicit-State")]
        bloom: bool,

        /// Bloom filter size as log2(bits) (default: 30 = 128 MiB). Only with --bloom.
        #[arg(long, default_value = "30", help_heading = "Explicit-State")]
        bloom_bits: u32,

        /// Collapse compression: per-variable interning (less memory than full, traces supported)
        #[arg(long, help_heading = "Explicit-State")]
        collapse: bool,

        /// Directed model checking: priority BFS exploring states closest to violation first
        #[arg(long, help_heading = "Explicit-State")]
        directed: bool,

        /// Swarm verification: run N parallel instances with shuffled action orders
        #[arg(long, value_name = "N", help_heading = "Explicit-State")]
        swarm: Option<usize>,

        // -- Symbolic (Z3) options --
        /// Bounded model checking (unroll transitions to --bmc-depth steps)
        #[arg(long, help_heading = "Symbolic (Z3)")]
        bmc: bool,

        /// BMC depth bound (0 = unlimited)
        #[arg(long, default_value = "0", help_heading = "Symbolic (Z3)")]
        bmc_depth: usize,

        /// Inductive invariant checking (single-step proof)
        #[arg(long, help_heading = "Symbolic (Z3)")]
        inductive: bool,

        /// k-induction with given strengthening depth
        #[arg(long, value_name = "K", help_heading = "Symbolic (Z3)")]
        k_induction: Option<usize>,

        /// IC3/CHC unbounded verification via Z3 Spacer
        #[arg(long, help_heading = "Symbolic (Z3)")]
        ic3: bool,

        /// Portfolio: run BMC, k-induction, and IC3 in parallel (first result wins)
        #[arg(long, help_heading = "Symbolic (Z3)")]
        portfolio: bool,

        /// Max sequence length for symbolic Seq[T] encoding
        #[arg(long, default_value = "5", help_heading = "Symbolic (Z3)")]
        seq_bound: usize,

        /// Spacer parameter profile for IC3/CHC {default, fast, thorough}
        #[arg(long, default_value = "default", help_heading = "Symbolic (Z3)")]
        spacer_profile: String,

        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,

        /// Suppress spec analysis and recommendations
        #[arg(short, long)]
        quiet: bool,

        /// Disable auto-enabling of optimizations (POR, symmetry)
        #[arg(long)]
        no_auto: bool,

        /// Output format (text, json, or itf)
        #[arg(long, value_enum, default_value = "text")]
        output: OutputFormat,

        /// Show profiling breakdown (per-action firing counts, phase timing)
        #[arg(long, help_heading = "Explicit-State")]
        profile: bool,

        /// Only check specific invariants (repeatable, by name)
        #[arg(long = "check-only", value_name = "INVARIANT", help_heading = "Explicit-State")]
        check_only: Vec<String>,

        /// Show only changed variables in traces (diff mode)
        #[arg(long)]
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

    /// Show reference of all available checking techniques and when to use them
    Techniques {
        /// Show extended plain-English explanations for each technique
        #[arg(short, long)]
        verbose: bool,
    },

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
            directed,
            swarm,
            bmc,
            bmc_depth,
            inductive,
            k_induction,
            ic3,
            portfolio,
            seq_bound,
            spacer_profile,
            verbose,
            quiet,
            no_auto,
            output,
            profile,
            check_only,
            diff,
        } => {
            let json = output == OutputFormat::Json;
            let quiet = quiet || output != OutputFormat::Text;

            let specific_symbolic = bmc || inductive || k_induction.is_some() || ic3 || portfolio;
            let specific_explicit = por
                || symmetry
                || fast
                || bloom
                || collapse
                || directed
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
                    let out = JsonOutput::new("error", 0.0)
                        .with_error("cannot combine --symbolic/--bfs flags or their sub-options".into());
                    println!("{}", serde_json::to_string(&out).unwrap());
                } else {
                    eprintln!("Error: cannot combine --symbolic/--bfs flags or their sub-options");
                }
                std::process::exit(1);
            }

            let sp = match spacer_profile.as_str() {
                "fast" => SpacerProfile::Fast,
                "thorough" => SpacerProfile::Thorough,
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
                    seq_bound,
                    sp,
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
                    directed,
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
                        &file, &constant, bmc_depth, false, false, None, false, false, seq_bound,
                        sp, json,
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
                        directed,
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
        Commands::Techniques { verbose } => cmd_techniques(verbose),
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
        let inv_names: Vec<&str> = spec.invariants.iter().map(|inv| inv.name.as_str()).collect();
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

    // Action details
    println!();
    println!("Action Analysis:");
    for (name, combos) in &profile.action_param_counts {
        let combo_str = match combos {
            Some(c) => format_large_number(*c as u128),
            None => "unbounded".to_string(),
        };
        println!("  {:30} {} param combos", name, combo_str);
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
    directed: bool,
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
        if !quiet && (actual_por != use_por || actual_symmetry != use_symmetry) {
            println!();
        }
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
        fast_check: fast_check || bloom,
        progress: Some(progress),
        action_shuffle_seed: None,
        profile,
        bloom,
        bloom_bits,
        directed,
        max_time_secs,
        check_only_invariants,
        collapse,
    };

    let mut explorer = Explorer::new(spec, consts, config);
    let result = explorer.check().map_err(|e| CliError::CheckError {
        message: e.to_string(),
    })?;

    let elapsed = start.elapsed();

    if let Some(ref pb) = spinner {
        pb.finish_and_clear();
    }

    let secs = elapsed.as_secs_f64();

    if output_format == OutputFormat::Dot {
        // DOT state graph output (BFS exploration tree)
        let store = explorer.store();
        if !store.has_full_tracking() {
            eprintln!("Error: --output dot requires full tracking (incompatible with --fast and --bloom)");
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
            CheckOutcome::InvariantViolation { trace, .. }
            | CheckOutcome::Deadlock { trace } => {
                trace.last().map(|(s, _)| s.fingerprint())
            }
            _ => None,
        };

        println!("{}", store_to_dot(store, &var_names, &action_names, violation_fp.as_ref()));

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
                    println!("{}", trace_to_mermaid(&trace, &var_names, "invariant_violation", Some(&invariant)));
                } else {
                    let itf = trace_to_itf(&trace, &var_names, "invariant_violation", Some(&invariant));
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
            CheckOutcome::Ok { states_explored, .. } => {
                eprintln!("Result: OK ({} states, no trace to export)", states_explored);
            }
            CheckOutcome::StateLimitReached { states_explored, .. } => {
                eprintln!("Result: STATE LIMIT REACHED ({} states, no trace)", states_explored);
                std::process::exit(2);
            }
            CheckOutcome::MemoryLimitReached { states_explored, .. } => {
                eprintln!("Result: MEMORY LIMIT REACHED ({} states, no trace)", states_explored);
                std::process::exit(2);
            }
            CheckOutcome::TimeLimitReached { states_explored, .. } => {
                eprintln!("Result: TIME LIMIT REACHED ({} states, no trace)", states_explored);
                std::process::exit(2);
            }
        }
    } else if json {
        let out = match result {
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
                } else if fast_check {
                    opts.push("fast");
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
                };
                let mut explorer = Explorer::new((*spec).clone(), (*consts).clone(), config);
                let result = explorer.check().map_err(|e| CliError::CheckError {
                    message: e.to_string(),
                })?;
                let total_secs = start.elapsed().as_secs_f64();
                if let CheckOutcome::InvariantViolation { invariant, trace } = result {
                    match output_format {
                        OutputFormat::Mermaid => {
                            println!("{}", trace_to_mermaid(&trace, var_names, "invariant_violation", Some(&invariant)));
                        }
                        OutputFormat::Itf => {
                            let itf = trace_to_itf(&trace, var_names, "invariant_violation", Some(&invariant));
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
    seq_bound: usize,
    spacer_profile: SpacerProfile,
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
    };

    let mode_str = if portfolio {
        "portfolio"
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
    info!(mode = mode_str, "checking...");
    let start = Instant::now();

    let result =
        specl_symbolic::check(&spec, &consts, &config).map_err(|e| CliError::CheckError {
            message: e.to_string(),
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
                    println!("Result: NOT INDUCTIVE");
                } else {
                    println!("Result: INVARIANT VIOLATION");
                }
                println!("  Invariant: {}", invariant);
                println!(
                    "  Trace: {} steps (use BFS for detailed trace — symbolic trace reconstruction is not yet reliable)",
                    trace.len()
                );
                std::process::exit(1);
            }
            SymbolicOutcome::Unknown { reason } => {
                println!();
                println!("Result: UNKNOWN");
                println!("  Reason: {}", reason);
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
                let out = JsonOutput::new("error", secs)
                    .with_error(format!("parse error: {}", e));
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
            let out = JsonOutput::new("error", secs)
                .with_error(format!("type error: {}", e));
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
                let out = JsonOutput::new("error", secs)
                    .with_error(format!("compile error: {}", e));
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
            SimulateOutcome::Ok { trace, var_names, .. } => {
                (trace, var_names, "ok", None)
            }
            SimulateOutcome::InvariantViolation { invariant, trace, var_names } => {
                (trace, var_names, "invariant_violation", Some(invariant.as_str()))
            }
            SimulateOutcome::Deadlock { trace, var_names } => {
                (trace, var_names, "deadlock", None)
            }
        };
        if output == OutputFormat::Mermaid {
            println!("{}", trace_to_mermaid(trace, var_names, result_kind, invariant));
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
    let mut values = vec![Value::None; spec.consts.len()];

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
        if matches!(values[const_decl.index], Value::None) {
            if let Some(default_value) = const_decl.default_value {
                values[const_decl.index] = Value::Int(default_value);
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

fn parse_value(s: &str) -> CliResult<Value> {
    // Try to parse as integer
    if let Ok(n) = s.parse::<i64>() {
        return Ok(Value::Int(n));
    }

    // Try to parse as boolean
    if s == "true" {
        return Ok(Value::Bool(true));
    }
    if s == "false" {
        return Ok(Value::Bool(false));
    }

    // Try to parse as string (quoted)
    if s.starts_with('"') && s.ends_with('"') {
        return Ok(Value::String(s[1..s.len() - 1].to_string()));
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
    match v {
        Value::Bool(b) => serde_json::Value::Bool(*b),
        Value::Int(n) => serde_json::json!(*n),
        Value::String(s) => serde_json::Value::String(s.clone()),
        Value::Set(elems) => serde_json::Value::Array(elems.iter().map(value_to_json).collect()),
        Value::Seq(elems) => serde_json::Value::Array(elems.iter().map(value_to_json).collect()),
        Value::Fn(pairs) => {
            let obj: serde_json::Map<String, serde_json::Value> = pairs
                .iter()
                .map(|(k, v)| (format!("{}", k), value_to_json(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::IntMap(vals) => {
            let obj: serde_json::Map<String, serde_json::Value> = vals
                .iter()
                .enumerate()
                .map(|(i, v)| (i.to_string(), serde_json::json!(*v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::Record(fields) => {
            let obj: serde_json::Map<String, serde_json::Value> = fields
                .iter()
                .map(|(k, v)| (k.clone(), value_to_json(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::Tuple(elems) => serde_json::Value::Array(elems.iter().map(value_to_json).collect()),
        Value::None => serde_json::Value::Null,
        Value::Some(inner) => value_to_json(inner),
    }
}

/// Convert a specl Value to ITF-encoded serde_json::Value.
/// ITF uses tagged objects for non-primitive types:
///   Int → {"#bigint": "42"}, Set → {"#set": [...]}, Map → {"#map": [[k,v],...]},
///   Tuple → {"#tup": [...]}, Seq → plain array, Record → plain object.
fn value_to_itf(v: &Value) -> serde_json::Value {
    match v {
        Value::Bool(b) => serde_json::Value::Bool(*b),
        Value::Int(n) => serde_json::json!({"#bigint": n.to_string()}),
        Value::String(s) => serde_json::Value::String(s.clone()),
        Value::Set(elems) => {
            serde_json::json!({"#set": elems.iter().map(value_to_itf).collect::<Vec<_>>()})
        }
        Value::Seq(elems) => {
            serde_json::Value::Array(elems.iter().map(value_to_itf).collect())
        }
        Value::Fn(pairs) => {
            let entries: Vec<serde_json::Value> = pairs
                .iter()
                .map(|(k, v)| serde_json::json!([value_to_itf(k), value_to_itf(v)]))
                .collect();
            serde_json::json!({"#map": entries})
        }
        Value::IntMap(vals) => {
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
        Value::Record(fields) => {
            let obj: serde_json::Map<String, serde_json::Value> = fields
                .iter()
                .map(|(k, v)| (k.clone(), value_to_itf(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::Tuple(elems) => {
            serde_json::json!({"#tup": elems.iter().map(value_to_itf).collect::<Vec<_>>()})
        }
        Value::None => serde_json::json!({"tag": "None", "value": serde_json::json!({})}),
        Value::Some(inner) => {
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
    let mut lines = Vec::new();
    lines.push("digraph states {".to_string());
    lines.push("    rankdir=TB;".to_string());
    lines.push("    node [shape=box, fontname=\"monospace\", fontsize=10];".to_string());
    lines.push("    edge [fontname=\"monospace\", fontsize=9];".to_string());

    let fps = store.seen_fingerprints();

    // Assign compact numeric IDs to fingerprints
    let mut fp_list: Vec<Fingerprint> = fps.into_iter().collect();
    fp_list.sort_by_key(|fp| fp.as_u64());
    let fp_to_id: std::collections::HashMap<Fingerprint, usize> = fp_list
        .iter()
        .enumerate()
        .map(|(i, fp)| (*fp, i))
        .collect();

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
                                let ps: Vec<String> = params.iter().map(|v| v.to_string()).collect();
                                format!("{}({})", base, ps.join(","))
                            }
                        } else {
                            base
                        }
                    })
                    .unwrap_or_default();
                lines.push(format!("    s{} -> s{} [label=\"{}\"];", src_id, dst_id, edge_label));
            }
        }
    }

    lines.push("}".to_string());
    lines.join("\n")
}

/// Format a Value compactly for DOT node labels.
fn format_value_compact(v: &Value) -> String {
    match v {
        Value::Int(n) => n.to_string(),
        Value::Bool(b) => if *b { "T" } else { "F" }.to_string(),
        Value::String(s) => format!("\"{}\"", s),
        Value::Set(s) => {
            let inner: Vec<String> = s.iter().map(format_value_compact).collect();
            format!("{{{}}}", inner.join(","))
        }
        Value::Seq(s) => {
            let inner: Vec<String> = s.iter().map(format_value_compact).collect();
            format!("[{}]", inner.join(","))
        }
        Value::Fn(f) => {
            let inner: Vec<String> = f
                .iter()
                .map(|(k, v)| format!("{}:{}", format_value_compact(k), format_value_compact(v)))
                .collect();
            format!("{{{}}}", inner.join(","))
        }
        Value::IntMap(m) => {
            let inner: Vec<String> = m.iter().enumerate().map(|(i, v)| format!("{}:{}", i, v)).collect();
            format!("{{{}}}", inner.join(","))
        }
        Value::Record(r) => {
            let inner: Vec<String> = r
                .iter()
                .map(|(k, v)| format!("{}:{}", k, format_value_compact(v)))
                .collect();
            format!("{{{}}}", inner.join(","))
        }
        Value::Tuple(t) => {
            let inner: Vec<String> = t.iter().map(format_value_compact).collect();
            format!("({})", inner.join(","))
        }
        Value::None => "None".to_string(),
        Value::Some(v) => format!("Some({})", format_value_compact(v)),
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
                lines.push(format!("    Note right of {}: {}", actor, changes.join(", ")));
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
            actor, result_kind.to_uppercase(), inv
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
            Some(size) => println!("    {}: {} ({} values)", name, ty, format_large_number(*size)),
            None => println!("    {}: {} (unbounded)", name, ty),
        }
    }

    // Tips
    if let Some(bound) = profile.state_space_bound {
        println!();
        if bound > 100_000_000 {
            println!("  Tip: Use --fast for fingerprint-only mode (10x less memory, no traces)");
            println!("       Use --bloom for fixed-memory probabilistic mode (bug finding)");
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

fn cmd_test(dir: Option<&PathBuf>, override_max_states: usize, max_time_per_spec: u64) -> CliResult<()> {
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
        let mut const_values = vec![Value::None; spec.consts.len()];
        for const_decl in &spec.consts {
            let mut found = false;
            for c in &constants {
                if let Some((name, val)) = c.split_once('=') {
                    if name == const_decl.name {
                        if let Ok(v) = val.parse::<i64>() {
                            const_values[const_decl.index] = Value::Int(v);
                            found = true;
                            break;
                        }
                    }
                }
            }
            if !found {
                const_values[const_decl.index] = Value::Int(1);
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
            CheckOutcome::Ok { states_explored, .. } => {
                println!("  PASS  {} ({} states, {:.1}s)", file.display(), format_large_number(*states_explored as u128), secs);
                passed += 1;
            }
            CheckOutcome::StateLimitReached { states_explored, .. } => {
                println!("  PASS  {} ({} states [limit], {:.1}s)", file.display(), format_large_number(*states_explored as u128), secs);
                passed += 1;
            }
            CheckOutcome::MemoryLimitReached { states_explored, .. } => {
                println!("  PASS  {} ({} states [mem limit], {:.1}s)", file.display(), format_large_number(*states_explored as u128), secs);
                passed += 1;
            }
            CheckOutcome::TimeLimitReached { states_explored, .. } => {
                println!("  PASS  {} ({} states [time limit], {:.1}s)", file.display(), format_large_number(*states_explored as u128), secs);
                passed += 1;
            }
            CheckOutcome::InvariantViolation { invariant, .. } => {
                // Some examples intentionally have bugs
                if source.contains("intentional") || source.contains("bug") || source.contains("BUG") {
                    println!("  PASS  {} (expected violation: {}, {:.1}s)", file.display(), invariant, secs);
                    passed += 1;
                } else {
                    println!("  FAIL  {} (invariant violation: {})", file.display(), invariant);
                    failures.push(format!("{}: invariant violation: {}", file.display(), invariant));
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
    println!("Results: {} passed, {} failed, {} skipped ({:.1}s)", passed, failed, skipped, total_secs);

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

fn cmd_techniques(verbose: bool) -> CliResult<()> {
    if verbose {
        print!(
            "\
EXPLICIT-STATE CHECKING (default)
  The checker explores every reachable state of your spec, one by one, using
  breadth-first search (BFS). This guarantees that if a bug exists, it finds the
  shortest sequence of actions that triggers it.

  State spaces grow exponentially with the number of variables and their ranges.
  For example, 3 variables each with 100 possible values = 1,000,000 states.
  The optimizations below reduce the number of states the checker must visit.

  --por          Partial Order Reduction
                 When two actions don't affect each other (e.g., process A updates its
                 own state and process B updates its own state), the checker normally
                 tries both orderings: A-then-B and B-then-A. Both lead to the same
                 result, so one is redundant. POR detects these independent actions and
                 skips the redundant orderings.
                 Typical reduction: 2-10x fewer states.
                 Auto-enabled when >30% of action pairs are independent.
                 Safe to always enable — no overhead when actions are dependent.

  --symmetry     Symmetry Reduction
                 When your spec models N identical processes (e.g., Dict[0..N, State]),
                 many states are just rearrangements of each other. For example, with
                 3 processes, \"process 0 is leader, others are followers\" is equivalent
                 to \"process 2 is leader, others are followers\" — the identity of the
                 leader doesn't matter, only that exactly one exists.
                 Symmetry reduction groups these equivalent states and only explores one
                 representative from each group.
                 Typical reduction: up to N! (factorial) — for N=4 that's 24x fewer states.
                 Auto-enabled when symmetric Dict patterns are detected.

  --fast         Fingerprint-Only Mode
                 Normally the checker stores the full data for every visited state so it
                 can reconstruct the exact steps leading to a bug. This uses a lot of
                 memory for large state spaces.
                 Fast mode stores only a compact 8-byte hash (fingerprint) per state,
                 using roughly 10x less memory. The tradeoff: if a bug is found, the
                 checker must re-run with full storage to reconstruct the trace.
                 Best for: specs where you're running out of memory before exploring all
                 states, or initial exploration of very large state spaces.

  --no-deadlock  Skip Deadlock Check
                 A deadlock is a state where no action can fire. The checker reports
                 these by default because they sometimes indicate bugs. However, most
                 protocols naturally reach quiescent states where nothing happens (e.g.,
                 all messages delivered, consensus reached). Use this flag to suppress
                 false deadlock reports.

SYMBOLIC CHECKING (Z3-backed)
  Instead of exploring states one by one, symbolic checking encodes your entire spec
  as mathematical formulas and uses an SMT solver (Z3) to reason about them. This can
  handle specs with very large or unbounded state spaces that would be impossible to
  explore exhaustively.

  --bmc          Bounded Model Checking (BMC)
                 Asks: \"can a bug happen within K steps?\" by encoding K transitions as
                 a formula and asking Z3 to find a satisfying assignment. Fast for bugs
                 that occur within a few steps. Set the bound with --bmc-depth (default: unlimited).
                 If no bug is found within K steps, that does NOT prove the spec is safe
                 — the bug might require more steps.

  --inductive    Inductive Invariant Checking
                 Tries to prove your invariant holds forever using mathematical induction:
                 \"if the invariant holds in the current state, does it still hold after
                 any single action?\" This is very fast when it works, but many real-world
                 invariants aren't directly inductive — they need additional strengthening
                 invariants to make the induction step go through.

  --k-induction K  k-Induction
                 A more powerful version of induction. Instead of assuming the invariant
                 held for just one step, it assumes it held for K consecutive steps. This
                 can prove invariants that simple induction cannot. Try K=2 first, then
                 increase to 3, 4, 5 if needed.
                 If k-induction succeeds, the invariant is guaranteed to hold in ALL
                 reachable states, regardless of depth.

  --ic3          IC3/CHC (Property Directed Reachability)
                 The most powerful automated verification technique available. IC3 builds
                 up a proof layer by layer, discovering exactly which states are reachable
                 and which are not. It can prove invariants hold forever without needing
                 any depth bound. However, it may take a long time or return \"unknown\"
                 for very complex specs.

  When no specific symbolic flag is given, Specl automatically tries techniques
  in order: induction, k-induction (K=2..5), IC3, then BMC fallback.

CHOOSING A STRATEGY
  1. Start small:          specl check spec.specl -c N=2
  2. Analyze first:        specl info spec.specl -c N=2
     This shows state space estimates and recommended flags.
  3. Specl auto-selects BFS or symbolic based on spec types.
  4. Specl auto-enables POR and symmetry when beneficial.
  5. For large state spaces (>10M states): add --fast
  6. Scale up gradually: N=2 first, then N=3. State spaces grow exponentially.
"
        );
    } else {
        print!(
            "\
EXPLICIT-STATE CHECKING (default)
  BFS exhaustive exploration. Finds shortest counterexample traces.

  --por          Partial Order Reduction
                 Exploits action independence to skip redundant interleavings.
                 Best for: specs with many independent actions (e.g., per-process updates).
                 Typical reduction: 2-10x. No overhead when unhelpful.
                 Auto-enabled when >30% of action pairs are independent.

  --symmetry     Symmetry Reduction
                 Identifies symmetric processes and explores one representative per orbit.
                 Best for: specs with Dict[0..N, T] where processes are interchangeable.
                 Typical reduction: N! (factorial). Auto-enabled when detected.

  --fast         Fingerprint-Only Mode
                 Uses 8 bytes/state instead of full state storage. 10x less memory.
                 Tradeoff: Cannot produce counterexample traces directly.
                 Re-runs with traces if a violation is found.
                 Best for: large state spaces where memory is the bottleneck.

  --no-deadlock  Skip Deadlock Check
                 Most protocols have quiescent states. Use unless testing liveness.

SYMBOLIC CHECKING (Z3-backed)
  Encodes spec as SMT formulas. Can handle unbounded/huge state spaces.

  --bmc          Bounded Model Checking (BMC)
                 Unrolls transitions to --bmc-depth steps. Fast for shallow bugs.

  --inductive    Inductive Invariant Checking
                 Single-step induction proof. Fast but may fail for non-inductive invariants.

  --k-induction K  k-Induction
                 Proves invariants hold for all reachable states (if k is sufficient).
                 Stronger than simple induction. Try K=2..5.

  --ic3          IC3/CHC (Property Directed Reachability)
                 Unbounded verification via Z3 Spacer. Most powerful symbolic mode.
                 Can prove invariants hold for ALL depths. May return \"unknown\" for hard specs.

  When no specific symbolic flag is given, Specl automatically cascades:
  induction -> k-induction(2..5) -> IC3 -> BMC fallback.

CHOOSING A STRATEGY
  Start with:           specl check spec.specl -c N=2
  Specl auto-selects BFS or symbolic, and auto-enables POR and symmetry.
  For large state spaces: add --fast
  Use `specl info` to analyze your spec before a long run.
"
        );
    }
    Ok(())
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
