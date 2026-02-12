//! Command-line interface for Specl model checker.

use clap::{Parser, Subcommand};
use miette::{Diagnostic, NamedSource, SourceSpan};
use notify::{RecursiveMode, Watcher};
use specl_eval::Value;
use specl_ir::analyze::analyze;
use specl_ir::compile;
use specl_mc::{CheckConfig, CheckOutcome, Explorer, State};
use specl_symbolic::{SymbolicConfig, SymbolicMode, SymbolicOutcome};
use specl_syntax::{parse, pretty_print};
use std::fs;
use std::path::PathBuf;
use std::sync::mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};
use thiserror::Error;
use tracing::info;
use tracing_subscriber::EnvFilter;

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

        // -- Symbolic (Z3) options --
        /// Bounded model checking (unroll transitions to --depth steps)
        #[arg(long, help_heading = "Symbolic (Z3)")]
        symbolic: bool,

        /// BMC/symbolic depth bound
        #[arg(long, default_value = "10", help_heading = "Symbolic (Z3)")]
        depth: usize,

        /// Inductive invariant checking (single-step proof)
        #[arg(long, help_heading = "Symbolic (Z3)")]
        inductive: bool,

        /// k-induction with given strengthening depth
        #[arg(long, value_name = "K", help_heading = "Symbolic (Z3)")]
        k_induction: Option<usize>,

        /// IC3/CHC unbounded verification via Z3 Spacer
        #[arg(long, help_heading = "Symbolic (Z3)")]
        ic3: bool,

        /// Auto cascade: induction -> k-induction -> IC3 -> BMC
        #[arg(long, help_heading = "Symbolic (Z3)")]
        smart: bool,

        /// Max sequence length for symbolic Seq[T] encoding
        #[arg(long, default_value = "5", help_heading = "Symbolic (Z3)")]
        seq_bound: usize,

        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,

        /// Suppress spec analysis and recommendations
        #[arg(short, long)]
        quiet: bool,

        /// Disable auto-enabling of optimizations (POR, symmetry)
        #[arg(long)]
        no_auto: bool,
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

    /// Show reference of all available checking techniques and when to use them
    Techniques {
        /// Show extended plain-English explanations for each technique
        #[arg(short, long)]
        verbose: bool,
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
    } else {
        EnvFilter::new("info")
    };

    tracing_subscriber::fmt()
        .with_env_filter(filter)
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
            max_states,
            max_depth,
            memory_limit,
            no_deadlock,
            no_parallel,
            threads,
            por,
            symmetry,
            fast,
            symbolic,
            depth,
            inductive,
            k_induction,
            ic3,
            smart,
            seq_bound,
            verbose,
            quiet,
            no_auto,
        } => {
            if symbolic || inductive || k_induction.is_some() || ic3 || smart {
                cmd_check_symbolic(
                    &file,
                    &constant,
                    depth,
                    inductive,
                    k_induction,
                    ic3,
                    smart,
                    seq_bound,
                )
            } else {
                cmd_check(
                    &file,
                    &constant,
                    max_states,
                    max_depth,
                    memory_limit,
                    !no_deadlock,
                    !no_parallel,
                    threads,
                    por,
                    symmetry,
                    fast,
                    verbose,
                    quiet,
                    no_auto,
                )
            }
        }
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

    // Estimated check time
    if let Some(bound) = total_bound {
        if bound > 0 {
            let throughput = 100_000.0_f64; // ~100K states/s typical
            let secs = bound as f64 / throughput;
            let time_str = if secs < 1.0 {
                "<1 second".to_string()
            } else if secs < 60.0 {
                format!("~{:.0} seconds", secs)
            } else if secs < 3600.0 {
                format!("~{:.0} minutes", secs / 60.0)
            } else if secs < 86400.0 {
                format!("~{:.1} hours", secs / 3600.0)
            } else {
                format!("~{:.1} days", secs / 86400.0)
            };
            println!();
            println!("Estimated check time: {} (at ~100K states/s)", time_str);
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
                flags.push("--smart".to_string());
            }
        }
    }
    println!("Suggested: specl check {} {}", filename, flags.join(" "));

    println!();
    Ok(())
}

fn cmd_check(
    file: &PathBuf,
    constants: &[String],
    max_states: usize,
    max_depth: usize,
    memory_limit_mb: usize,
    check_deadlock: bool,
    parallel: bool,
    num_threads: usize,
    use_por: bool,
    use_symmetry: bool,
    fast_check: bool,
    _verbose: bool,
    quiet: bool,
    no_auto: bool,
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

    // Parse constants
    let consts = parse_constants(constants, &spec)?;

    // Spec analysis, recommendations, and auto-enable
    let profile = analyze(&spec);
    if !quiet {
        print_profile(&profile, use_por, use_symmetry);
    }

    // Reject unbounded types for explicit-state checking
    let unbounded_warnings: Vec<_> = profile
        .warnings
        .iter()
        .filter(|w| matches!(w, specl_ir::analyze::Warning::UnboundedType { .. }))
        .collect();
    if !unbounded_warnings.is_empty() {
        let lines: Vec<String> = unbounded_warnings
            .iter()
            .map(|w| format!("  {}", w))
            .collect();
        return Err(CliError::Other {
            message: format!(
                "explicit-state checking requires finite domains\n\n{}\n\n\
                 Fix: {}\n\
                 For unbounded types, use symbolic checking: --smart",
                lines.join("\n"),
                unbounded_warnings[0].fix_hint()
            ),
        });
    }

    let mut actual_por = use_por;
    let mut actual_symmetry = use_symmetry;

    if !no_auto {
        if !use_por && profile.independence_ratio > 0.3 {
            actual_por = true;
            if !quiet {
                let pct = (profile.independence_ratio * 100.0) as u32;
                println!("Auto-enabled: --por ({}% independent actions)", pct);
            }
        }
        if !use_symmetry && profile.has_symmetry {
            actual_symmetry = true;
            if !quiet {
                let sizes: Vec<String> = profile
                    .symmetry_domain_sizes
                    .iter()
                    .map(|s| s.to_string())
                    .collect();
                println!(
                    "Auto-enabled: --symmetry (symmetric domains: {})",
                    sizes.join(", ")
                );
            }
        }
        if !quiet && (actual_por != use_por || actual_symmetry != use_symmetry) {
            println!();
        }
    }

    let config = CheckConfig {
        check_deadlock,
        max_states,
        max_depth,
        memory_limit_mb,
        parallel,
        num_threads,
        use_por: actual_por,
        use_symmetry: actual_symmetry,
        fast_check,
    };

    // Extract variable names for trace formatting before moving spec
    let var_names: Vec<String> = spec.vars.iter().map(|v| v.name.clone()).collect();

    info!("model checking...");
    let start = Instant::now();

    let mut explorer = Explorer::new(spec, consts, config);
    let result = explorer.check().map_err(|e| CliError::CheckError {
        message: e.to_string(),
    })?;

    let elapsed = start.elapsed();

    match result {
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
            let secs = elapsed.as_secs_f64();
            println!("  Time: {:.1}s", secs);
            if secs > 0.001 {
                println!(
                    "  Throughput: {} states/s",
                    format_large_number((states_explored as f64 / secs) as u128)
                );
            }
            // Show active optimizations
            let mut opts = Vec::new();
            if actual_por {
                opts.push("POR");
            }
            if actual_symmetry {
                opts.push("symmetry");
            }
            if fast_check {
                opts.push("fast");
            }
            if !opts.is_empty() {
                println!("  Optimizations: {}", opts.join(", "));
            }
        }
        CheckOutcome::InvariantViolation { invariant, trace } => {
            println!();
            println!("Result: INVARIANT VIOLATION");
            println!("  Invariant: {}", invariant);
            println!("  Trace ({} steps):", trace.len());
            for (i, (state, action)) in trace.iter().enumerate() {
                let action_str = action.as_deref().unwrap_or("init");
                let state_str = format_state_with_names(state, &var_names);
                println!("    {}: {} -> {}", i, action_str, state_str);
            }
            std::process::exit(1);
        }
        CheckOutcome::Deadlock { trace } => {
            println!();
            println!("Result: DEADLOCK");
            println!("  Trace ({} steps):", trace.len());
            for (i, (state, action)) in trace.iter().enumerate() {
                let action_str = action.as_deref().unwrap_or("init");
                let state_str = format_state_with_names(state, &var_names);
                println!("    {}: {} -> {}", i, action_str, state_str);
            }
            std::process::exit(1);
        }
        CheckOutcome::StateLimitReached {
            states_explored,
            max_depth,
        } => {
            println!();
            println!("Result: STATE LIMIT REACHED");
            println!("  States explored: {}", states_explored);
            println!("  Max depth: {}", max_depth);
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
            std::process::exit(2);
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
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
            std::process::exit(2);
        }
    }

    Ok(())
}

fn cmd_check_symbolic(
    file: &PathBuf,
    constants: &[String],
    depth: usize,
    inductive: bool,
    k_induction: Option<usize>,
    ic3: bool,
    smart: bool,
    seq_bound: usize,
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
        mode: if smart {
            SymbolicMode::Smart
        } else if ic3 {
            SymbolicMode::Ic3
        } else if let Some(k) = k_induction {
            SymbolicMode::KInduction(k)
        } else if inductive {
            SymbolicMode::Inductive
        } else {
            SymbolicMode::Bmc
        },
        depth,
        seq_bound,
    };

    let mode_str = if smart {
        "smart"
    } else if ic3 {
        "IC3"
    } else if k_induction.is_some() {
        "k-induction"
    } else if inductive {
        "inductive"
    } else {
        "symbolic BMC"
    };
    info!(mode = mode_str, "checking...");
    let start = Instant::now();

    let result =
        specl_symbolic::check(&spec, &consts, &config).map_err(|e| CliError::CheckError {
            message: e.to_string(),
        })?;

    let elapsed = start.elapsed();

    match result {
        SymbolicOutcome::Ok { method } => {
            println!();
            println!("Result: OK");
            println!("  Method: {}", method);
            if let Some(k) = k_induction {
                println!("  K: {}", k);
            } else if !inductive && !ic3 {
                println!("  Depth: {}", depth);
            }
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
        }
        SymbolicOutcome::InvariantViolation { invariant, trace } => {
            println!();
            if inductive {
                println!("Result: NOT INDUCTIVE");
            } else {
                println!("Result: INVARIANT VIOLATION");
            }
            println!("  Invariant: {}", invariant);
            println!("  Trace ({} steps):", trace.len());
            for (i, step) in trace.iter().enumerate() {
                let action_str = step.action.as_deref().unwrap_or("init");
                let state_str = step
                    .state
                    .iter()
                    .map(|(k, v)| format!("{}={}", k, v))
                    .collect::<Vec<_>>()
                    .join(", ");
                println!("    {}: {} -> {}", i, action_str, state_str);
            }
            std::process::exit(1);
        }
        SymbolicOutcome::Unknown { reason } => {
            println!();
            println!("Result: UNKNOWN");
            println!("  Reason: {}", reason);
            std::process::exit(2);
        }
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

fn format_large_number(n: u128) -> String {
    if n >= 1_000_000_000_000 {
        format!("{:.1}T", n as f64 / 1e12)
    } else if n >= 1_000_000_000 {
        format!("{:.1}B", n as f64 / 1e9)
    } else if n >= 1_000_000 {
        format!("{:.1}M", n as f64 / 1e6)
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
        eprintln!("Error: explicit-state checking requires finite domains");
        for w in &unbounded_warnings {
            eprintln!("  {}", w);
        }
        eprintln!("Fix: {}", unbounded_warnings[0].fix_hint());
        return;
    }

    let config = CheckConfig {
        check_deadlock,
        max_states,
        max_depth,
        ..Default::default()
    };

    let start = Instant::now();
    let mut explorer = Explorer::new(spec, consts, config);
    let result = match explorer.check() {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Check error: {}", e);
            return;
        }
    };

    let elapsed = start.elapsed();

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
    }

    println!();
    println!("Watching for changes...");
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

  --symbolic     Bounded Model Checking (BMC)
                 Asks: \"can a bug happen within K steps?\" by encoding K transitions as
                 a formula and asking Z3 to find a satisfying assignment. Fast for bugs
                 that occur within a few steps. Set the bound with --depth (default 10).
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

  --smart        Automatic Cascade
                 Tries verification techniques in order from fastest to most powerful:
                 induction, then k-induction (K=2..5), then IC3, falling back to BMC if
                 nothing else works. This is the recommended default for symbolic checking
                 — it will use the simplest technique that succeeds.

CHOOSING A STRATEGY
  1. Start small:          specl check spec.specl -c N=2
  2. Analyze first:        specl info spec.specl -c N=2
     This shows state space estimates and recommended flags.
  3. Specl auto-enables POR and symmetry when beneficial.
  4. For large state spaces (>10M states): add --fast
  5. For unbounded types (Int, Nat): use --smart for symbolic checking
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

  --symbolic     Bounded Model Checking (BMC)
                 Unrolls transitions to --depth steps. Fast for shallow bugs.

  --inductive    Inductive Invariant Checking
                 Single-step induction proof. Fast but may fail for non-inductive invariants.

  --k-induction K  k-Induction
                 Proves invariants hold for all reachable states (if k is sufficient).
                 Stronger than simple induction. Try K=2..5.

  --ic3          IC3/CHC (Property Directed Reachability)
                 Unbounded verification via Z3 Spacer. Most powerful symbolic mode.
                 Can prove invariants hold for ALL depths. May return \"unknown\" for hard specs.

  --smart        Automatic Cascade
                 Tries: induction -> k-induction(2..5) -> IC3 -> BMC fallback.
                 Best default for symbolic checking.

CHOOSING A STRATEGY
  Start with:           specl check spec.specl -c N=2
  Specl auto-enables POR and symmetry when beneficial.
  For large state spaces: add --fast
  For unbounded specs:    use --smart
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
