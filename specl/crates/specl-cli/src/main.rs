//! Command-line interface for Specl model checker.

use clap::{Parser, Subcommand};
use miette::{Diagnostic, NamedSource, SourceSpan};
use notify::{RecursiveMode, Watcher};
use specl_eval::Value;
use specl_ir::compile;
use specl_mc::{CheckConfig, CheckOutcome, Explorer, State};
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

    /// Model check a Specl file
    Check {
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

        /// Maximum memory usage in MB (0 = unlimited)
        #[arg(long, default_value = "0")]
        memory_limit: usize,

        /// Disable deadlock checking
        #[arg(long)]
        no_deadlock: bool,

        /// Disable parallel exploration
        #[arg(long)]
        no_parallel: bool,

        /// Number of threads for parallel exploration (0 = use all available)
        #[arg(long, default_value = "0")]
        threads: usize,

        /// Enable partial order reduction
        #[arg(long)]
        por: bool,

        /// Enable symmetry reduction
        #[arg(long)]
        symmetry: bool,

        /// Fast check mode: minimal memory, re-explore for traces on violation
        #[arg(long)]
        fast: bool,

        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
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
            verbose,
        } => cmd_check(
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
        ),
        Commands::Format { file, write } => cmd_format(&file, write),
        Commands::Watch {
            file,
            constant,
            max_states,
            max_depth,
            no_deadlock,
        } => cmd_watch(&file, &constant, max_states, max_depth, !no_deadlock),
        Commands::Translate { file, output } => cmd_translate(&file, output.as_ref()),
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

    let config = CheckConfig {
        check_deadlock,
        max_states,
        max_depth,
        memory_limit_mb,
        parallel,
        num_threads,
        use_por,
        use_symmetry,
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
            println!("  States explored: {}", states_explored);
            println!("  Max depth: {}", max_depth);
            println!("  Time: {:.2}s", elapsed.as_secs_f64());
            println!(
                "  States/sec: {:.0}",
                states_explored as f64 / elapsed.as_secs_f64()
            );
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
    for const_decl in &spec.consts {
        if matches!(values[const_decl.index], Value::None) {
            if let Some(default_value) = const_decl.default_value {
                // Scalar constant - use the default value
                values[const_decl.index] = Value::Int(default_value);
            } else {
                // Type-constrained constant - must be provided
                return Err(CliError::Other {
                    message: format!(
                        "constant '{}' not provided (use -c {}=VALUE)",
                        const_decl.name, const_decl.name
                    ),
                });
            }
        }
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
