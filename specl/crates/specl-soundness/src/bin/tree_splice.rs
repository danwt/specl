use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use tree_sitter::{Node, Parser};

#[derive(Debug)]
struct Args {
    seed_dirs: Vec<PathBuf>,
    out_dir: PathBuf,
    count: usize,
    seed: u64,
    max_bytes: usize,
}

fn parse_args() -> Result<Args, String> {
    let mut seed_dirs = Vec::new();
    let mut out_dir = None;
    let mut count: usize = 100;
    let mut seed: u64 = 7;
    let mut max_bytes: usize = 1200;

    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--seed-dir" => {
                let value = args.next().ok_or("--seed-dir needs a path")?;
                seed_dirs.push(PathBuf::from(value));
            }
            "--out-dir" => {
                let value = args.next().ok_or("--out-dir needs a path")?;
                out_dir = Some(PathBuf::from(value));
            }
            "--count" => {
                let value = args.next().ok_or("--count needs a number")?;
                count = value.parse().map_err(|_| "invalid --count value")?;
            }
            "--seed" => {
                let value = args.next().ok_or("--seed needs a number")?;
                seed = value.parse().map_err(|_| "invalid --seed value")?;
            }
            "--max-bytes" => {
                let value = args.next().ok_or("--max-bytes needs a number")?;
                max_bytes = value.parse().map_err(|_| "invalid --max-bytes value")?;
            }
            "--help" | "-h" => {
                return Err(help());
            }
            other => {
                return Err(format!("unknown flag: {other}\n{}", help()));
            }
        }
    }

    if seed_dirs.is_empty() {
        return Err(format!("at least one --seed-dir is required\n{}", help()));
    }
    let out_dir = out_dir.ok_or_else(|| format!("--out-dir is required\n{}", help()))?;

    Ok(Args {
        seed_dirs,
        out_dir,
        count,
        seed,
        max_bytes,
    })
}

fn help() -> String {
    "\
Usage:
  tree_splice --seed-dir <DIR> [--seed-dir <DIR> ...] --out-dir <DIR> [--count N] [--seed N] [--max-bytes N]

Description:
  Parse TLA+ files with tree-sitter-tlaplus and generate spliced modules by replacing
  one subtree from a base file with a subtree from a donor file.
"
    .to_string()
}

fn find_tla_files(root: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = fs::read_dir(root) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                find_tla_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "tla") {
                out.push(path);
            }
        }
    }
}

fn collect_candidate_ranges(node: Node<'_>, text_len: usize, out: &mut Vec<(usize, usize)>) {
    if node.child_count() > 0 {
        let start = node.start_byte();
        let end = node.end_byte();
        if start < end
            && end <= text_len
            && end - start >= 8
            && end - start <= 1200
            && node.kind() != "source_file"
        {
            out.push((start, end));
        }
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            collect_candidate_ranges(child, text_len, out);
        }
    }
}

fn splice_one(
    rng: &mut StdRng,
    parser: &mut Parser,
    base_text: &str,
    donor_text: &str,
    max_bytes: usize,
) -> Option<String> {
    let base_tree = parser.parse(base_text, None)?;
    let donor_tree = parser.parse(donor_text, None)?;
    let mut base_ranges = Vec::new();
    let mut donor_ranges = Vec::new();
    collect_candidate_ranges(base_tree.root_node(), base_text.len(), &mut base_ranges);
    collect_candidate_ranges(donor_tree.root_node(), donor_text.len(), &mut donor_ranges);
    if base_ranges.is_empty() || donor_ranges.is_empty() {
        return None;
    }

    for _ in 0..40 {
        let (b0, b1) = base_ranges[rng.gen_range(0..base_ranges.len())];
        let (d0, d1) = donor_ranges[rng.gen_range(0..donor_ranges.len())];
        let donor_piece = &donor_text[d0..d1];
        let mut out = String::with_capacity(base_text.len() + donor_piece.len());
        out.push_str(&base_text[..b0]);
        out.push_str(donor_piece);
        out.push_str(&base_text[b1..]);
        if out.len() <= max_bytes {
            return Some(out);
        }
    }
    None
}

fn main() -> Result<(), String> {
    let args = parse_args()?;
    fs::create_dir_all(&args.out_dir).map_err(|e| e.to_string())?;

    let mut files = Vec::new();
    for dir in &args.seed_dirs {
        find_tla_files(dir, &mut files);
    }
    files.sort();
    files.dedup();
    if files.len() < 2 {
        return Err("need at least two .tla files across seed dirs".to_string());
    }

    let mut parser = Parser::new();
    let language = tree_sitter_tlaplus::LANGUAGE;
    parser
        .set_language(&language.into())
        .map_err(|e| format!("failed to set tree-sitter language: {e}"))?;

    let mut rng = StdRng::seed_from_u64(args.seed);
    let mut generated = 0usize;
    let mut attempts = 0usize;

    while generated < args.count && attempts < args.count * 30 {
        attempts += 1;
        let base_idx = rng.gen_range(0..files.len());
        let mut donor_idx = rng.gen_range(0..files.len());
        if donor_idx == base_idx {
            donor_idx = (donor_idx + 1) % files.len();
        }

        let base_text = match fs::read_to_string(&files[base_idx]) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let donor_text = match fs::read_to_string(&files[donor_idx]) {
            Ok(s) => s,
            Err(_) => continue,
        };

        if let Some(spliced) = splice_one(
            &mut rng,
            &mut parser,
            &base_text,
            &donor_text,
            args.max_bytes,
        ) {
            let out_path = args.out_dir.join(format!("splice_{generated:05}.tla"));
            if fs::write(&out_path, spliced).is_ok() {
                generated += 1;
            }
        }
    }

    println!(
        "generated={} attempts={} seeds={}",
        generated,
        attempts,
        files.len()
    );
    if generated < args.count {
        return Err(format!(
            "generated only {} files out of requested {}",
            generated, args.count
        ));
    }
    Ok(())
}
