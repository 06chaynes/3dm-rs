//! 3DM XML Tree Differencing and Merging Tool CLI
//!
//! This is a Rust port of the original Java 3DM tool by Tancred Lindholm.

use std::fs::File;
use std::io::{self, BufWriter, Write};

use clap::{Parser, Subcommand};
use xml_3dm::{
    BaseNodeFactory, BranchNodeFactory, Diff, DiffMatching, Matching, Merge, Patch, TriMatching,
    XmlParser,
};

/// 3DM XML Tree Differencing and Merging Tool
#[derive(Parser)]
#[command(name = "tdm")]
#[command(version)]
#[command(about = "3DM XML Tree Differencing and Merging Tool", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Merge two branches relative to a common base
    #[command(visible_alias = "m")]
    Merge {
        /// Base file (common ancestor)
        base: String,
        /// First branch file
        branch1: String,
        /// Second branch file
        branch2: String,
        /// Output file (default: stdout)
        output: Option<String>,

        /// Threshold for considering duplicate structure as a copy (bytes)
        #[arg(short = 'c', long, default_value = "128")]
        copythreshold: usize,
    },

    /// Generate a diff between base and branch
    #[command(visible_alias = "d")]
    Diff {
        /// Base file
        base: String,
        /// Branch file
        branch: String,
        /// Output file (default: stdout)
        output: Option<String>,
    },

    /// Apply a patch to a base file
    #[command(visible_alias = "p")]
    Patch {
        /// Base file
        base: String,
        /// Patch file (diff XML)
        patchfile: String,
        /// Output file (default: stdout)
        output: Option<String>,
    },
}

fn main() -> std::process::ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Merge {
            base,
            branch1,
            branch2,
            output,
            copythreshold,
        } => run_merge(&base, &branch1, &branch2, output.as_deref(), copythreshold),
        Commands::Diff {
            base,
            branch,
            output,
        } => run_diff(&base, &branch, output.as_deref()),
        Commands::Patch {
            base,
            patchfile,
            output,
        } => run_patch(&base, &patchfile, output.as_deref()),
    };

    match result {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("Error: {}", e);
            std::process::ExitCode::FAILURE
        }
    }
}

/// Runs the 3-way merge algorithm.
fn run_merge(
    base_path: &str,
    branch1_path: &str,
    branch2_path: &str,
    output_path: Option<&str>,
    copy_threshold: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    // Parse input files
    let base_parser = XmlParser::new(BaseNodeFactory);
    let branch_parser = XmlParser::new(BranchNodeFactory);

    eprintln!("Parsing base: {}", base_path);
    let doc_base = base_parser.parse_file(base_path)?;

    eprintln!("Parsing branch1: {}", branch1_path);
    let doc_a = branch_parser.parse_file(branch1_path)?;

    eprintln!("Parsing branch2: {}", branch2_path);
    let doc_b = branch_parser.parse_file(branch2_path)?;

    // Build tri-matching (handles matching internally)
    eprintln!(
        "Building matchings and merging (copy threshold: {})...",
        copy_threshold
    );
    let tri_matching =
        TriMatching::with_copy_threshold(doc_a, doc_base, doc_b, copy_threshold as i32);

    // Run merge
    let mut merge = Merge::new(tri_matching);

    // Get output writer
    let mut output: Box<dyn Write> = match output_path {
        Some(path) => Box::new(BufWriter::new(File::create(path)?)),
        None => Box::new(io::stdout()),
    };

    merge.merge(&mut output)?;

    // Report conflicts if any
    let num_conflicts = merge.conflict_log.conflicts().len();
    let num_warnings = merge.conflict_log.warnings().len();
    if num_conflicts > 0 || num_warnings > 0 {
        eprintln!(
            "Merge complete with {} conflicts and {} warnings.",
            num_conflicts, num_warnings
        );
    } else {
        eprintln!("Merge complete.");
    }

    Ok(())
}

/// Runs the diff algorithm.
fn run_diff(
    base_path: &str,
    branch_path: &str,
    output_path: Option<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Parse input files
    let base_parser = XmlParser::new(BaseNodeFactory);
    let branch_parser = XmlParser::new(BranchNodeFactory);

    eprintln!("Parsing base: {}", base_path);
    let doc_base = base_parser.parse_file(base_path)?;

    eprintln!("Parsing branch: {}", branch_path);
    let doc_branch = branch_parser.parse_file(branch_path)?;

    // Build matching
    eprintln!("Building matching...");
    let mut matching = DiffMatching::new();
    matching.build_matching(&doc_base, &doc_branch);

    // Generate diff
    eprintln!("Generating diff...");
    let diff = Diff::new(&matching).ok_or("Failed to create diff - no base root")?;

    // Get output writer
    let mut output: Box<dyn Write> = match output_path {
        Some(path) => Box::new(BufWriter::new(File::create(path)?)),
        None => Box::new(io::stdout()),
    };

    diff.diff(&mut output)?;

    eprintln!("Diff complete.");
    Ok(())
}

/// Runs the patch algorithm.
fn run_patch(
    base_path: &str,
    patch_path: &str,
    output_path: Option<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Parse input files - use base parser for both since patch is structural
    let base_parser = XmlParser::new(BaseNodeFactory);

    eprintln!("Parsing base: {}", base_path);
    let doc_base = base_parser.parse_file(base_path)?;

    eprintln!("Parsing patch: {}", patch_path);
    let doc_patch = base_parser.parse_file(patch_path)?;

    // Apply patch
    eprintln!("Applying patch...");
    let patch = Patch::new();

    // Get output writer
    let mut output: Box<dyn Write> = match output_path {
        Some(path) => Box::new(BufWriter::new(File::create(path)?)),
        None => Box::new(io::stdout()),
    };

    patch.patch(&doc_base, &doc_patch, &mut output)?;

    eprintln!("Patch complete.");
    Ok(())
}
