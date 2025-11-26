//! Example: 3-way merge of XML documents
//!
//! This example demonstrates how to perform a 3-way merge on XML documents.
//! It takes three XML files (base, left branch, right branch) and merges them.
//!
//! Usage: cargo run --example merge <base.xml> <branch1.xml> <branch2.xml>

use std::env;
use std::io;
use xml_3dm::{BaseNodeFactory, BranchNodeFactory, Merge, TriMatching, XmlParser};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    if args.len() != 4 {
        eprintln!("Usage: {} <base.xml> <branch1.xml> <branch2.xml>", args[0]);
        std::process::exit(1);
    }

    let base_file = &args[1];
    let branch1_file = &args[2];
    let branch2_file = &args[3];

    // Parse the three XML files
    let base_parser = XmlParser::new(BaseNodeFactory);
    let branch_parser = XmlParser::new(BranchNodeFactory);

    eprintln!("Parsing base: {}", base_file);
    let base = base_parser.parse_file(base_file)?;

    eprintln!("Parsing branch 1: {}", branch1_file);
    let branch1 = branch_parser.parse_file(branch1_file)?;

    eprintln!("Parsing branch 2: {}", branch2_file);
    let branch2 = branch_parser.parse_file(branch2_file)?;

    // Build matching between the three trees
    eprintln!("Building matching...");
    let matching = TriMatching::new(branch1, base, branch2);

    // Perform the merge
    eprintln!("Merging...");
    let mut merger = Merge::new(matching);
    merger.merge(&mut io::stdout())?;

    // Report conflicts if any
    if merger.conflict_log.has_conflicts() {
        eprintln!("\nConflicts detected:");
        for conflict in merger.conflict_log.conflicts() {
            eprintln!("  {:?}", conflict);
        }
        std::process::exit(2);
    }

    if !merger.conflict_log.warnings().is_empty() {
        eprintln!("\nWarnings:");
        for warning in merger.conflict_log.warnings() {
            eprintln!("  {:?}", warning);
        }
    }

    eprintln!("\nMerge completed successfully!");
    Ok(())
}
