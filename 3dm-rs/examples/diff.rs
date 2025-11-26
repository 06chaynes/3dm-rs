//! Example: Generate diff between two XML documents
//!
//! This example demonstrates how to generate a diff between a base document
//! and a modified version.
//!
//! Usage: cargo run --example diff <base.xml> <modified.xml>

use std::env;
use std::io;
use xml_3dm::{BaseNodeFactory, BranchNodeFactory, Diff, DiffMatching, Matching, XmlParser};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    if args.len() != 3 {
        eprintln!("Usage: {} <base.xml> <modified.xml>", args[0]);
        std::process::exit(1);
    }

    let base_file = &args[1];
    let modified_file = &args[2];

    // Parse base and modified versions
    let base_parser = XmlParser::new(BaseNodeFactory);
    let branch_parser = XmlParser::new(BranchNodeFactory);

    eprintln!("Parsing base: {}", base_file);
    let base = base_parser.parse_file(base_file)?;

    eprintln!("Parsing modified: {}", modified_file);
    let branch = branch_parser.parse_file(modified_file)?;

    // Build matching optimized for diff
    eprintln!("Building matching...");
    let mut matching = DiffMatching::new();
    matching.build_matching(&base, &branch);

    // Generate diff
    eprintln!("Generating diff...");
    if let Some(diff) = Diff::new(&matching) {
        diff.diff(&mut io::stdout())?;
        eprintln!("\nDiff generated successfully!");
    } else {
        eprintln!("Failed to create diff (no root node found)");
        std::process::exit(1);
    }

    Ok(())
}
