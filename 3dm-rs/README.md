# xml-3dm

A Rust implementation of the 3DM (3-way Diff/Merge) algorithm for structure-aware XML differencing and merging.

## Overview

`xml-3dm` is a library for performing 3-way merges on XML documents. The library operates on XML tree structure and handles the following scenarios:

- Merging changes when one branch moves content and another edits it
- Detecting and preserving copy operations across the tree
- Resolving conflicts at the element and attribute level
- Generating compact diff representations with copy detection

This is a Rust port of the original [3DM tool](https://www.cs.hut.fi/~ctl/3dm/) created by Tancred Lindholm as part of his Master's thesis at Helsinki University of Technology.

## Features

- **Structure-aware merging**: Understands XML tree structure, not just text lines
- **Heuristic matching**: Uses Q-gram distance and tree structure to match corresponding nodes
- **Copy detection**: Identifies copied subtrees and encodes them efficiently
- **Conflict resolution**: Provides detailed conflict and warning logs
- **Full XML support**: Handles elements, attributes, text nodes, and mixed content

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
xml-3dm = "0.1"
```

## Usage

### 3-Way Merge

```rust
use xml_3dm::{parse_file, BaseNodeFactory, BranchNodeFactory, XmlParser, Merge, TriMatching};
use std::io;

// Parse the three XML files
let base_parser = XmlParser::new(BaseNodeFactory);
let branch_parser = XmlParser::new(BranchNodeFactory);

let base = base_parser.parse_file("base.xml")?;
let left = branch_parser.parse_file("branch1.xml")?;
let right = branch_parser.parse_file("branch2.xml")?;

// Build matching between the three trees
let matching = TriMatching::new(left, base, right);

// Perform the merge
let mut merger = Merge::new(matching);
merger.merge(&mut io::stdout())?;

// Check for conflicts
if merger.conflict_log.has_conflicts() {
    eprintln!("Conflicts detected:");
    for conflict in merger.conflict_log.conflicts() {
        eprintln!("  {}", conflict);
    }
}
```

### Diff Generation

```rust
use xml_3dm::{parse_file, BaseNodeFactory, BranchNodeFactory, XmlParser, Diff, DiffMatching};
use std::io;

// Parse base and modified versions
let base_parser = XmlParser::new(BaseNodeFactory);
let branch_parser = XmlParser::new(BranchNodeFactory);

let base = base_parser.parse_file("base.xml")?;
let branch = branch_parser.parse_file("modified.xml")?;

// Build matching optimized for diff
let matching = DiffMatching::new(base, branch);

// Generate diff
if let Some(diff) = Diff::new(&matching) {
    diff.diff(&mut io::stdout())?;
}
```

### Patch Application

```rust
use xml_3dm::{parse_file, BaseNodeFactory, XmlParser, Patch};
use std::io;

// Parse base and diff
let parser = XmlParser::new(BaseNodeFactory);
let base = parser.parse_file("base.xml")?;
let diff = parser.parse_file("changes.xml")?;

// Apply patch
let patcher = Patch::new();
patcher.patch(&base, &diff, &mut io::stdout())?;
```

## Algorithm

The 3DM algorithm works in several phases:

1. **Parsing**: Builds tree representations of the XML documents
2. **Matching**: Uses heuristic matching to find corresponding nodes across trees
   - Exact matching by content hash
   - Fuzzy matching using Q-gram distance
   - Structural matching of children
3. **Merge**: Combines changes from both branches relative to the base
   - Detects inserts, deletes, moves, and updates
   - Resolves operation conflicts using a conflict table
   - Merges element content and attributes
4. **Output**: Serializes the merged tree back to XML

## Configuration

### Copy Detection Threshold

The minimum size (in information bytes) for copy detection can be configured:

```rust
use xml_3dm::TriMatching;

// Disable copy detection
let matching = TriMatching::with_copy_threshold(left, base, right, 0);

// Increase threshold (default is 128)
let matching = TriMatching::with_copy_threshold(left, base, right, 256);
```

### Custom Matching Algorithms

You can provide custom matching implementations:

```rust
use xml_3dm::{TriMatching, HeuristicMatching};

let left_matching = HeuristicMatching::new(128);
let right_matching = HeuristicMatching::new(128);

let matching = TriMatching::with_matching(
    left,
    base,
    right,
    left_matching,
    right_matching,
);
```

## Limitations

- No namespace awareness (attributes treated as simple name-value pairs)
- Processing instructions are not preserved (comments ARE preserved)
- Limited support for mixed content (element + text siblings)
- Requires well-formed XML input

## License

Licensed under the GNU Lesser General Public License v2.1 or later (LGPL-2.1-or-later), matching the original 3DM implementation.

## Credits

Original 3DM implementation by Tancred Lindholm (Helsinki University of Technology, 2001).
