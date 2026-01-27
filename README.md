# 3DM-RS: XML Differencing and Merging

A Rust implementation of the 3DM (3-way Diff/Merge) algorithm for XML document processing.

## Overview

3DM-RS provides a library (`xml-3dm`) and CLI tool (`tdm`) for structure-aware XML operations. The implementation operates on XML tree structure rather than text lines.

**Capabilities:**

- 3-way merge: Combine changes from two branches relative to a common ancestor
- Diff generation: Create compact diff representations with copy detection
- Patch application: Apply diffs to reconstruct modified documents
- Structure awareness: Operates on XML tree structure
- Move detection: Tracks content moved between locations
- Copy detection: Identifies and encodes duplicated subtrees
- Conflict resolution: Provides conflict and warning logs with document paths
- Comment preservation: XML comments are preserved through all operations
- Formatted output: Proper indentation with 2 spaces per level

## Quick Start

### Command-Line Tool

```bash
# Install the CLI tool
cargo install --path tdm-cli

# Merge two edited versions
tdm merge original.xml alice-edits.xml bob-edits.xml merged.xml

# Generate a diff
tdm diff original.xml modified.xml changes.xml

# Apply a patch
tdm patch original.xml changes.xml reconstructed.xml
```

See [tdm-cli/README.md](tdm-cli/README.md) for CLI documentation.

### Library

```toml
[dependencies]
xml-3dm = "0.1"
```

```rust
use xml_3dm::{XmlParser, BaseNodeFactory, BranchNodeFactory, Merge, TriMatching};
use std::io;

// Parse the three XML files
let base_parser = XmlParser::new(BaseNodeFactory);
let branch_parser = XmlParser::new(BranchNodeFactory);

let base = base_parser.parse_file("base.xml")?;
let branch1 = branch_parser.parse_file("branch1.xml")?;
let branch2 = branch_parser.parse_file("branch2.xml")?;

// Build matching and merge
let tri_matching = TriMatching::new(branch1, base, branch2);
let mut merger = Merge::new(tri_matching);

// Output merged result
merger.merge(&mut io::stdout())?;

// Check for conflicts
if !merger.conflict_log.conflicts().is_empty() {
    eprintln!("Conflicts detected!");
}
```

See [3dm-rs/README.md](3dm-rs/README.md) for library documentation.

## Example: Structure-Aware Merging

Consider a document being edited by two people:

**Original (base.xml):**

```xml
<document>
  <section id="intro">
    <para>This is the introduciton.</para>
  </section>
</document>
```

**Alice's edits:** Moves the paragraph to a new section
**Bob's edits:** Fixes the typo "introduciton" → "introduction"

**3DM Result:**

```xml
<document>
  <section id="overview">
    <para>This is the introduction.</para>
  </section>
</document>
```

The paragraph is both moved and corrected in the merged output.

## Features

### Structure-Aware Operations

- Element matching: Uses content hashing and Q-gram distance
- Copy detection: Identifies subtrees copied to multiple locations
- Move operations: Tracks content moved within or between parents
- Attribute merging: Conflict resolution at attribute level

### Output

- Formatted XML: Indented with 2 spaces per level
- Comment preservation: XML comments are maintained
- Entity encoding: Proper escaping of special characters
- Deterministic output: Consistent attribute ordering

### Error Handling

- Conflict detection: Identifies unresolvable conflicts
- Warning logs: Reports potential issues
- Path tracking: Shows document location for each conflict
- Operation logging: Records all edit operations

## Configuration

### Copy Detection Threshold

```bash
# Disable copy detection
tdm merge -c 0 base.xml branch1.xml branch2.xml merged.xml

# Increase threshold
tdm merge -c 256 base.xml branch1.xml branch2.xml merged.xml
```

### Custom Matching Algorithms

```rust
use xml_3dm::{TriMatching, HeuristicMatching};

let tri = TriMatching::with_matching(
    branch1,
    base,
    branch2,
    HeuristicMatching::new(128),
    HeuristicMatching::new(128),
);
```

## Algorithm Overview

1. **Parsing**: Build tree representations using quick-xml
2. **Matching**: Find corresponding nodes across trees
   - Exact matching by MD5 content hash
   - Fuzzy matching using Q-gram distance (Ukkonen 1992)
   - Structural similarity of child lists
3. **Merge**: Combine changes from both branches
   - Detect operations (insert, delete, move, copy, update)
   - Resolve conflicts using operation priority table
   - Merge element content and attributes
4. **Output**: Serialize merged tree with formatting

## Use Cases

- Version control: Git merge driver for XML files
- Document collaboration: Merge changes from multiple reviewers
- Configuration management: Merge XML configuration files
- Data synchronization: Sync XML data across systems
- Schema evolution: Merge database schema definitions

### Git Integration

Configure `tdm` as a Git merge driver:

```bash
# In .git/config or ~/.gitconfig
[merge "xml3dm"]
    name = 3DM XML merge driver
    driver = tdm merge %O %A %B %A
    recursive = binary

# In .gitattributes
*.xml merge=xml3dm
```

For pretty-printed output with indentation, add the `--pretty` flag:

```bash
driver = tdm merge --pretty %O %A %B %A
```

## Limitations

- No namespace awareness: Namespaces treated as part of element names
- Whitespace normalization: Consecutive whitespace collapsed to single space
- Processing instructions: Not preserved (comments are preserved)
- Well-formed XML only: Does not handle malformed documents

## License

Licensed under the GNU Lesser General Public License v2.1 or later (LGPL-2.1-or-later), matching the original 3DM implementation.

## Credits

Original 3DM implementation by Tancred Lindholm (Helsinki University of Technology, 2001).

## Getting Help

```bash
# CLI help
tdm --help
tdm merge --help

# Library documentation
cargo doc --open
```
