# tdm - 3DM XML Tree Differencing and Merging Tool

A command-line tool for structure-aware XML differencing and 3-way merging.

## Overview

`tdm` (Tree Diff/Merge) is a CLI tool that performs operations on XML documents:

- **3-way merge**: Merge two modified versions relative to a common ancestor
- **Diff generation**: Create a compact diff representation showing changes
- **Patch application**: Apply a diff to reconstruct the modified version

The tool operates on XML tree structure and handles scenarios like moving and editing the same content.

## Installation

### From Source

```bash
cargo install --path .
```

### From Crates.io

```bash
cargo install xml-3dm-cli
```

## Usage

### 3-Way Merge

Merge two branches that diverged from a common base:

```bash
tdm merge <BASE> <BRANCH1> <BRANCH2> [OUTPUT]

# Example
tdm merge original.xml alice-edits.xml bob-edits.xml merged.xml

# Short form
tdm m base.xml branch1.xml branch2.xml
```

**Options:**

- `-c, --copy-threshold <BYTES>`: Minimum size for copy detection (default: 128)
  - Set to 0 to disable copy detection
  - Increase for larger documents to reduce false positives

### Diff Generation

Generate a diff showing changes from base to branch:

```bash
tdm diff <BASE> <BRANCH> [OUTPUT]

# Example
tdm diff original.xml modified.xml changes.xml

# Short form
tdm d base.xml branch.xml
```

The diff format uses XML with special `copy` and `insert` operations:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<diff>
  <diff:copy src="3" dst="1" />
  <diff:insert dst="2">
    <newElement>New content</newElement>
  </diff:insert>
</diff>
```

### Patch Application

Apply a diff to reconstruct the modified version:

```bash
tdm patch <BASE> <PATCHFILE> [OUTPUT]

# Example
tdm patch original.xml changes.xml reconstructed.xml

# Short form
tdm p base.xml patch.xml
```

## Examples

### Example 1: Simple Merge

Two reviewers edit a document independently:

```bash
# Alice moves a paragraph
# Bob fixes a typo in that paragraph
tdm merge original.xml alice-version.xml bob-version.xml result.xml
# Result: Paragraph is moved with the typo fixed
```

### Example 2: Conflict Detection

When changes cannot be automatically merged:

```bash
tdm merge base.xml branch1.xml branch2.xml merged.xml
# Output shows conflicts in stderr:
#   CONFLICT: Conflicting updates at /document/section[2]/@title
#   WARNING: Node deleted in one branch, modified in other
```

### Example 3: Disable Copy Detection

For faster merging on large documents:

```bash
tdm merge -c 0 base.xml branch1.xml branch2.xml merged.xml
```

### Example 4: Diff and Patch Round-Trip

```bash
# Generate diff
tdm diff original.xml modified.xml changes.xml

# Apply diff to reconstruct
tdm patch original.xml changes.xml reconstructed.xml

# Verify
diff modified.xml reconstructed.xml
# (should be identical)
```

## How It Works

### Matching Phase

1. **Parse** XML into tree structures
2. **Match nodes** across trees using:
   - Content hash equality (exact matches)
   - Q-gram distance for fuzzy matching
   - Tree structure similarity

### Merge Phase

1. **Detect operations**: Insert, delete, move, update, copy
2. **Resolve conflicts** using operation priority table
3. **Merge content**: Combine attribute and text changes
4. **Output** the merged tree

### Features

- **Structure-aware**: Understands XML elements, not just text lines
- **Move detection**: Tracks content moved between locations
- **Copy detection**: Identifies duplicated subtrees
- **Conflict reporting**: Clear error messages with document paths
- **Attribute merging**: Intelligent attribute-level conflict resolution

## Exit Codes

- `0`: Success (merge completed, possibly with warnings)
- `1`: Error (parse failure, I/O error, or unresolvable conflicts)

## Limitations

- Requires well-formed XML input
- No namespace awareness
- Processing instructions are not preserved (comments ARE preserved)
- Whitespace is normalized (consecutive spaces collapsed)

## Use Cases

- **Version control**: Use as a Git merge driver for XML files
- **Document collaboration**: Merge changes from multiple reviewers
- **Configuration management**: Merge XML configuration files
- **Data synchronization**: Sync XML data across systems

## Git Integration

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

## License

Licensed under the GNU Lesser General Public License v2.1 or later (LGPL-2.1-or-later).

## Credits

Based on the original [3DM tool](https://www.cs.hut.fi/~ctl/3dm/) by Tancred Lindholm (Helsinki University of Technology, 2001).

## Getting Help

```bash
tdm --help
tdm merge --help
tdm diff --help
tdm patch --help
```
