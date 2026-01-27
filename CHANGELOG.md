# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.3] - 2026-01-26

### Fixed

- **Merge output whitespace**: Fixed text content serialization in merge output. Previously added spurious whitespace around text nodes (e.g., `<title>\n  text  </title>`). Now uses `XmlPrinter` for correct inline text handling.

### Added

- **`merge_to_tree()` API**: New public method that returns the merged tree as a `NodeRef` for programmatic inspection or modification before output.

## [0.1.2] - 2026-01-26

### Changed

- **Adaptive Q-gram sizing**: Implemented thesis equation for Q-gram distance calculation. Q-gram size now adapts based on combined string length (q=1 for <5, q=2 for 5-49, q=4 for ≥50) instead of fixed q=4. Improves fuzzy matching discrimination for short strings.

## [0.1.1] - 2026-01-26

### Fixed

- **MoveF-MoveF conflict detection**: Implemented proper parent comparison in `is_movef_movef_conflict()`. Previously returned false unconditionally; now correctly detects when both branches move the same node to different parents.

- **Escape handling for reserved diff tags**: Added `<esc>` wrapper for user XML elements named `copy`, `insert`, `esc`, or `diff` in diff output. Prevents misinterpretation of user content as diff commands during patch application.

### Changed

- Updated `quick-xml` from 0.38 to 0.39

## [0.1.0] - 2025-11-26

### Added

- Initial release
