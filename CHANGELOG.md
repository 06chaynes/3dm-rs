# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.1] - 2026-01-26

### Fixed

- **MoveF-MoveF conflict detection** (ISS-G01): Implemented proper parent comparison in `is_movef_movef_conflict()`. Previously returned false unconditionally; now correctly detects when both branches move the same node to different parents.

- **Escape handling for reserved diff tags** (ISS-F01): Added `<esc>` wrapper for user XML elements named `copy`, `insert`, `esc`, or `diff` in diff output. Prevents misinterpretation of user content as diff commands during patch application.

### Changed

- Updated `quick-xml` from 0.38 to 0.39

## [0.1.0] - 2025-11-26

### Added

- Initial release
