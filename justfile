# Default recipe to display available commands
default:
    @just --list

# Format all code
fmt:
    cargo fmt --all

# Check formatting without making changes
fmt-check:
    cargo fmt --all -- --check

# Run clippy on all targets
lint:
    cargo clippy --all-targets --all-features -- -D warnings

# Run clippy with fixes
lint-fix:
    cargo clippy --all-targets --all-features --fix --allow-dirty --allow-staged

# Run tests for the library
test-lib:
    cargo test --package xml-3dm --lib

# Run tests for the CLI
test-cli:
    cargo test --package xml-3dm-cli

# Run all tests
test:
    cargo test --all

# Run all checks (format, clippy, tests)
check: fmt-check lint test

# Run all checks and fixes
fix: fmt lint-fix test

# Build the project
build:
    cargo build --all

# Build in release mode
build-release:
    cargo build --all --release

# Clean build artifacts
clean:
    cargo clean

# Release a new version (usage: just release patch|minor|major)
release LEVEL:
    cargo release {{LEVEL}} --execute

# Preview what a release would do without making changes
release-dry-run LEVEL:
    cargo release {{LEVEL}}

# Verify dist configuration
dist-plan:
    cargo dist plan

# Build all examples
build-examples:
    cargo build --examples --package xml-3dm

# Run the merge example (usage: just example-merge <base.xml> <branch1.xml> <branch2.xml>)
example-merge *ARGS:
    cargo run --package xml-3dm --example merge -- {{ARGS}}

# Run the diff example (usage: just example-diff <base.xml> <modified.xml>)
example-diff *ARGS:
    cargo run --package xml-3dm --example diff -- {{ARGS}}

# Run the patch example (usage: just example-patch <base.xml> <diff.xml>)
example-patch *ARGS:
    cargo run --package xml-3dm --example patch -- {{ARGS}}

# Show example usage
examples-help:
    @echo "Available examples:"
    @echo ""
    @echo "  just example-merge <base.xml> <branch1.xml> <branch2.xml>"
    @echo "    Perform a 3-way merge of XML documents"
    @echo ""
    @echo "  just example-diff <base.xml> <modified.xml>"
    @echo "    Generate a diff between two XML documents"
    @echo ""
    @echo "  just example-patch <base.xml> <diff.xml>"
    @echo "    Apply a diff patch to a base XML document"
    @echo ""
    @echo "Example files are available in: 3dm-rs/tests/fixtures/mergecases/"
    @echo ""
    @echo "Example usage with test fixtures:"
    @echo "  just example-merge 3dm-rs/tests/fixtures/mergecases/a1/b.xml 3dm-rs/tests/fixtures/mergecases/a1/1.xml 3dm-rs/tests/fixtures/mergecases/a1/2.xml"
