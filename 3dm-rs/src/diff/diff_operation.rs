//! Diff operation types.
//!
//! Represents the different operations that can appear in a diff document.

/// Types of operations in a diff document.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiffOpType {
    /// Root tag with copy operation (base root matches branch root).
    RootCopy,
    /// Root tag with insert operation (new root).
    RootInsert,
    /// Copy a subtree from the base tree.
    Copy,
    /// Insert new content not from base.
    Insert,
}

/// A diff operation with source, destination, and run count.
#[derive(Debug, Clone)]
pub struct DiffOperation {
    /// The type of operation.
    pub op_type: DiffOpType,
    /// Source node ID (for copy operations).
    pub source: Option<u64>,
    /// Destination node ID (for positioning).
    pub destination: Option<u64>,
    /// Run count for consecutive copies.
    pub run: Option<u64>,
}

impl DiffOperation {
    /// Creates a new diff operation.
    pub fn new(
        op_type: DiffOpType,
        source: Option<u64>,
        destination: Option<u64>,
        run: Option<u64>,
    ) -> Self {
        DiffOperation {
            op_type,
            source,
            destination,
            run,
        }
    }

    /// Creates a root copy operation.
    pub fn root_copy() -> Self {
        DiffOperation::new(DiffOpType::RootCopy, None, None, None)
    }

    /// Creates a root insert operation.
    pub fn root_insert() -> Self {
        DiffOperation::new(DiffOpType::RootInsert, None, None, None)
    }

    /// Creates a copy operation.
    pub fn copy(source: u64, destination: Option<u64>, run: u64) -> Self {
        DiffOperation::new(DiffOpType::Copy, Some(source), destination, Some(run))
    }

    /// Creates an insert operation.
    pub fn insert(destination: Option<u64>) -> Self {
        DiffOperation::new(DiffOpType::Insert, None, destination, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_root_copy() {
        let op = DiffOperation::root_copy();
        assert_eq!(op.op_type, DiffOpType::RootCopy);
        assert!(op.source.is_none());
    }

    #[test]
    fn test_root_insert() {
        let op = DiffOperation::root_insert();
        assert_eq!(op.op_type, DiffOpType::RootInsert);
    }

    #[test]
    fn test_copy() {
        let op = DiffOperation::copy(5, Some(10), 3);
        assert_eq!(op.op_type, DiffOpType::Copy);
        assert_eq!(op.source, Some(5));
        assert_eq!(op.destination, Some(10));
        assert_eq!(op.run, Some(3));
    }

    #[test]
    fn test_insert() {
        let op = DiffOperation::insert(Some(7));
        assert_eq!(op.op_type, DiffOpType::Insert);
        assert!(op.source.is_none());
        assert_eq!(op.destination, Some(7));
    }
}
