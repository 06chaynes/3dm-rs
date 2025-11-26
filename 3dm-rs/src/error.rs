//! Error types for 3DM.

use thiserror::Error;

/// Result type alias for 3DM operations.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during 3DM operations.
#[derive(Error, Debug)]
pub enum Error {
    /// XML parsing error.
    #[error("XML parse error: {0}")]
    Parse(String),

    /// Invalid match type value.
    #[error("Invalid match type: {0}")]
    InvalidMatchType(u8),

    /// Node operation error.
    #[error("Node error: {0}")]
    Node(String),

    /// I/O error.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    /// XML error from quick-xml.
    #[error("XML error: {0}")]
    Xml(#[from] quick_xml::Error),
}
