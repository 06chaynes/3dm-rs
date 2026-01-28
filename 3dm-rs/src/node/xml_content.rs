//! XML content types for tree nodes.
//!
//! This module provides `XmlContent`, which represents the content of an XML node,
//! either an element (tag with attributes) or text content.

use crate::constants::{ATTR_INFO, ATTR_VALUE_THRESHOLD, ELEMENT_NAME_INFO, TEXT_THRESHOLD};
use md5::{Digest, Md5};
use std::collections::HashMap;

use super::namespace::ExpandedName;

/// Represents the content of an XML node.
#[derive(Debug, Clone)]
pub enum XmlContent {
    /// An XML element with a qualified name and attributes.
    Element(XmlElement),
    /// XML text content.
    Text(XmlText),
    /// XML comment.
    Comment(XmlComment),
    /// XML processing instruction.
    ProcessingInstruction(XmlProcessingInstruction),
}

impl XmlContent {
    /// Returns the information size of this content.
    ///
    /// This metric is used for similarity calculations and copy detection.
    pub fn info_size(&self) -> i32 {
        match self {
            XmlContent::Element(e) => e.info_size,
            XmlContent::Text(t) => t.info_size,
            XmlContent::Comment(c) => c.info_size,
            XmlContent::ProcessingInstruction(pi) => pi.info_size,
        }
    }

    /// Tests content equality using MD5 hash comparison.
    pub fn content_equals(&self, other: &XmlContent) -> bool {
        match (self, other) {
            (XmlContent::Element(a), XmlContent::Element(b)) => a.content_equals(b),
            (XmlContent::Text(a), XmlContent::Text(b)) => a.content_equals(b),
            (XmlContent::Comment(a), XmlContent::Comment(b)) => a.content_equals(b),
            (XmlContent::ProcessingInstruction(a), XmlContent::ProcessingInstruction(b)) => {
                a.content_equals(b)
            }
            _ => false,
        }
    }

    /// Returns a 32-bit hash code for this content.
    ///
    /// This is used for fast equality pre-checks and child list distance calculations.
    pub fn content_hash(&self) -> i32 {
        match self {
            XmlContent::Element(e) => e.content_hash(),
            XmlContent::Text(t) => t.content_hash(),
            XmlContent::Comment(c) => c.content_hash(),
            XmlContent::ProcessingInstruction(pi) => pi.content_hash(),
        }
    }

    /// Returns true if this is an element node.
    pub fn is_element(&self) -> bool {
        matches!(self, XmlContent::Element(_))
    }

    /// Returns true if this is a text node.
    pub fn is_text(&self) -> bool {
        matches!(self, XmlContent::Text(_))
    }

    /// Returns true if this is a comment node.
    pub fn is_comment(&self) -> bool {
        matches!(self, XmlContent::Comment(_))
    }

    /// Returns true if this is a processing instruction node.
    pub fn is_processing_instruction(&self) -> bool {
        matches!(self, XmlContent::ProcessingInstruction(_))
    }

    /// Returns a reference to the element, if this is an element node.
    pub fn as_element(&self) -> Option<&XmlElement> {
        match self {
            XmlContent::Element(e) => Some(e),
            _ => None,
        }
    }

    /// Returns a mutable reference to the element, if this is an element node.
    pub fn as_element_mut(&mut self) -> Option<&mut XmlElement> {
        match self {
            XmlContent::Element(e) => Some(e),
            _ => None,
        }
    }

    /// Returns a reference to the text, if this is a text node.
    pub fn as_text(&self) -> Option<&XmlText> {
        match self {
            XmlContent::Text(t) => Some(t),
            _ => None,
        }
    }

    /// Returns a mutable reference to the text, if this is a text node.
    pub fn as_text_mut(&mut self) -> Option<&mut XmlText> {
        match self {
            XmlContent::Text(t) => Some(t),
            _ => None,
        }
    }

    /// Returns a reference to the PI, if this is a processing instruction node.
    pub fn as_processing_instruction(&self) -> Option<&XmlProcessingInstruction> {
        match self {
            XmlContent::ProcessingInstruction(pi) => Some(pi),
            _ => None,
        }
    }
}

/// Calculates MD5 hash of character data, matching Java's byte ordering.
///
/// Java's `MessageDigest.update()` is called with:
/// - `(byte) (char & 0xff)` - low byte
/// - `(byte) (char >> 8)` - high byte
///
/// This is little-endian byte order for each UTF-16 code unit.
fn calculate_hash_chars(data: &[char]) -> [u8; 16] {
    let mut hasher = Md5::new();
    for &c in data {
        let code = c as u16;
        hasher.update([(code & 0xff) as u8, (code >> 8) as u8]);
    }
    hasher.finalize().into()
}

/// Calculates MD5 hash of a string, matching Java's byte ordering.
fn calculate_hash_str(data: &str) -> [u8; 16] {
    let mut hasher = Md5::new();
    // Java strings are UTF-16, so we iterate over UTF-16 code units
    for code in data.encode_utf16() {
        hasher.update([(code & 0xff) as u8, (code >> 8) as u8]);
    }
    hasher.finalize().into()
}

/// Converts the first 4 bytes of an MD5 hash to a 32-bit integer.
///
/// This matches Java's behavior where bytes are sign-extended when used
/// in arithmetic expressions. In Java:
/// ```java
/// hash[0] + (hash[1] << 8) + (hash[2] << 16) + (hash[3] << 24)
/// ```
/// Since Java bytes are signed, negative values get sign-extended.
fn hash_to_i32(hash: &[u8; 16]) -> i32 {
    // Cast to i8 first to get Java's signed byte behavior, then sign-extend to i32
    let b0 = hash[0] as i8 as i32;
    let b1 = hash[1] as i8 as i32;
    let b2 = hash[2] as i8 as i32;
    let b3 = hash[3] as i8 as i32;
    b0.wrapping_add(b1 << 8)
        .wrapping_add(b2 << 16)
        .wrapping_add(b3 << 24)
}

/// An XML element with a qualified name and attributes.
#[derive(Debug, Clone)]
pub struct XmlElement {
    /// The qualified name of the element (e.g., "div", "ns:element").
    name: String,
    /// The expanded name (namespace URI + local name), if parsed with namespace awareness.
    expanded_name: Option<ExpandedName>,
    /// Namespace declarations on this element (prefix -> URI).
    namespace_decls: HashMap<String, String>,
    /// Attributes as key-value pairs. The key is the qualified attribute name.
    attributes: HashMap<String, String>,
    /// Cached hash code of the element name (matches Java's String.hashCode()).
    name_hash: i32,
    /// MD5 hash of the attributes.
    attr_hash: [u8; 16],
    /// Information size metric.
    info_size: i32,
}

impl XmlElement {
    /// Creates a new XML element with the given name and attributes.
    pub fn new(name: String, attributes: HashMap<String, String>) -> Self {
        Self::new_with_namespace(name, None, HashMap::new(), attributes)
    }

    /// Creates a new element with namespace information.
    pub fn new_with_namespace(
        name: String,
        expanded_name: Option<ExpandedName>,
        namespace_decls: HashMap<String, String>,
        attributes: HashMap<String, String>,
    ) -> Self {
        let mut element = XmlElement {
            name,
            expanded_name,
            namespace_decls,
            attributes,
            name_hash: 0,
            attr_hash: [0; 16],
            info_size: 0,
        };
        element.rehash();
        element
    }

    /// Recalculates the hash values and info size.
    ///
    /// This should be called after modifying the name or attributes.
    pub fn rehash(&mut self) {
        self.name_hash = java_string_hash(&self.name);
        self.info_size = ELEMENT_NAME_INFO;

        let mut hasher = Md5::new();

        // Sort attribute names for deterministic hashing
        // Note: Java's AttributesImpl iteration order may differ, but for our
        // purposes we need consistent ordering. The Java code iterates in
        // insertion order, which we'll match by sorting.
        let mut attr_names: Vec<&String> = self.attributes.keys().collect();
        attr_names.sort();

        for attr_name in attr_names {
            let attr_value = &self.attributes[attr_name];
            let vsize = attr_value.chars().count() as i32;
            self.info_size += ATTR_INFO
                + if vsize > ATTR_VALUE_THRESHOLD {
                    vsize - ATTR_VALUE_THRESHOLD
                } else {
                    1
                };
            hasher.update(calculate_hash_str(attr_name));
            hasher.update(calculate_hash_str(attr_value));
        }

        self.attr_hash = hasher.finalize().into();
    }

    /// Returns the qualified name of the element.
    pub fn qname(&self) -> &str {
        &self.name
    }

    /// Sets the qualified name of the element.
    ///
    /// Note: This does not automatically rehash. Call `rehash()` after
    /// modifying if hash values are needed.
    pub fn set_qname(&mut self, name: String) {
        self.name = name;
    }

    /// Returns the attributes.
    pub fn attributes(&self) -> &HashMap<String, String> {
        &self.attributes
    }

    /// Returns a mutable reference to the attributes.
    ///
    /// Note: This does not automatically rehash. Call `rehash()` after
    /// modifying if hash values are needed.
    pub fn attributes_mut(&mut self) -> &mut HashMap<String, String> {
        &mut self.attributes
    }

    /// Sets the attributes.
    ///
    /// Note: This does not automatically rehash. Call `rehash()` after
    /// modifying if hash values are needed.
    pub fn set_attributes(&mut self, attributes: HashMap<String, String>) {
        self.attributes = attributes;
    }

    /// Returns the expanded name, if available.
    pub fn expanded_name(&self) -> Option<&ExpandedName> {
        self.expanded_name.as_ref()
    }

    /// Returns namespace declarations on this element.
    pub fn namespace_decls(&self) -> &HashMap<String, String> {
        &self.namespace_decls
    }

    /// Compares element names with namespace awareness.
    /// Falls back to string comparison if neither has expanded names.
    pub fn names_match(&self, other: &XmlElement) -> bool {
        match (&self.expanded_name, &other.expanded_name) {
            (Some(a), Some(b)) => a == b,
            (None, None) => self.name == other.name,
            _ => false,
        }
    }

    /// Tests content equality using hash comparison.
    ///
    /// Note: This compares element name and attributes only, not namespace
    /// declarations. Use `namespace_decls_equal` for namespace comparison.
    pub fn content_equals(&self, other: &XmlElement) -> bool {
        self.name_hash == other.name_hash && self.attr_hash == other.attr_hash
    }

    /// Tests whether namespace declarations are equal.
    pub fn namespace_decls_equal(&self, other: &XmlElement) -> bool {
        self.namespace_decls == other.namespace_decls
    }

    /// Returns a 32-bit hash code for this element.
    pub fn content_hash(&self) -> i32 {
        hash_to_i32(&self.attr_hash) ^ self.name_hash
    }

    /// Returns the information size.
    pub fn info_size(&self) -> i32 {
        self.info_size
    }
}

impl std::fmt::Display for XmlElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {{", self.name)?;
        let mut first = true;
        // Sort for consistent output
        let mut attr_names: Vec<&String> = self.attributes.keys().collect();
        attr_names.sort();
        for name in attr_names {
            if !first {
                write!(f, " ")?;
            }
            first = false;
            write!(f, " {}={}", name, self.attributes[name])?;
        }
        write!(f, "}}")
    }
}

/// XML text content.
#[derive(Debug, Clone)]
pub struct XmlText {
    /// The text content as a character array (matching Java's char[]).
    text: Vec<char>,
    /// MD5 hash of the text content.
    content_hash: [u8; 16],
    /// Information size metric.
    info_size: i32,
}

impl XmlText {
    /// Creates a new text node from a string.
    pub fn new(text: &str) -> Self {
        let chars: Vec<char> = text.chars().collect();
        Self::from_chars(chars)
    }

    /// Creates a new text node from a character array.
    pub fn from_chars(text: Vec<char>) -> Self {
        let content_hash = calculate_hash_chars(&text);
        let len = text.len() as i32;
        let info_size = if len > TEXT_THRESHOLD {
            len - TEXT_THRESHOLD
        } else {
            1
        };
        XmlText {
            text,
            content_hash,
            info_size,
        }
    }

    /// Creates a new text node from a slice of characters.
    pub fn from_char_slice(text: &[char], start: usize, length: usize) -> Self {
        let chars: Vec<char> = text[start..start + length].to_vec();
        Self::from_chars(chars)
    }

    /// Tests content equality using MD5 hash comparison.
    pub fn content_equals(&self, other: &XmlText) -> bool {
        self.content_hash == other.content_hash
    }

    /// Returns the text as a character slice.
    pub fn text(&self) -> &[char] {
        &self.text
    }

    /// Sets the text content.
    ///
    /// Note: This recalculates the hash and info size.
    pub fn set_text(&mut self, text: Vec<char>) {
        self.content_hash = calculate_hash_chars(&text);
        let len = text.len() as i32;
        self.info_size = if len > TEXT_THRESHOLD {
            len - TEXT_THRESHOLD
        } else {
            1
        };
        self.text = text;
    }

    /// Returns a 32-bit hash code for this text node.
    pub fn content_hash(&self) -> i32 {
        hash_to_i32(&self.content_hash)
    }

    /// Returns the information size.
    pub fn info_size(&self) -> i32 {
        self.info_size
    }
}

impl std::fmt::Display for XmlText {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.text.iter().collect();
        write!(f, "{}", s)
    }
}

/// XML comment content.
#[derive(Debug, Clone)]
pub struct XmlComment {
    /// The comment text (without the <!-- and --> markers).
    text: Vec<char>,
    /// MD5 hash of the comment content.
    content_hash: [u8; 16],
    /// Information size metric (comments have minimal info size).
    info_size: i32,
}

impl XmlComment {
    /// Creates a new comment node from a string.
    pub fn new(text: &str) -> Self {
        let chars: Vec<char> = text.chars().collect();
        Self::from_chars(chars)
    }

    /// Creates a new comment node from a character array.
    pub fn from_chars(text: Vec<char>) -> Self {
        let content_hash = calculate_hash_chars(&text);
        // Comments have minimal info size (don't contribute much to structure)
        let info_size = 1;
        XmlComment {
            text,
            content_hash,
            info_size,
        }
    }

    /// Tests content equality using MD5 hash comparison.
    pub fn content_equals(&self, other: &XmlComment) -> bool {
        self.content_hash == other.content_hash
    }

    /// Returns the comment text as a character slice.
    pub fn text(&self) -> &[char] {
        &self.text
    }

    /// Sets the comment text.
    pub fn set_text(&mut self, text: Vec<char>) {
        self.content_hash = calculate_hash_chars(&text);
        self.text = text;
    }

    /// Returns a 32-bit hash code for this comment node.
    pub fn content_hash(&self) -> i32 {
        hash_to_i32(&self.content_hash)
    }

    /// Returns the information size.
    pub fn info_size(&self) -> i32 {
        self.info_size
    }
}

impl std::fmt::Display for XmlComment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.text.iter().collect();
        write!(f, "<!-- {} -->", s)
    }
}

/// XML processing instruction content.
#[derive(Debug, Clone)]
pub struct XmlProcessingInstruction {
    /// The target of the PI (e.g., "xml-stylesheet").
    target: String,
    /// The content/data of the PI (everything after the target).
    content: String,
    /// MD5 hash of combined target and content.
    content_hash: [u8; 16],
    /// Information size metric (PIs have minimal info size like comments).
    info_size: i32,
}

impl XmlProcessingInstruction {
    /// Creates a new PI from target and content strings.
    pub fn new(target: &str, content: &str) -> Self {
        let content_hash = Self::calculate_hash(target, content);
        XmlProcessingInstruction {
            target: target.to_string(),
            content: content.to_string(),
            content_hash,
            info_size: 1,
        }
    }

    fn calculate_hash(target: &str, content: &str) -> [u8; 16] {
        use md5::{Digest, Md5};
        let mut hasher = Md5::new();
        for code in target.encode_utf16() {
            hasher.update([(code & 0xff) as u8, (code >> 8) as u8]);
        }
        for code in content.encode_utf16() {
            hasher.update([(code & 0xff) as u8, (code >> 8) as u8]);
        }
        hasher.finalize().into()
    }

    /// Tests content equality using MD5 hash comparison.
    pub fn content_equals(&self, other: &XmlProcessingInstruction) -> bool {
        self.content_hash == other.content_hash
    }

    /// Returns the PI target.
    pub fn target(&self) -> &str {
        &self.target
    }

    /// Returns the PI content.
    pub fn content(&self) -> &str {
        &self.content
    }

    /// Returns a 32-bit hash code for this PI node.
    pub fn content_hash(&self) -> i32 {
        hash_to_i32(&self.content_hash)
    }

    /// Returns the information size.
    pub fn info_size(&self) -> i32 {
        self.info_size
    }
}

impl std::fmt::Display for XmlProcessingInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.content.is_empty() {
            write!(f, "<?{}?>", self.target)
        } else {
            write!(f, "<?{} {}?>", self.target, self.content)
        }
    }
}

/// Computes a hash code compatible with Java's String.hashCode().
///
/// Java's algorithm: `s[0]*31^(n-1) + s[1]*31^(n-2) + ... + s[n-1]`
/// where n is the length of the string.
///
/// This uses wrapping arithmetic to match Java's int overflow behavior.
pub fn java_string_hash(s: &str) -> i32 {
    let mut hash: i32 = 0;
    for code in s.encode_utf16() {
        hash = hash.wrapping_mul(31).wrapping_add(code as i32);
    }
    hash
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_java_string_hash() {
        // Test some known Java String.hashCode() values
        assert_eq!(java_string_hash(""), 0);
        assert_eq!(java_string_hash("a"), 97);
        assert_eq!(java_string_hash("ab"), 97 * 31 + 98);
        assert_eq!(java_string_hash("hello"), 99162322);
    }

    #[test]
    fn test_text_node_equality() {
        let t1 = XmlText::new("hello world");
        let t2 = XmlText::new("hello world");
        let t3 = XmlText::new("hello world!");

        assert!(t1.content_equals(&t2));
        assert!(!t1.content_equals(&t3));
    }

    #[test]
    fn test_element_equality() {
        let mut attrs1 = HashMap::new();
        attrs1.insert("id".to_string(), "foo".to_string());

        let mut attrs2 = HashMap::new();
        attrs2.insert("id".to_string(), "foo".to_string());

        let mut attrs3 = HashMap::new();
        attrs3.insert("id".to_string(), "bar".to_string());

        let e1 = XmlElement::new("div".to_string(), attrs1);
        let e2 = XmlElement::new("div".to_string(), attrs2);
        let e3 = XmlElement::new("div".to_string(), attrs3);
        let e4 = XmlElement::new("span".to_string(), HashMap::new());

        assert!(e1.content_equals(&e2));
        assert!(!e1.content_equals(&e3));
        assert!(!e1.content_equals(&e4));
    }

    #[test]
    fn test_info_size() {
        // Text shorter than threshold
        let t1 = XmlText::new("hi");
        assert_eq!(t1.info_size(), 1);

        // Text longer than threshold (5)
        let t2 = XmlText::new("hello world");
        assert_eq!(t2.info_size(), 11 - TEXT_THRESHOLD);

        // Element with no attributes
        let e1 = XmlElement::new("div".to_string(), HashMap::new());
        assert_eq!(e1.info_size(), ELEMENT_NAME_INFO);

        // Element with attribute (value shorter than threshold)
        let mut attrs = HashMap::new();
        attrs.insert("id".to_string(), "x".to_string());
        let e2 = XmlElement::new("div".to_string(), attrs);
        assert_eq!(e2.info_size(), ELEMENT_NAME_INFO + ATTR_INFO + 1);
    }

    #[test]
    fn test_xml_content_enum() {
        let elem = XmlContent::Element(XmlElement::new("div".to_string(), HashMap::new()));
        let text = XmlContent::Text(XmlText::new("hello"));

        assert!(elem.is_element());
        assert!(!elem.is_text());
        assert!(!text.is_element());
        assert!(text.is_text());

        assert!(elem.as_element().is_some());
        assert!(elem.as_text().is_none());
        assert!(text.as_text().is_some());
        assert!(text.as_element().is_none());
    }

    #[test]
    fn test_namespace_decls_affect_equality() {
        let attrs = HashMap::new();

        let mut ns1 = HashMap::new();
        ns1.insert("a".to_string(), "http://example.com/a".to_string());

        let mut ns2 = HashMap::new();
        ns2.insert("b".to_string(), "http://example.com/b".to_string());

        let e1 = XmlElement::new_with_namespace("root".to_string(), None, ns1, attrs.clone());
        let e2 = XmlElement::new_with_namespace("root".to_string(), None, ns2, attrs.clone());
        let e3 = XmlElement::new("root".to_string(), attrs);

        // content_equals ignores namespace declarations (intentional)
        assert!(e1.content_equals(&e2));
        assert!(e1.content_equals(&e3));

        // namespace_decls_equal detects namespace differences
        assert!(!e1.namespace_decls_equal(&e2));
        assert!(!e1.namespace_decls_equal(&e3));
        assert!(e1.namespace_decls_equal(&e1));
    }
}
