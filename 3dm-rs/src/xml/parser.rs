//! XML parser that builds node trees.
//!
//! This parser uses quick-xml's streaming API to build node trees matching
//! the Java implementation's behavior.

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;

use quick_xml::escape::unescape;
use quick_xml::events::{BytesStart, Event};
use quick_xml::Reader;

use super::NodeFactory;
use crate::error::{Error, Result};
use crate::node::{NodeInner, NodeRef, XmlComment, XmlContent, XmlElement, XmlText};

/// XML parser that builds node trees.
pub struct XmlParser<F: NodeFactory> {
    factory: F,
}

impl<F: NodeFactory> XmlParser<F> {
    /// Creates a new parser with the given node factory.
    pub fn new(factory: F) -> Self {
        XmlParser { factory }
    }

    /// Parses XML from a string.
    pub fn parse_str(&self, xml: &str) -> Result<NodeRef> {
        let mut reader = Reader::from_str(xml);
        // Don't trim text - we handle whitespace normalization ourselves
        reader.config_mut().trim_text_start = false;
        reader.config_mut().trim_text_end = false;
        self.parse_reader(&mut reader)
    }

    /// Parses XML from a file.
    pub fn parse_file<P: AsRef<Path>>(&self, path: P) -> Result<NodeRef> {
        let file = File::open(path)?;
        let buf_reader = BufReader::new(file);
        let mut reader = Reader::from_reader(buf_reader);
        // Don't trim text - we handle whitespace normalization ourselves
        reader.config_mut().trim_text_start = false;
        reader.config_mut().trim_text_end = false;
        self.parse_reader(&mut reader)
    }

    /// Parses XML from a quick-xml Reader.
    fn parse_reader<R: Read + std::io::BufRead>(&self, reader: &mut Reader<R>) -> Result<NodeRef> {
        // Create the synthetic $ROOT$ element (matches Java's startDocument)
        let root = self.factory.make_node(XmlContent::Element(XmlElement::new(
            "$ROOT$".to_string(),
            HashMap::new(),
        )));

        let mut node_stack: Vec<NodeRef> = vec![root.clone()];
        let mut current_text: Option<String> = None;
        let mut buf = Vec::new();

        loop {
            match reader.read_event_into(&mut buf) {
                Ok(Event::Start(ref e)) => {
                    // Flush any accumulated text
                    if let Some(text) = current_text.take() {
                        let trimmed = text.trim();
                        if !trimmed.is_empty() {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(trimmed)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    // Create the element node
                    let element = self.parse_element(e, reader)?;
                    let node = self.factory.make_node(XmlContent::Element(element));

                    // Add to parent and push onto stack
                    if let Some(parent) = node_stack.last() {
                        NodeInner::add_child_to_ref(parent, node.clone());
                    }
                    node_stack.push(node);
                }
                Ok(Event::End(_)) => {
                    // Flush any accumulated text
                    if let Some(text) = current_text.take() {
                        let trimmed = text.trim();
                        if !trimmed.is_empty() {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(trimmed)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    // Pop from stack
                    node_stack.pop();
                }
                Ok(Event::Empty(ref e)) => {
                    // Self-closing tag - handle like Start + End
                    if let Some(text) = current_text.take() {
                        let trimmed = text.trim();
                        if !trimmed.is_empty() {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(trimmed)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    let element = self.parse_element(e, reader)?;
                    let node = self.factory.make_node(XmlContent::Element(element));

                    if let Some(parent) = node_stack.last() {
                        NodeInner::add_child_to_ref(parent, node);
                    }
                }
                Ok(Event::Text(e)) => {
                    // Accumulate text, normalizing whitespace as Java does
                    let raw =
                        std::str::from_utf8(e.as_ref()).map_err(|e| Error::Parse(e.to_string()))?;
                    let text = unescape(raw).map_err(|e| Error::Parse(e.to_string()))?;
                    let normalized = self.normalize_whitespace(&text, current_text.as_deref());
                    if let Some(normalized) = normalized {
                        current_text = Some(match current_text {
                            Some(mut existing) => {
                                existing.push_str(&normalized);
                                existing
                            }
                            None => normalized,
                        });
                    }
                }
                Ok(Event::CData(ref e)) => {
                    // Treat CDATA like text
                    let text = String::from_utf8_lossy(e.as_ref());
                    let normalized = self.normalize_whitespace(&text, current_text.as_deref());
                    if let Some(normalized) = normalized {
                        current_text = Some(match current_text {
                            Some(mut existing) => {
                                existing.push_str(&normalized);
                                existing
                            }
                            None => normalized,
                        });
                    }
                }
                Ok(Event::Eof) => break,
                Ok(Event::Comment(ref e)) => {
                    // Capture comments as nodes
                    let comment_text = String::from_utf8_lossy(e.as_ref()).to_string();
                    let comment_node = self
                        .factory
                        .make_node(XmlContent::Comment(XmlComment::new(&comment_text)));
                    if let Some(parent) = node_stack.last() {
                        NodeInner::add_child_to_ref(parent, comment_node);
                    }
                }
                Ok(Event::Decl(_)) | Ok(Event::PI(_)) => {
                    // Ignore XML declaration and processing instructions
                }
                Ok(Event::DocType(_)) => {
                    // Ignore DOCTYPE
                }
                Ok(Event::GeneralRef(_)) => {
                    // Ignore general entity references
                }
                Err(e) => return Err(Error::Parse(format!("XML parse error: {}", e))),
            }
            buf.clear();
        }

        Ok(root)
    }

    /// Parses an element's name and attributes.
    fn parse_element<R: Read + std::io::BufRead>(
        &self,
        e: &BytesStart,
        reader: &Reader<R>,
    ) -> Result<XmlElement> {
        let name = reader
            .decoder()
            .decode(e.name().as_ref())
            .map_err(|e| Error::Parse(e.to_string()))?
            .to_string();

        let mut attributes = HashMap::new();
        for attr_result in e.attributes() {
            let attr = attr_result.map_err(|e| Error::Parse(format!("Attribute error: {}", e)))?;
            let key = reader
                .decoder()
                .decode(attr.key.as_ref())
                .map_err(|e| Error::Parse(e.to_string()))?
                .to_string();
            let value = attr
                .unescape_value()
                .map_err(|e| Error::Parse(e.to_string()))?
                .to_string();
            attributes.insert(key, value);
        }

        Ok(XmlElement::new(name, attributes))
    }

    /// Normalizes whitespace in text content, matching Java's behavior.
    ///
    /// The Java implementation:
    /// - Collapses consecutive whitespace to a single space
    /// - Tracks whether the previous text ended with whitespace
    /// - Only returns Some if there's non-whitespace content
    fn normalize_whitespace(&self, text: &str, previous: Option<&str>) -> Option<String> {
        let last_is_ws = previous.is_none_or(|p| p.ends_with(' '));
        let mut last_was_ws = last_is_ws;
        let mut has_non_ws = false;
        let mut result = String::new();

        for c in text.chars() {
            if c.is_whitespace() {
                if !last_was_ws {
                    result.push(' ');
                    last_was_ws = true;
                }
                // Skip additional whitespace
            } else {
                result.push(c);
                last_was_ws = false;
                has_non_ws = true;
            }
        }

        if has_non_ws {
            Some(result)
        } else {
            None
        }
    }
}

/// Parses XML from a file using a base node factory.
pub fn parse_file<P: AsRef<Path>>(path: P) -> Result<NodeRef> {
    let parser = XmlParser::new(super::BaseNodeFactory);
    parser.parse_file(path)
}

/// Parses XML from a string using a base node factory.
pub fn parse_str(xml: &str) -> Result<NodeRef> {
    let parser = XmlParser::new(super::BaseNodeFactory);
    parser.parse_str(xml)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::xml::BaseNodeFactory;

    #[test]
    fn test_parse_simple_xml() {
        let xml = r#"<root><child>text</child></root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        // Root should be $ROOT$ with one child (the actual root element)
        let root_borrowed = root.borrow();
        assert_eq!(root_borrowed.child_count(), 1);

        let root_content = root_borrowed.content().unwrap();
        if let XmlContent::Element(e) = root_content {
            assert_eq!(e.qname(), "$ROOT$");
        } else {
            panic!("Expected element");
        }

        // First child should be <root>
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();
        if let Some(XmlContent::Element(e)) = root_elem_borrowed.content() {
            assert_eq!(e.qname(), "root");
        } else {
            panic!("Expected element");
        }
    }

    #[test]
    fn test_parse_with_attributes() {
        let xml = r#"<root id="foo" class="bar">content</root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        if let Some(XmlContent::Element(e)) = root_elem_borrowed.content() {
            assert_eq!(e.qname(), "root");
            assert_eq!(e.attributes().get("id"), Some(&"foo".to_string()));
            assert_eq!(e.attributes().get("class"), Some(&"bar".to_string()));
        } else {
            panic!("Expected element");
        }
    }

    #[test]
    fn test_whitespace_normalization() {
        let xml = r#"<root>  hello   world  </root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        // Should have one text child with normalized whitespace
        assert_eq!(root_elem_borrowed.child_count(), 1);
        let text_node = root_elem_borrowed.children()[0].clone();
        let text_borrowed = text_node.borrow();

        if let Some(XmlContent::Text(t)) = text_borrowed.content() {
            let text: String = t.text().iter().collect();
            assert_eq!(text, "hello world");
        } else {
            panic!("Expected text node");
        }
    }

    #[test]
    fn test_empty_element() {
        let xml = r#"<root><empty /></root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        assert_eq!(root_elem_borrowed.child_count(), 1);
        let empty_elem = root_elem_borrowed.children()[0].clone();
        let empty_borrowed = empty_elem.borrow();

        if let Some(XmlContent::Element(e)) = empty_borrowed.content() {
            assert_eq!(e.qname(), "empty");
        } else {
            panic!("Expected element");
        }
        assert_eq!(empty_borrowed.child_count(), 0);
    }

    #[test]
    fn test_nested_elements() {
        let xml = r#"<a><b><c>deep</c></b></a>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        // Navigate: $ROOT$ -> a -> b -> c -> text
        let root_borrowed = root.borrow();
        let a = root_borrowed.children()[0].clone();
        let a_borrowed = a.borrow();
        let b = a_borrowed.children()[0].clone();
        let b_borrowed = b.borrow();
        let c = b_borrowed.children()[0].clone();
        let c_borrowed = c.borrow();
        let text = c_borrowed.children()[0].clone();
        let text_borrowed = text.borrow();

        if let Some(XmlContent::Text(t)) = text_borrowed.content() {
            let text_str: String = t.text().iter().collect();
            assert_eq!(text_str, "deep");
        } else {
            panic!("Expected text node");
        }
    }
}
