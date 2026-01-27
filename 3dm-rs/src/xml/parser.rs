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
use crate::node::{
    is_xmlns_attr, split_qname, ExpandedName, NamespaceContext, NodeInner, NodeRef, XmlComment,
    XmlContent, XmlElement, XmlProcessingInstruction, XmlText,
};

/// Whitespace handling mode during parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum WhitespaceMode {
    /// Normalize whitespace (collapse consecutive, trim).
    #[default]
    Normalize,
    /// Preserve all whitespace exactly as in source.
    Preserve,
}

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
        let mut ws_mode_stack: Vec<WhitespaceMode> = vec![WhitespaceMode::Normalize];
        let mut ns_context = NamespaceContext::new();
        let mut current_text: Option<String> = None;
        let mut buf = Vec::new();

        loop {
            match reader.read_event_into(&mut buf) {
                Ok(Event::Start(ref e)) => {
                    // Get current whitespace mode
                    let current_ws_mode =
                        *ws_mode_stack.last().unwrap_or(&WhitespaceMode::Normalize);

                    // Flush any accumulated text
                    if let Some(text) = current_text.take() {
                        let text_to_store = if current_ws_mode == WhitespaceMode::Preserve {
                            text // Keep as-is
                        } else {
                            text.trim().to_string() // Trim
                        };
                        if !text_to_store.is_empty() || current_ws_mode == WhitespaceMode::Preserve
                        {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(&text_to_store)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    // Push namespace scope BEFORE parsing element
                    ns_context.push_scope();

                    // Create the element node with namespace awareness
                    let (element, ws_mode_override) =
                        self.parse_element_with_ns(e, reader, &mut ns_context)?;
                    let node = self.factory.make_node(XmlContent::Element(element));

                    // Push whitespace mode (inherit or override)
                    let new_ws_mode = ws_mode_override.unwrap_or(current_ws_mode);
                    ws_mode_stack.push(new_ws_mode);

                    // Add to parent and push onto stack
                    if let Some(parent) = node_stack.last() {
                        NodeInner::add_child_to_ref(parent, node.clone());
                    }
                    node_stack.push(node);
                }
                Ok(Event::End(_)) => {
                    let current_ws_mode =
                        *ws_mode_stack.last().unwrap_or(&WhitespaceMode::Normalize);

                    // Flush any accumulated text
                    if let Some(text) = current_text.take() {
                        let text_to_store = if current_ws_mode == WhitespaceMode::Preserve {
                            text
                        } else {
                            text.trim().to_string()
                        };
                        if !text_to_store.is_empty() || current_ws_mode == WhitespaceMode::Preserve
                        {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(&text_to_store)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    // Pop from stacks
                    node_stack.pop();
                    ws_mode_stack.pop();
                    ns_context.pop_scope();
                }
                Ok(Event::Empty(ref e)) => {
                    // Self-closing tag - handle like Start + End (no children, so no scope push)
                    let current_ws_mode =
                        *ws_mode_stack.last().unwrap_or(&WhitespaceMode::Normalize);

                    // Flush any accumulated text
                    if let Some(text) = current_text.take() {
                        let text_to_store = if current_ws_mode == WhitespaceMode::Preserve {
                            text
                        } else {
                            text.trim().to_string()
                        };
                        if !text_to_store.is_empty() {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(&text_to_store)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    // Push/pop namespace scope for empty elements (may have xmlns declarations)
                    ns_context.push_scope();
                    let (element, _ws_mode_override) =
                        self.parse_element_with_ns(e, reader, &mut ns_context)?;
                    ns_context.pop_scope();
                    let node = self.factory.make_node(XmlContent::Element(element));

                    if let Some(parent) = node_stack.last() {
                        NodeInner::add_child_to_ref(parent, node);
                    }
                }
                Ok(Event::Text(e)) => {
                    let current_ws_mode =
                        *ws_mode_stack.last().unwrap_or(&WhitespaceMode::Normalize);
                    let raw =
                        std::str::from_utf8(e.as_ref()).map_err(|e| Error::Parse(e.to_string()))?;
                    let text = unescape(raw).map_err(|e| Error::Parse(e.to_string()))?;

                    if current_ws_mode == WhitespaceMode::Preserve {
                        // Preserve mode: keep text exactly as-is
                        current_text = Some(match current_text {
                            Some(mut existing) => {
                                existing.push_str(&text);
                                existing
                            }
                            None => text.to_string(),
                        });
                    } else {
                        // Normalize mode: use existing normalization
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
                }
                Ok(Event::CData(ref e)) => {
                    // CDATA sections preserve whitespace by their nature
                    let text = String::from_utf8_lossy(e.as_ref());
                    current_text = Some(match current_text {
                        Some(mut existing) => {
                            existing.push_str(&text);
                            existing
                        }
                        None => text.to_string(),
                    });
                }
                Ok(Event::Eof) => break,
                Ok(Event::Comment(ref e)) => {
                    let current_ws_mode =
                        *ws_mode_stack.last().unwrap_or(&WhitespaceMode::Normalize);

                    // Flush any accumulated text first
                    if let Some(text) = current_text.take() {
                        let text_to_store = if current_ws_mode == WhitespaceMode::Preserve {
                            text
                        } else {
                            text.trim().to_string()
                        };
                        if !text_to_store.is_empty() {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(&text_to_store)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    // Capture comments as nodes
                    let comment_text = String::from_utf8_lossy(e.as_ref()).to_string();
                    let comment_node = self
                        .factory
                        .make_node(XmlContent::Comment(XmlComment::new(&comment_text)));
                    if let Some(parent) = node_stack.last() {
                        NodeInner::add_child_to_ref(parent, comment_node);
                    }
                }
                Ok(Event::PI(ref e)) => {
                    let current_ws_mode =
                        *ws_mode_stack.last().unwrap_or(&WhitespaceMode::Normalize);

                    // Flush any accumulated text first (like Event::Start does)
                    if let Some(text) = current_text.take() {
                        let text_to_store = if current_ws_mode == WhitespaceMode::Preserve {
                            text
                        } else {
                            text.trim().to_string()
                        };
                        if !text_to_store.is_empty() || current_ws_mode == WhitespaceMode::Preserve
                        {
                            let text_node = self
                                .factory
                                .make_node(XmlContent::Text(XmlText::new(&text_to_store)));
                            if let Some(parent) = node_stack.last() {
                                NodeInner::add_child_to_ref(parent, text_node);
                            }
                        }
                    }

                    // Parse PI: <?target content?>
                    let pi_data = String::from_utf8_lossy(e.as_ref()).to_string();
                    // Use char_indices() for UTF-8 safety
                    let (target, content) = match pi_data
                        .char_indices()
                        .find(|(_, c)| c.is_whitespace())
                        .map(|(i, _)| i)
                    {
                        Some(pos) => (
                            pi_data[..pos].to_string(),
                            pi_data[pos..].trim().to_string(),
                        ),
                        None => (pi_data, String::new()),
                    };

                    let pi_node = self.factory.make_node(XmlContent::ProcessingInstruction(
                        XmlProcessingInstruction::new(&target, &content),
                    ));
                    if let Some(parent) = node_stack.last() {
                        NodeInner::add_child_to_ref(parent, pi_node);
                    }
                }
                Ok(Event::Decl(_)) => {
                    // Still ignore XML declaration
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

    /// Parses an element's name and attributes with namespace awareness.
    ///
    /// Returns the element and an optional whitespace mode override if `xml:space` is present.
    fn parse_element_with_ns<R: Read + std::io::BufRead>(
        &self,
        e: &BytesStart,
        reader: &Reader<R>,
        ns_context: &mut NamespaceContext,
    ) -> Result<(XmlElement, Option<WhitespaceMode>)> {
        let qname = reader
            .decoder()
            .decode(e.name().as_ref())
            .map_err(|e| Error::Parse(e.to_string()))?
            .to_string();

        let mut attributes = HashMap::new();
        let mut namespace_decls = HashMap::new();
        let mut ws_mode_override = None;

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

            // Check for xml:space attribute
            if key == "xml:space" {
                ws_mode_override = Some(match value.as_str() {
                    "preserve" => WhitespaceMode::Preserve,
                    _ => WhitespaceMode::Normalize,
                });
            }

            if is_xmlns_attr(&key) {
                // Namespace declaration
                let prefix = if key == "xmlns" {
                    String::new()
                } else {
                    key[6..].to_string() // "xmlns:prefix" -> "prefix"
                };
                ns_context.bind(&prefix, &value);
                namespace_decls.insert(prefix, value);
            } else {
                attributes.insert(key, value);
            }
        }

        // Resolve element name to expanded name
        let (prefix, local_name) = split_qname(&qname);
        let expanded_name = match prefix {
            Some(p) => ns_context
                .resolve(p)
                .map(|uri| ExpandedName::new(uri, local_name.to_string())),
            None => {
                if let Some(uri) = ns_context.default_namespace() {
                    if !uri.is_empty() {
                        Some(ExpandedName::new(uri, local_name.to_string()))
                    } else {
                        Some(ExpandedName::no_namespace(local_name.to_string()))
                    }
                } else {
                    Some(ExpandedName::no_namespace(local_name.to_string()))
                }
            }
        };

        Ok((
            XmlElement::new_with_namespace(qname, expanded_name, namespace_decls, attributes),
            ws_mode_override,
        ))
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

    #[test]
    fn test_whitespace_preservation() {
        // Test xml:space="preserve" attribute
        let xml = r#"<root xml:space="preserve">  hello   world  </root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        // Should have one text child with preserved whitespace
        assert_eq!(root_elem_borrowed.child_count(), 1);
        let text_node = root_elem_borrowed.children()[0].clone();
        let text_borrowed = text_node.borrow();

        if let Some(XmlContent::Text(t)) = text_borrowed.content() {
            let text: String = t.text().iter().collect();
            // Whitespace should be preserved exactly
            assert_eq!(text, "  hello   world  ");
        } else {
            panic!("Expected text node");
        }
    }

    #[test]
    fn test_whitespace_preservation_inheritance() {
        // Test that xml:space="preserve" is inherited by child elements
        let xml = r#"<root xml:space="preserve"><child>  text  </child></root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        let child_elem = root_elem_borrowed.children()[0].clone();
        let child_borrowed = child_elem.borrow();

        assert_eq!(child_borrowed.child_count(), 1);
        let text_node = child_borrowed.children()[0].clone();
        let text_borrowed = text_node.borrow();

        if let Some(XmlContent::Text(t)) = text_borrowed.content() {
            let text: String = t.text().iter().collect();
            // Whitespace should be preserved in child element
            assert_eq!(text, "  text  ");
        } else {
            panic!("Expected text node");
        }
    }

    #[test]
    fn test_whitespace_preservation_override() {
        // Test that xml:space="default" overrides inherited preserve mode
        let xml =
            r#"<root xml:space="preserve"><child xml:space="default">  text  </child></root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        let child_elem = root_elem_borrowed.children()[0].clone();
        let child_borrowed = child_elem.borrow();

        assert_eq!(child_borrowed.child_count(), 1);
        let text_node = child_borrowed.children()[0].clone();
        let text_borrowed = text_node.borrow();

        if let Some(XmlContent::Text(t)) = text_borrowed.content() {
            let text: String = t.text().iter().collect();
            // Whitespace should be normalized in override element
            assert_eq!(text, "text");
        } else {
            panic!("Expected text node");
        }
    }

    #[test]
    fn test_namespace_parsing() {
        let xml = r#"<root xmlns="http://example.com" xmlns:ns="http://ns.example.com"><ns:child /></root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        if let Some(XmlContent::Element(e)) = root_elem_borrowed.content() {
            assert_eq!(e.qname(), "root");
            // Should have namespace declarations separated from attributes
            assert_eq!(
                e.namespace_decls().get(""),
                Some(&"http://example.com".to_string())
            );
            assert_eq!(
                e.namespace_decls().get("ns"),
                Some(&"http://ns.example.com".to_string())
            );
            assert!(e.attributes().is_empty());
            // Should have expanded name with default namespace
            let expanded = e.expanded_name().expect("should have expanded name");
            assert_eq!(expanded.namespace_uri.as_ref(), "http://example.com");
            assert_eq!(expanded.local_name, "root");
        } else {
            panic!("Expected element");
        }

        // Check child has resolved prefix
        let child = root_elem_borrowed.children()[0].clone();
        let child_borrowed = child.borrow();
        if let Some(XmlContent::Element(e)) = child_borrowed.content() {
            assert_eq!(e.qname(), "ns:child");
            let expanded = e.expanded_name().expect("should have expanded name");
            assert_eq!(expanded.namespace_uri.as_ref(), "http://ns.example.com");
            assert_eq!(expanded.local_name, "child");
        } else {
            panic!("Expected element");
        }
    }

    #[test]
    fn test_comment_flushes_text() {
        // Text before a comment should be flushed as a text node before the comment
        let xml = r#"<root>hello<!-- comment -->world</root>"#;
        let parser = XmlParser::new(BaseNodeFactory);
        let root = parser.parse_str(xml).unwrap();

        let root_borrowed = root.borrow();
        let root_elem = root_borrowed.children()[0].clone();
        let root_elem_borrowed = root_elem.borrow();

        // Should have 3 children: text("hello"), comment, text("world")
        assert_eq!(root_elem_borrowed.child_count(), 3);

        // First child should be text "hello"
        let first = root_elem_borrowed.children()[0].clone();
        let first_borrowed = first.borrow();
        if let Some(XmlContent::Text(t)) = first_borrowed.content() {
            let text: String = t.text().iter().collect();
            assert_eq!(text, "hello");
        } else {
            panic!("Expected text node, got {:?}", first_borrowed.content());
        }

        // Second child should be comment
        let second = root_elem_borrowed.children()[1].clone();
        let second_borrowed = second.borrow();
        assert!(matches!(
            second_borrowed.content(),
            Some(XmlContent::Comment(_))
        ));

        // Third child should be text "world"
        let third = root_elem_borrowed.children()[2].clone();
        let third_borrowed = third.borrow();
        if let Some(XmlContent::Text(t)) = third_borrowed.content() {
            let text: String = t.text().iter().collect();
            assert_eq!(text, "world");
        } else {
            panic!("Expected text node");
        }
    }
}
