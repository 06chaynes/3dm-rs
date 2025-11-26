//! XML printer that outputs node trees.
//!
//! This printer outputs XML that matches the Java implementation's format
//! for byte-for-byte compatibility.

use std::io::Write;

use crate::node::{NodeRef, XmlContent};

/// Options for XML printing.
#[derive(Debug, Clone, Default)]
pub struct XmlPrinterOptions {
    /// Whether to pretty-print with indentation.
    pub pretty_print: bool,
}

/// XML printer that outputs node trees.
pub struct XmlPrinter<W: Write> {
    writer: W,
    options: XmlPrinterOptions,
    indent: usize,
    /// State tracking for proper tag closing
    state: PrintState,
    /// Stack of "has content" flags for each element level
    content_stack: Vec<bool>,
    /// Whether current element has content
    has_content: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum PrintState {
    Initial,
    AfterTag,
    AfterChars,
}

impl<W: Write> XmlPrinter<W> {
    /// Creates a new XML printer.
    pub fn new(writer: W) -> Self {
        Self::with_options(writer, XmlPrinterOptions::default())
    }

    /// Creates a new XML printer with the given options.
    pub fn with_options(writer: W, options: XmlPrinterOptions) -> Self {
        XmlPrinter {
            writer,
            options,
            indent: 0,
            state: PrintState::Initial,
            content_stack: Vec::new(),
            has_content: true, // Start as true (like Java's HAS_CONTENT at document start)
        }
    }

    /// Prints a node tree to the output.
    pub fn print(&mut self, root: &NodeRef) -> std::io::Result<()> {
        self.print_node(root, false)
    }

    /// Prints a node tree as a fragment (no XML declaration).
    pub fn print_fragment(&mut self, root: &NodeRef) -> std::io::Result<()> {
        self.print_node(root, true)
    }

    fn print_node(&mut self, node: &NodeRef, fragment: bool) -> std::io::Result<()> {
        let borrowed = node.borrow();
        let content = borrowed.content();

        if !fragment {
            self.start_document()?;
        }

        match content {
            Some(XmlContent::Text(text)) => {
                let text_str: String = text.text().iter().collect();
                self.characters(&text_str)?;
            }
            Some(XmlContent::Comment(comment)) => {
                let comment_text: String = comment.text().iter().collect();
                self.print_with_nl(&format!(
                    "{}<!-- {} -->",
                    Self::indent_str(self.indent),
                    comment_text
                ))?;
            }
            Some(XmlContent::Element(element)) => {
                let qname = element.qname();

                // Skip the synthetic $ROOT$ element but print its children
                if qname == "$ROOT$" {
                    for child in borrowed.children() {
                        self.print_node(child, true)?;
                    }
                } else {
                    self.start_element(qname, element.attributes())?;

                    for child in borrowed.children() {
                        self.print_node(child, true)?;
                    }

                    self.end_element(qname)?;
                }
            }
            None => {}
        }

        if !fragment {
            self.end_document()?;
        }

        Ok(())
    }

    fn start_document(&mut self) -> std::io::Result<()> {
        self.has_content = true;
        write!(self.writer, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>")?;
        if self.options.pretty_print {
            writeln!(self.writer)?;
        }
        self.state = PrintState::AfterTag;
        Ok(())
    }

    fn end_document(&mut self) -> std::io::Result<()> {
        if !self.options.pretty_print {
            writeln!(self.writer)?;
        }
        self.writer.flush()
    }

    fn start_element(
        &mut self,
        qname: &str,
        attrs: &std::collections::HashMap<String, String>,
    ) -> std::io::Result<()> {
        // Close previous unclosed tag if needed
        if !self.has_content {
            self.print_with_nl(">")?;
            self.has_content = true;
        }

        // In non-pretty mode, add newline between tags
        if self.state == PrintState::AfterTag && !self.options.pretty_print {
            writeln!(self.writer)?;
        }

        // Build opening tag
        let mut tag = String::new();
        tag.push('<');
        tag.push_str(qname);

        // Add attributes (sorted for deterministic output)
        let mut attr_names: Vec<&String> = attrs.keys().collect();
        attr_names.sort();
        for name in attr_names {
            let value = &attrs[name];
            tag.push(' ');
            tag.push_str(name);
            tag.push_str("=\"");
            tag.push_str(&to_entities(value));
            tag.push('"');
        }

        // Print with indentation if pretty printing
        if self.options.pretty_print {
            write!(self.writer, "{}", &Self::indent_str(self.indent))?;
        }
        write!(self.writer, "{}", tag)?;

        // Push state and increment indent
        self.content_stack.push(self.has_content);
        self.has_content = false; // Reset for new element
        self.indent += 1;
        self.state = PrintState::AfterTag;

        Ok(())
    }

    fn end_element(&mut self, qname: &str) -> std::io::Result<()> {
        self.indent -= 1;

        if !self.has_content {
            // No content - use self-closing tag
            self.print_with_nl(" />")?;
        } else {
            // Has content - print closing tag
            if self.state == PrintState::AfterTag && !self.options.pretty_print {
                writeln!(self.writer)?;
            }

            let close_tag = format!("</{}>", qname);
            if self.options.pretty_print {
                write!(self.writer, "{}", &Self::indent_str(self.indent))?;
            }
            self.print_with_nl(&close_tag)?;
        }

        // Pop state
        self.has_content = self.content_stack.pop().unwrap_or(true);
        self.state = PrintState::AfterTag;

        Ok(())
    }

    fn characters(&mut self, text: &str) -> std::io::Result<()> {
        self.state = PrintState::AfterChars;

        // Close previous unclosed tag if needed
        if !self.has_content {
            self.print_with_nl(">")?;
        }
        self.has_content = true;

        if text.is_empty() {
            return Ok(());
        }

        let encoded = to_entities(text);
        self.print_with_nl(&encoded)
    }

    fn print_with_nl(&mut self, s: &str) -> std::io::Result<()> {
        if self.options.pretty_print {
            writeln!(self.writer, "{}", s)
        } else {
            write!(self.writer, "{}", s)
        }
    }

    fn indent_str(level: usize) -> String {
        "  ".repeat(level)
    }
}

/// Converts special characters to XML entities.
fn to_entities(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => result.push_str("&amp;"),
            '<' => result.push_str("&lt;"),
            '>' => result.push_str("&gt;"),
            '\'' => result.push_str("&apos;"),
            '"' => result.push_str("&quot;"),
            _ => result.push(c),
        }
    }
    result
}

/// Prints a node tree to a string.
pub fn print_to_string(root: &NodeRef) -> std::io::Result<String> {
    let mut output = Vec::new();
    {
        let mut printer = XmlPrinter::new(&mut output);
        printer.print(root)?;
    }
    Ok(String::from_utf8_lossy(&output).to_string())
}

/// Prints a node tree to a string with pretty printing.
pub fn print_to_string_pretty(root: &NodeRef) -> std::io::Result<String> {
    let mut output = Vec::new();
    {
        let options = XmlPrinterOptions { pretty_print: true };
        let mut printer = XmlPrinter::with_options(&mut output, options);
        printer.print(root)?;
    }
    Ok(String::from_utf8_lossy(&output).to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::xml::parse_str;

    #[test]
    fn test_print_simple() {
        let xml = r#"<root>text</root>"#;
        let root = parse_str(xml).unwrap();
        let output = print_to_string(&root).unwrap();

        // Should have XML declaration and the element
        assert!(output.starts_with("<?xml version=\"1.0\" encoding=\"UTF-8\"?>"));
        assert!(output.contains("<root>"));
        assert!(output.contains("text"));
        assert!(output.contains("</root>"));
    }

    #[test]
    fn test_print_with_attributes() {
        let xml = r#"<root id="foo">content</root>"#;
        let root = parse_str(xml).unwrap();
        let output = print_to_string(&root).unwrap();

        assert!(output.contains(r#"id="foo""#));
        assert!(output.contains("content"));
    }

    #[test]
    fn test_print_empty_element() {
        let xml = r#"<root><empty /></root>"#;
        let root = parse_str(xml).unwrap();
        let output = print_to_string(&root).unwrap();

        // Empty element should be self-closing
        assert!(output.contains("<empty />"));
    }

    #[test]
    fn test_entity_encoding() {
        let xml = r#"<root attr="&amp;&lt;&gt;">&amp;&lt;&gt;</root>"#;
        let root = parse_str(xml).unwrap();
        let output = print_to_string(&root).unwrap();

        // Entities should be preserved
        assert!(output.contains("&amp;"));
        assert!(output.contains("&lt;"));
        assert!(output.contains("&gt;"));
    }

    #[test]
    fn test_print_nested() {
        let xml = r#"<a><b><c>deep</c></b></a>"#;
        let root = parse_str(xml).unwrap();
        let output = print_to_string(&root).unwrap();

        assert!(output.contains("<a>"));
        assert!(output.contains("<b>"));
        assert!(output.contains("<c>"));
        assert!(output.contains("deep"));
        assert!(output.contains("</c>"));
        assert!(output.contains("</b>"));
        assert!(output.contains("</a>"));
    }

    #[test]
    fn test_pretty_print() {
        let xml = r#"<root><child>text</child></root>"#;
        let root = parse_str(xml).unwrap();
        let output = print_to_string_pretty(&root).unwrap();

        // Pretty print should have indentation
        assert!(output.contains(" <child>"));
    }

    /// Helper to compare tree structure (element names and text content)
    fn trees_equal(a: &NodeRef, b: &NodeRef) -> bool {
        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        // Compare content
        match (a_borrowed.content(), b_borrowed.content()) {
            (Some(XmlContent::Element(ea)), Some(XmlContent::Element(eb))) => {
                if ea.qname() != eb.qname() {
                    return false;
                }
                // Compare attributes
                if ea.attributes() != eb.attributes() {
                    return false;
                }
            }
            (Some(XmlContent::Text(ta)), Some(XmlContent::Text(tb))) => {
                let text_a: String = ta.text().iter().collect();
                let text_b: String = tb.text().iter().collect();
                if text_a != text_b {
                    return false;
                }
            }
            (None, None) => {}
            _ => return false,
        }

        // Compare children count
        if a_borrowed.child_count() != b_borrowed.child_count() {
            return false;
        }

        // Compare children recursively
        for (child_a, child_b) in a_borrowed
            .children()
            .iter()
            .zip(b_borrowed.children().iter())
        {
            if !trees_equal(child_a, child_b) {
                return false;
            }
        }

        true
    }

    #[test]
    fn test_round_trip_simple() {
        let xml = r#"<root>text</root>"#;
        let tree1 = parse_str(xml).unwrap();
        let output1 = print_to_string(&tree1).unwrap();
        let tree2 = parse_str(&output1).unwrap();

        assert!(trees_equal(&tree1, &tree2));
    }

    #[test]
    fn test_round_trip_with_attributes() {
        let xml = r#"<root id="foo" class="bar"><child name="test">content</child></root>"#;
        let tree1 = parse_str(xml).unwrap();
        let output1 = print_to_string(&tree1).unwrap();
        let tree2 = parse_str(&output1).unwrap();

        assert!(trees_equal(&tree1, &tree2));
    }

    #[test]
    fn test_round_trip_nested() {
        let xml = r#"<a><b><c><d>deep text</d></c></b></a>"#;
        let tree1 = parse_str(xml).unwrap();
        let output1 = print_to_string(&tree1).unwrap();
        let tree2 = parse_str(&output1).unwrap();

        assert!(trees_equal(&tree1, &tree2));
    }

    #[test]
    fn test_round_trip_mixed_content() {
        let xml = r#"<root>text1<child>inner</child>text2</root>"#;
        let tree1 = parse_str(xml).unwrap();
        let output1 = print_to_string(&tree1).unwrap();
        let tree2 = parse_str(&output1).unwrap();

        assert!(trees_equal(&tree1, &tree2));
    }

    #[test]
    fn test_round_trip_empty_elements() {
        let xml = r#"<root><empty /><also-empty></also-empty></root>"#;
        let tree1 = parse_str(xml).unwrap();
        let output1 = print_to_string(&tree1).unwrap();
        let tree2 = parse_str(&output1).unwrap();

        assert!(trees_equal(&tree1, &tree2));
    }

    #[test]
    fn test_round_trip_entities() {
        let xml =
            r#"<root attr="&amp;&lt;&gt;&apos;&quot;">text with &amp; and &lt;tag&gt;</root>"#;
        let tree1 = parse_str(xml).unwrap();
        let output1 = print_to_string(&tree1).unwrap();
        let tree2 = parse_str(&output1).unwrap();

        assert!(trees_equal(&tree1, &tree2));
    }

    #[test]
    fn test_double_round_trip() {
        // Parse -> Print -> Parse -> Print should produce identical output
        let xml = r#"<doc><section id="s1"><para>First paragraph.</para><para>Second paragraph.</para></section></doc>"#;
        let tree1 = parse_str(xml).unwrap();
        let output1 = print_to_string(&tree1).unwrap();
        let tree2 = parse_str(&output1).unwrap();
        let output2 = print_to_string(&tree2).unwrap();

        // The second print should produce identical output
        assert_eq!(output1, output2);
    }
}
