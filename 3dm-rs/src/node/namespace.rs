//! Namespace handling for XML elements.

use std::collections::HashMap;
use std::rc::Rc;

/// Represents an expanded XML name (namespace URI + local name).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExpandedName {
    /// The namespace URI (empty string for no namespace).
    pub namespace_uri: Rc<str>,
    /// The local part of the name (without prefix).
    pub local_name: String,
}

impl ExpandedName {
    /// Creates a new expanded name with a namespace.
    pub fn new(uri: impl Into<Rc<str>>, local: impl Into<String>) -> Self {
        Self {
            namespace_uri: uri.into(),
            local_name: local.into(),
        }
    }

    /// Creates an expanded name with no namespace.
    pub fn no_namespace(local: impl Into<String>) -> Self {
        Self {
            namespace_uri: "".into(),
            local_name: local.into(),
        }
    }
}

/// Tracks namespace bindings during parsing.
pub struct NamespaceContext {
    /// URI interning cache for memory efficiency.
    uri_cache: HashMap<String, Rc<str>>,
    /// Stack of scopes, each containing prefix -> URI bindings.
    scopes: Vec<HashMap<String, Rc<str>>>,
}

impl Default for NamespaceContext {
    fn default() -> Self {
        Self::new()
    }
}

impl NamespaceContext {
    /// Creates a new namespace context with XML namespace pre-bound.
    pub fn new() -> Self {
        let mut ctx = NamespaceContext {
            uri_cache: HashMap::new(),
            scopes: vec![HashMap::new()],
        };
        // xml prefix is always bound
        ctx.bind("xml", "http://www.w3.org/XML/1998/namespace");
        ctx
    }

    /// Pushes a new scope for entering an element.
    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Pops the current scope when leaving an element.
    pub fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    /// Binds a prefix to a URI in the current scope.
    pub fn bind(&mut self, prefix: &str, uri: &str) {
        let uri_rc = self.intern_uri(uri);
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(prefix.to_string(), uri_rc);
        }
    }

    /// Resolves a prefix to its URI, searching from innermost scope.
    pub fn resolve(&self, prefix: &str) -> Option<Rc<str>> {
        for scope in self.scopes.iter().rev() {
            if let Some(uri) = scope.get(prefix) {
                return Some(uri.clone());
            }
        }
        None
    }

    /// Returns the default namespace (empty prefix binding).
    pub fn default_namespace(&self) -> Option<Rc<str>> {
        self.resolve("")
    }

    /// Interns a URI string for memory efficiency.
    pub fn intern_uri(&mut self, uri: &str) -> Rc<str> {
        if let Some(cached) = self.uri_cache.get(uri) {
            cached.clone()
        } else {
            let rc: Rc<str> = uri.into();
            self.uri_cache.insert(uri.to_string(), rc.clone());
            rc
        }
    }
}

/// Splits a qualified name into prefix and local name.
///
/// Returns (Some(prefix), local) for "prefix:local"
/// Returns (None, name) for "name" without prefix
pub fn split_qname(qname: &str) -> (Option<&str>, &str) {
    if let Some(pos) = qname.find(':') {
        (Some(&qname[..pos]), &qname[pos + 1..])
    } else {
        (None, qname)
    }
}

/// Checks if an attribute name is a namespace declaration.
pub fn is_xmlns_attr(name: &str) -> bool {
    name == "xmlns" || name.starts_with("xmlns:")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_qname() {
        assert_eq!(split_qname("svg:rect"), (Some("svg"), "rect"));
        assert_eq!(split_qname("rect"), (None, "rect"));
        assert_eq!(split_qname("ns:foo:bar"), (Some("ns"), "foo:bar"));
    }

    #[test]
    fn test_namespace_context() {
        let mut ctx = NamespaceContext::new();
        ctx.push_scope();
        ctx.bind("svg", "http://www.w3.org/2000/svg");

        assert!(ctx.resolve("svg").is_some());
        assert_eq!(
            ctx.resolve("svg").unwrap().as_ref(),
            "http://www.w3.org/2000/svg"
        );

        ctx.pop_scope();
        assert!(ctx.resolve("svg").is_none());
    }

    #[test]
    fn test_is_xmlns() {
        assert!(is_xmlns_attr("xmlns"));
        assert!(is_xmlns_attr("xmlns:svg"));
        assert!(!is_xmlns_attr("xml:space"));
        assert!(!is_xmlns_attr("href"));
    }

    #[test]
    fn test_default_namespace() {
        let mut ctx = NamespaceContext::new();
        assert!(ctx.default_namespace().is_none());

        ctx.push_scope();
        ctx.bind("", "http://www.w3.org/1999/xhtml");
        assert_eq!(
            ctx.default_namespace().unwrap().as_ref(),
            "http://www.w3.org/1999/xhtml"
        );

        ctx.pop_scope();
        assert!(ctx.default_namespace().is_none());
    }

    #[test]
    fn test_xml_prefix_always_bound() {
        let ctx = NamespaceContext::new();
        assert_eq!(
            ctx.resolve("xml").unwrap().as_ref(),
            "http://www.w3.org/XML/1998/namespace"
        );
    }

    #[test]
    fn test_scope_inheritance() {
        let mut ctx = NamespaceContext::new();
        ctx.push_scope();
        ctx.bind("a", "http://example.com/a");

        ctx.push_scope();
        ctx.bind("b", "http://example.com/b");

        // Both should be visible
        assert!(ctx.resolve("a").is_some());
        assert!(ctx.resolve("b").is_some());

        ctx.pop_scope();
        // Only a should remain
        assert!(ctx.resolve("a").is_some());
        assert!(ctx.resolve("b").is_none());
    }
}
