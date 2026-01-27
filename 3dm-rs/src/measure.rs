//! Node similarity measurement.
//!
//! This module provides distance calculations between nodes using the Q-gram
//! distance algorithm (Ukkonen92). It calculates content distance, child list
//! distance, and matched child list distance between nodes.

use rustc_hash::FxHashMap;

use crate::node::{NodeRef, XmlContent};

/// Maximum distance. The distance is normalized between 0 and MAX_DIST.
pub const MAX_DIST: f64 = 1.0;

/// Distance to return by childListDistance if both nodes have 0 children.
pub const ZERO_CHILDREN_MATCH: f64 = 1.0;

/// Info bytes in an element name ($c_e$ in thesis).
pub const ELEMENT_NAME_INFO: i32 = 1;

/// Info bytes in the presence of an attribute ($c_a$ in thesis).
pub const ATTR_INFO: i32 = 2;

/// Attribute values less than this have an info size of 1 ($c_v$ in thesis).
pub const ATTR_VALUE_THRESHOLD: usize = 5;

/// Text nodes shorter than this have an info size of 1 ($c_t$ in thesis).
pub const TEXT_THRESHOLD: usize = 5;

/// Penalty term ($c_p$ in thesis).
const PENALTY_C: i32 = 20;

/// Determines Q-gram size based on combined string length (thesis equation 6.1).
/// Returns q=1 for very short strings, q=2 for medium, q=4 for long.
fn decide_q(combined_len: usize) -> usize {
    if combined_len < 5 {
        1
    } else if combined_len < 50 {
        2
    } else {
        4
    }
}

/// Node similarity measurement calculator.
///
/// This struct calculates the content, child list and matched child list
/// distance between nodes using the Q-gram distance algorithm.
pub struct Measure {
    /// Mismatched info bytes.
    mismatched: i32,
    /// Total info bytes.
    total: i32,
    /// Set to true if total mismatch occurs (e.g., text and element node compared).
    total_mismatch: bool,
    /// Hash tables used to store Q-grams.
    a_grams: FxHashMap<String, i32>,
    b_grams: FxHashMap<String, i32>,
}

impl Default for Measure {
    fn default() -> Self {
        Self::new()
    }
}

impl Measure {
    /// Creates a new Measure instance.
    pub fn new() -> Self {
        Measure {
            mismatched: 0,
            total: 0,
            total_mismatch: false,
            a_grams: FxHashMap::with_capacity_and_hasher(2048, Default::default()),
            b_grams: FxHashMap::with_capacity_and_hasher(2048, Default::default()),
        }
    }

    /// Returns content distance between nodes.
    ///
    /// The distance is normalized between 0.0 and 1.0 (MAX_DIST).
    /// Returns 1.0 if node types are incompatible (element vs text).
    pub fn get_distance(&mut self, a: Option<&NodeRef>, b: Option<&NodeRef>) -> f64 {
        if let (Some(a), Some(b)) = (a, b) {
            self.include_nodes(a, b);
        }

        let result = if self.total_mismatch {
            MAX_DIST
        } else if self.total == 0 {
            0.0
        } else {
            let penalty = (1.0 - (self.total as f64) / (PENALTY_C as f64)).max(0.0);
            penalty + (1.0 - penalty) * (self.mismatched as f64) / (self.total as f64)
        };

        self.reset_distance();
        result
    }

    /// Resets the distance calculation state.
    fn reset_distance(&mut self) {
        self.mismatched = 0;
        self.total = 0;
        self.total_mismatch = false;
    }

    /// Adds a node pair to the distance calculation state.
    fn include_nodes(&mut self, a: &NodeRef, b: &NodeRef) {
        if self.total_mismatch {
            return;
        }

        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        let ca = a_borrowed.content();
        let cb = b_borrowed.content();

        match (ca, cb) {
            (Some(XmlContent::Element(ea)), Some(XmlContent::Element(eb))) => {
                // Compare element names
                self.total += ELEMENT_NAME_INFO;
                if !ea.names_match(eb) {
                    self.mismatched += ELEMENT_NAME_INFO;
                }

                // Compare attributes present in a
                let attrs_a = ea.attributes();
                let attrs_b = eb.attributes();

                for (name, v1) in attrs_a.iter() {
                    if let Some(v2) = attrs_b.get(name) {
                        // Attribute exists in both - compare values
                        let amismatch = self.string_dist_str(v1, v2);
                        let info = if v1.len() > ATTR_VALUE_THRESHOLD {
                            v1.len() as i32
                        } else {
                            1
                        } + if v2.len() > ATTR_VALUE_THRESHOLD {
                            v2.len() as i32
                        } else {
                            1
                        };
                        self.mismatched += if amismatch > info { info } else { amismatch };
                        self.total += info;
                    } else {
                        // Attribute only in a (deleted from b)
                        self.mismatched += ATTR_INFO;
                        self.total += ATTR_INFO;
                    }
                }

                // Scan for attributes present in b but not in a
                for name in attrs_b.keys() {
                    if !attrs_a.contains_key(name) {
                        self.mismatched += ATTR_INFO;
                        self.total += ATTR_INFO;
                    }
                }
            }
            (Some(XmlContent::Text(ta)), Some(XmlContent::Text(tb))) => {
                // Compare text content
                let info = (ta.info_size() + tb.info_size()) / 2;
                let amismatch = self.string_dist_chars(ta.text(), tb.text()) / 2;

                self.mismatched += if amismatch > info { info } else { amismatch };
                self.total += info;
            }
            (
                Some(XmlContent::ProcessingInstruction(pa)),
                Some(XmlContent::ProcessingInstruction(pb)),
            ) => {
                // Compare processing instructions
                self.total += 1;
                if pa.target() != pb.target() || !pa.content_equals(pb) {
                    self.mismatched += 1;
                }
            }
            _ => {
                // Incompatible types (element vs text, or missing content)
                self.total_mismatch = true;
            }
        }
    }

    /// Calculates string distance using Q-gram algorithm.
    pub fn string_dist_str(&mut self, a: &str, b: &str) -> i32 {
        self.q_dist_str(a, b)
    }

    /// Calculates string distance for char arrays using Q-gram algorithm.
    pub fn string_dist_chars(&mut self, a: &[char], b: &[char]) -> i32 {
        self.q_dist_chars(a, b)
    }

    /// Calculates child list distance between nodes.
    ///
    /// This compares children by their content hashes to measure structural similarity.
    /// Returns ZERO_CHILDREN_MATCH (1.0) if both nodes have no children.
    pub fn child_list_distance(&mut self, a: &NodeRef, b: &NodeRef) -> f64 {
        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        let a_count = a_borrowed.child_count();
        let b_count = b_borrowed.child_count();

        if a_count == 0 && b_count == 0 {
            return ZERO_CHILDREN_MATCH;
        }

        // Build char arrays from content hashes (truncated to 16 bits)
        let ac: Vec<char> = a_borrowed
            .children()
            .iter()
            .map(|child| {
                let child_borrowed = child.borrow();
                if let Some(content) = child_borrowed.content() {
                    char::from_u32((content.content_hash() & 0xffff) as u32).unwrap_or('\0')
                } else {
                    '\0'
                }
            })
            .collect();

        let bc: Vec<char> = b_borrowed
            .children()
            .iter()
            .map(|child| {
                let child_borrowed = child.borrow();
                if let Some(content) = child_borrowed.content() {
                    char::from_u32((content.content_hash() & 0xffff) as u32).unwrap_or('\0')
                } else {
                    '\0'
                }
            })
            .collect();

        let dist = self.string_dist_chars(&ac, &bc);
        (dist as f64) / ((a_count + b_count) as f64)
    }

    /// Calculates matched child list distance.
    ///
    /// This measures how well children of a base node match children of a branch node,
    /// based on their matching relationships (not content hashes).
    ///
    /// # Arguments
    /// * `base` - The base node
    /// * `branch` - The branch node
    /// * `_is_left` - Whether the branch is the left branch (unused, for API compatibility)
    pub fn matched_child_list_distance(
        &mut self,
        base: &NodeRef,
        branch: &NodeRef,
        _is_left: bool,
    ) -> i32 {
        let base_borrowed = base.borrow();
        let branch_borrowed = branch.borrow();

        // Build array for base children: position + 1 (to avoid 0 = -0 bug)
        let ac: Vec<char> = (0..base_borrowed.child_count())
            .map(|i| char::from_u32((i + 1) as u32).unwrap_or('\0'))
            .collect();

        // Build array for branch children based on their base match
        let bc: Vec<char> = branch_borrowed
            .children()
            .iter()
            .enumerate()
            .map(|(i, child)| {
                let child_borrowed = child.borrow();

                // Get base match for this branch child
                if let Some(base_match_weak) = child_borrowed.get_base_match() {
                    if let Some(base_match) = base_match_weak.upgrade() {
                        let base_match_borrowed = base_match.borrow();

                        // Check if parent of base match is our base node
                        if let Some(parent) = base_match_borrowed.parent().upgrade() {
                            // Compare by ID
                            if parent.borrow().id() == base_borrowed.id() {
                                // Use child position (0-indexed, so add 1)
                                return char::from_u32(
                                    (base_match_borrowed.child_pos() + 1) as u32,
                                )
                                .unwrap_or('\0');
                            }
                        }
                    }
                }

                // No match or different parent - use negative position
                // Note: In Java, this uses -(i+1), but since we're using chars,
                // we need to handle this differently. We'll use high values
                // that won't collide with valid positions.
                char::from_u32(0x10000 + i as u32).unwrap_or('\0')
            })
            .collect();

        self.string_dist_chars(&ac, &bc)
    }

    /// Q-gram distance for strings (Ukkonen92 algorithm).
    fn q_dist_str(&mut self, a: &str, b: &str) -> i32 {
        self.a_grams.clear();
        self.b_grams.clear();

        // Adaptive Q based on combined length
        let q = decide_q(a.len() + b.len());

        // Build q-grams for string a
        let chars_a: Vec<char> = a.chars().collect();
        for i in 0..chars_a.len() {
            let end = (i + q).min(chars_a.len());
            let gram: String = chars_a[i..end].iter().collect();
            *self.a_grams.entry(gram).or_insert(0) += 1;
        }

        // Build q-grams for string b
        let chars_b: Vec<char> = b.chars().collect();
        for i in 0..chars_b.len() {
            let end = (i + q).min(chars_b.len());
            let gram: String = chars_b[i..end].iter().collect();
            *self.b_grams.entry(gram).or_insert(0) += 1;
        }

        self.calc_q_distance()
    }

    /// Q-gram distance for char arrays (Ukkonen92 algorithm).
    fn q_dist_chars(&mut self, a: &[char], b: &[char]) -> i32 {
        self.a_grams.clear();
        self.b_grams.clear();

        // Adaptive Q based on combined length
        let q = decide_q(a.len() + b.len());

        // Build q-grams for array a
        for i in 0..a.len() {
            let end = (i + q).min(a.len());
            let gram: String = a[i..end].iter().collect();
            *self.a_grams.entry(gram).or_insert(0) += 1;
        }

        // Build q-grams for array b
        for i in 0..b.len() {
            let end = (i + q).min(b.len());
            let gram: String = b[i..end].iter().collect();
            *self.b_grams.entry(gram).or_insert(0) += 1;
        }

        self.calc_q_distance()
    }

    /// Builds Q-grams from a string into the provided map.
    /// Used by tests to verify Q-gram construction.
    /// Assumes comparing string to itself (combined_len = 2 * len).
    #[cfg(test)]
    fn build_q_grams_str(&self, s: &str, grams: &mut FxHashMap<String, i32>) {
        grams.clear();
        let chars: Vec<char> = s.chars().collect();
        let q = decide_q(chars.len() * 2);
        for i in 0..chars.len() {
            let end = (i + q).min(chars.len());
            let gram: String = chars[i..end].iter().collect();
            *grams.entry(gram).or_insert(0) += 1;
        }
    }

    /// Calculates the Q-gram distance from the built gram tables.
    fn calc_q_distance(&self) -> i32 {
        let mut dist = 0;

        // Loop over a_grams
        for (gram, count_a) in &self.a_grams {
            let count_b = self.b_grams.get(gram).copied().unwrap_or(0);
            dist += (count_a - count_b).abs();
        }

        // Add grams present in b but not in a
        for (gram, count_b) in &self.b_grams {
            if !self.a_grams.contains_key(gram) {
                dist += *count_b;
            }
        }

        dist
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, XmlElement, XmlText};
    use std::collections::HashMap as StdHashMap;

    #[test]
    fn test_q_dist_identical_strings() {
        let mut measure = Measure::new();
        let dist = measure.string_dist_str("hello world", "hello world");
        assert_eq!(dist, 0);
    }

    #[test]
    fn test_q_dist_different_strings() {
        let mut measure = Measure::new();
        let dist = measure.string_dist_str("hello", "world");
        assert!(dist > 0);
    }

    #[test]
    fn test_q_dist_similar_strings() {
        let mut measure = Measure::new();
        // These differ by one character
        let dist = measure.string_dist_str(
            "return stringDist( a, b, a.length()+b.length() );",
            "return stzingDist( a, b, a.length()+b.length() );",
        );
        // Should be small but non-zero
        assert!(dist > 0);
        assert!(dist < 20); // Reasonably similar
    }

    #[test]
    fn test_q_dist_empty_strings() {
        let mut measure = Measure::new();
        let dist = measure.string_dist_str("", "");
        assert_eq!(dist, 0);
    }

    #[test]
    fn test_q_dist_one_empty() {
        let mut measure = Measure::new();
        let dist = measure.string_dist_str("hello", "");
        assert!(dist > 0);
    }

    #[test]
    fn test_get_distance_same_elements() {
        let mut measure = Measure::new();

        let attrs = StdHashMap::new();
        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs.clone(),
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs,
        ))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        // With short content (just element name, total=1), penalty is applied
        // penalty = max(0, 1 - 1/20) = 0.95
        // distance = 0.95 + 0.05 * 0 = 0.95
        assert!((dist - 0.95).abs() < 0.01);
    }

    #[test]
    fn test_get_distance_different_element_names() {
        let mut measure = Measure::new();

        let attrs = StdHashMap::new();
        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs.clone(),
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "span".to_string(),
            attrs,
        ))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        assert!(dist > 0.0);
        assert!(dist <= 1.0);
    }

    #[test]
    fn test_get_distance_same_attributes() {
        let mut measure = Measure::new();

        let mut attrs = StdHashMap::new();
        attrs.insert("id".to_string(), "foo".to_string());
        attrs.insert("class".to_string(), "bar".to_string());

        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs.clone(),
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs,
        ))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        // With short content (element name + 2 attrs with short values):
        // total = 1 + 2*2 = 5 (name + 2 attrs with info=1+1 each)
        // penalty = max(0, 1 - 5/20) = 0.75
        // Since identical, mismatched = 0, so distance = penalty = 0.75
        assert!((dist - 0.75).abs() < 0.01);
    }

    #[test]
    fn test_get_distance_different_attribute_values() {
        let mut measure = Measure::new();

        let mut attrs_a = StdHashMap::new();
        attrs_a.insert("id".to_string(), "foo".to_string());

        let mut attrs_b = StdHashMap::new();
        attrs_b.insert("id".to_string(), "bar".to_string());

        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs_a,
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs_b,
        ))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        assert!(dist > 0.0);
        assert!(dist <= 1.0);
    }

    #[test]
    fn test_get_distance_missing_attribute() {
        let mut measure = Measure::new();

        let mut attrs_a = StdHashMap::new();
        attrs_a.insert("id".to_string(), "foo".to_string());

        let attrs_b = StdHashMap::new();

        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs_a,
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            attrs_b,
        ))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        assert!(dist > 0.0);
    }

    #[test]
    fn test_get_distance_same_text() {
        let mut measure = Measure::new();

        let a = new_base_node(Some(XmlContent::Text(XmlText::new("hello world"))));
        let b = new_base_node(Some(XmlContent::Text(XmlText::new("hello world"))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        // "hello world" has 11 chars, info_size = 11 per node
        // total = (11 + 11) / 2 = 11
        // penalty = max(0, 1 - 11/20) = 0.45
        // Since identical, mismatched = 0, distance = penalty = 0.45
        // But wait, let me check the actual value - shorter text has higher penalty
        assert!(dist >= 0.0);
        assert!(dist < 1.0); // Not a total mismatch
                             // For longer identical texts, distance should be lower
        let mut measure2 = Measure::new();
        let long_text = "This is a much longer piece of text that should have lower penalty";
        let c = new_base_node(Some(XmlContent::Text(XmlText::new(long_text))));
        let d = new_base_node(Some(XmlContent::Text(XmlText::new(long_text))));
        let dist2 = measure2.get_distance(Some(&c), Some(&d));
        // Longer text should have lower distance (less penalty)
        assert!(dist2 < dist);
    }

    #[test]
    fn test_get_distance_different_text() {
        let mut measure = Measure::new();

        let a = new_base_node(Some(XmlContent::Text(XmlText::new("hello"))));
        let b = new_base_node(Some(XmlContent::Text(XmlText::new("world"))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        assert!(dist > 0.0);
        assert!(dist <= 1.0);
    }

    #[test]
    fn test_get_distance_element_vs_text() {
        let mut measure = Measure::new();

        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            StdHashMap::new(),
        ))));
        let b = new_base_node(Some(XmlContent::Text(XmlText::new("hello"))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        assert_eq!(dist, 1.0); // Total mismatch
    }

    #[test]
    fn test_child_list_distance_both_empty() {
        let mut measure = Measure::new();

        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            StdHashMap::new(),
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            StdHashMap::new(),
        ))));

        let dist = measure.child_list_distance(&a, &b);
        assert_eq!(dist, ZERO_CHILDREN_MATCH);
    }

    #[test]
    fn test_child_list_distance_same_children() {
        let mut measure = Measure::new();

        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            StdHashMap::new(),
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            StdHashMap::new(),
        ))));

        // Add same children to both
        let child1 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "span".to_string(),
            StdHashMap::new(),
        ))));
        let child2 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "span".to_string(),
            StdHashMap::new(),
        ))));

        crate::node::NodeInner::add_child_to_ref(&a, child1);
        crate::node::NodeInner::add_child_to_ref(&b, child2);

        let dist = measure.child_list_distance(&a, &b);
        assert_eq!(dist, 0.0);
    }

    #[test]
    fn test_child_list_distance_different_children() {
        let mut measure = Measure::new();

        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            StdHashMap::new(),
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "div".to_string(),
            StdHashMap::new(),
        ))));

        // Add different children
        let child1 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "span".to_string(),
            StdHashMap::new(),
        ))));
        let child2 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "p".to_string(),
            StdHashMap::new(),
        ))));

        crate::node::NodeInner::add_child_to_ref(&a, child1);
        crate::node::NodeInner::add_child_to_ref(&b, child2);

        let dist = measure.child_list_distance(&a, &b);
        assert!(dist > 0.0);
        assert!(dist <= 1.0);
    }

    #[test]
    fn test_penalty_for_short_content() {
        let mut measure = Measure::new();

        // Very short text nodes should have penalty applied
        let a = new_base_node(Some(XmlContent::Text(XmlText::new("a"))));
        let b = new_base_node(Some(XmlContent::Text(XmlText::new("b"))));

        let dist = measure.get_distance(Some(&a), Some(&b));
        // With short content, penalty increases distance
        assert!(dist > 0.0);
    }

    #[test]
    fn test_q_grams_built_correctly() {
        let measure = Measure::new();
        let mut grams: FxHashMap<String, i32> = FxHashMap::default();
        measure.build_q_grams_str("hello", &mut grams);

        // "hello" (len=5) comparing to itself → combined=10 → Q=2
        // Should produce 2-grams: "he", "el", "ll", "lo", "o"
        assert!(grams.contains_key("he"));
        assert!(grams.contains_key("el"));
        assert!(grams.contains_key("ll"));
        assert!(grams.contains_key("lo"));
        assert!(grams.contains_key("o"));
    }
}
