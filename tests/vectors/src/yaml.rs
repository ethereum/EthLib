//! The YAML encoding of a test vector, byte for byte.
//!
//! The pinned vectors come from the consensus-specs generators, which write YAML with `ruamel.yaml`.
//! Their digests pin every byte, so this encoder reproduces that writer's layout exactly:
//!
//! - Maps and lists of byte strings use block style, one entry per line.
//! - A list of plain scalars uses flow style, `[1, 2, 3]`, wrapped near column 80.
//! - Byte strings are single-quoted hexadecimal.

use serde_json::Value;

/// The column the writer tries not to cross.
///
/// It is the default line width of `ruamel.yaml`.
const WIDTH: usize = 80;

/// The YAML text of a document, which must be a map.
///
/// # Panics
///
/// Panics on a shape the vectors never use, and so the encoder does not define:
/// a document that is not a map, or a map or a list of plain scalars nested inside a list.
#[must_use]
pub fn to_yaml(document: &Value) -> String {
    let Value::Object(fields) = document else { panic!("a vector is a map") };
    let mut out = String::new();
    for (key, value) in fields {
        entry(&mut out, key, value, 0);
    }
    out
}

/// Write one map entry whose key starts at column `indent`.
fn entry(out: &mut String, key: &str, value: &Value, indent: usize) {
    // Every entry starts its own line with its key.
    push_indent(out, indent);
    out.push_str(key);
    out.push(':');
    match value {
        // A nested map starts on the next line, two columns in.
        Value::Object(inner) => {
            out.push('\n');
            for (key, value) in inner {
                entry(out, key, value, indent + 2);
            }
        }
        // A list of plain scalars stays on the key's line, as a flow list.
        Value::Array(items) if is_flow(items) => {
            // The key and its colon fill the line up to here.
            let column = indent + key.len() + 1;
            flow_sequence(out, items, column, indent);
            out.push('\n');
        }
        // Any other list starts on the next line, its dashes aligned with the key.
        //
        //     input:
        //     - '0x01'
        Value::Array(items) => {
            out.push('\n');
            block_sequence(out, items, indent, false);
        }
        // A scalar follows the key after one space.
        scalar => {
            out.push(' ');
            push_scalar(out, scalar);
            out.push('\n');
        }
    }
}

/// Write a block list whose dashes sit at column `indent`.
///
/// A list nested in a list starts on its parent's line:
///
/// ```text
///     - - '0x01'
///       - '0x02'
///     - - '0x03'
/// ```
///
/// So the first dash of a nested list follows its parent's dash, and is not indented again.
fn block_sequence(out: &mut String, items: &[Value], indent: usize, first_inline: bool) {
    for (i, item) in items.iter().enumerate() {
        // The first item of a nested list already sits after its parent's dash.
        if i > 0 || !first_inline {
            push_indent(out, indent);
        }
        out.push_str("- ");
        match item {
            // A nested list of byte strings continues on this line.
            Value::Array(inner) if !is_flow(inner) => block_sequence(out, inner, indent + 2, true),
            Value::Array(_) | Value::Object(_) => panic!("the vectors never nest a flow list or a map in a list"),
            scalar => {
                push_scalar(out, scalar);
                out.push('\n');
            }
        }
    }
}

/// Write a flow list of plain scalars, starting after the key at `column`.
///
/// The list wraps the way `ruamel.yaml` wraps it, by two independent rules:
///
/// ```text
///     rule 1: a comma ends past column 80     → break, next item at indent + 2
///     rule 2: an item would end past column 80 → break, the item at indent + 4
/// ```
///
/// Rule 1 fires before the space after the comma, so its line ends on the comma.
/// Rule 2 fires after that space, so its line keeps a trailing space.
///
/// ```text
///       cell_indices: [0, 1, 2, ..., 16, 17,_      ← rule 2, "_" is the kept space
///           18, 19, 20, ..., 35, 36,               ← rule 1
///         37, 38, 39]
/// ```
fn flow_sequence(out: &mut String, items: &[Value], column: usize, indent: usize) {
    // The writer indents the list one level past its key, and each item one level more.
    let list_indent = indent + 2;
    let item_indent = indent + 4;

    out.push_str(" [");
    let mut column = column + 2;
    for (i, item) in items.iter().enumerate() {
        let text = plain(item).expect("a flow list holds only plain scalars");

        // Every item after the first follows a comma, and then a space.
        let mut needs_space = false;
        if i > 0 {
            out.push(',');
            column += 1;
            needs_space = true;
        }

        // Rule 1: a comma that crossed the width ends the line.
        if column > WIDTH {
            out.push('\n');
            push_indent(out, list_indent);
            column = list_indent;
            needs_space = false;
        }
        if needs_space {
            out.push(' ');
            column += 1;
        }

        // Rule 2: an item that would cross the width moves to a new line.
        //
        // An item already at the start of its line stays, however long it is.
        if column + text.len() > WIDTH && column > item_indent {
            out.push('\n');
            push_indent(out, item_indent);
            column = item_indent;
        }
        out.push_str(&text);
        column += text.len();
    }
    out.push(']');
}

/// Whether a list is written in flow style: all of its items are plain scalars.
///
/// An empty list qualifies, and is written `[]`.
fn is_flow(items: &[Value]) -> bool {
    items.iter().all(|item| plain(item).is_some())
}

/// The text of a scalar written without quotes, or `None` for any other value.
fn plain(value: &Value) -> Option<String> {
    match value {
        Value::Null => Some("null".to_owned()),
        Value::Bool(b) => Some(b.to_string()),
        Value::Number(n) => Some(n.to_string()),
        Value::String(_) | Value::Array(_) | Value::Object(_) => None,
    }
}

/// Write a scalar: plain, or a string in single quotes.
///
/// Every string in a vector is a `0x` byte string.
/// Unquoted, YAML 1.1 would read it as an integer, so `ruamel.yaml` quotes it.
fn push_scalar(out: &mut String, value: &Value) {
    match value {
        Value::String(text) => {
            out.push('\'');
            out.push_str(text);
            out.push('\'');
        }
        other => out.push_str(&plain(other).expect("a scalar is plain or a byte string")),
    }
}

/// Write `width` spaces.
fn push_indent(out: &mut String, width: usize) {
    out.extend(std::iter::repeat_n(' ', width));
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn scalars_and_maps() {
        // One field of each scalar kind, under a nested map.
        let document = json!({"input": {"z": "0xab01", "n": 7, "empty": "0x"}, "output": null});
        assert_eq!(to_yaml(&document), "input:\n  z: '0xab01'\n  n: 7\n  empty: '0x'\noutput: null\n");
    }

    #[test]
    fn nested_block_lists() {
        // A list of lists of byte strings: each inner list starts after its parent's dash.
        let document = json!({"output": [["0x01", "0x02"], ["0x03"]]});
        assert_eq!(to_yaml(&document), "output:\n- - '0x01'\n  - '0x02'\n- - '0x03'\n");
    }

    #[test]
    fn empty_lists_are_flow() {
        // An empty list has no item that forces block style.
        let document = json!({"input": {"cells": []}, "output": true});
        assert_eq!(to_yaml(&document), "input:\n  cells: []\noutput: true\n");
    }

    #[test]
    fn flow_list_wraps_like_ruamel() {
        // The expected text is the output of `ruamel.yaml` 0.19.1 for the same data.
        //
        // Fixture state: 40 indices under a key at column 2.
        //
        //     line 1: the comma after 17 ends on column 80, not past it
        //             → the space is written, then 18 would end on column 83
        //             → rule 2: break before 18 at column 6, trailing space kept
        //     line 2: the comma after 36 ends on column 81
        //             → rule 1: break before the space, 37 at column 4
        let document = json!({"input": {"cell_indices": (0..40).collect::<Vec<u64>>()}});
        let expected = "input:\n  cell_indices: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, \n      18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,\n    37, 38, 39]\n";
        assert_eq!(to_yaml(&document), expected);
    }
}
