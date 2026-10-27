//! Every committed vector, parsed and written back, must come out byte for byte.
//!
//! This pins the encoder against the whole corpus without running Lean.
//! An independent YAML parser reads each file, so the encoder is not checked against itself.

use std::fs;
use std::path::{Path, PathBuf};

use ethlib_vectors::CASE_FILE;
use saphyr::{LoadableYamlNode, Scalar, Yaml};
use serde_json::{Map, Value};

#[test]
fn every_committed_vector_round_trips() {
    // Fixture state: every case under the vector root, in a stable order.
    let mut files = Vec::new();
    collect(&ethlib_vectors::root(), &mut files);
    files.sort();
    assert!(!files.is_empty(), "no vector found under the vector root");

    let mut mismatches = Vec::new();
    for path in &files {
        let text = fs::read_to_string(path).unwrap();

        // Parse with the reference parser.
        let documents = Yaml::load_from_str(&text).unwrap();
        let [document] = documents.as_slice() else { panic!("{}: one document per file", path.display()) };

        // Re-encode and compare every byte.
        if ethlib_vectors::to_yaml(&value(document)) != text {
            mismatches.push(path.display().to_string());
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} of {} vectors re-encode differently:\n{}",
        mismatches.len(),
        files.len(),
        mismatches.join("\n")
    );
}

/// Convert a parsed node into the data model the encoder writes.
fn value(node: &Yaml<'_>) -> Value {
    match node {
        Yaml::Value(Scalar::Null) => Value::Null,
        Yaml::Value(Scalar::Boolean(b)) => Value::Bool(*b),
        Yaml::Value(Scalar::Integer(n)) => Value::from(*n),
        Yaml::Value(Scalar::String(s)) => Value::String(s.to_string()),
        Yaml::Sequence(items) => items.iter().map(value).collect(),
        Yaml::Mapping(entries) => Value::Object(
            entries
                .iter()
                .map(|(key, node)| (key.as_str().expect("string keys").to_owned(), value(node)))
                .collect::<Map<_, _>>(),
        ),
        other => panic!("unexpected YAML node: {other:?}"),
    }
}

/// Append every case file under `dir` to `out`.
fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect(&path, out);
        } else if path.file_name().is_some_and(|name| name == CASE_FILE) {
            out.push(path);
        }
    }
}
