//! Run every generator case and compare its output with the committed vector.
//!
//! ```text
//!     cargo test -p ethlib-generators --release --test vectors                       every case
//!     cargo test -p ethlib-generators --release --test vectors -- verify_kzg_proof   one handler
//!     ETHLIB_BLESS=1 cargo test -p ethlib-generators --release --test vectors        write the files
//! ```
//!
//! Each case is one trial, named `<kind>::<handler>::<case>`, and the trials run in parallel.
//! A run never writes a file unless asked to.
//! A written pinned case still has to match its digest, which the pin check enforces.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use ethlib_generators::Case;
use ethlib_vectors::CASE_FILE;
use libtest_mimic::{Arguments, Failed, Trial};

/// The variable that makes the run write each differing or missing file, instead of failing.
const BLESS: &str = "ETHLIB_BLESS";

fn main() {
    let args = Arguments::from_args();
    let bless = env::var_os(BLESS).is_some();
    let root = ethlib_vectors::root();

    // Every case's file and suite, to find the committed files that no case produces.
    let cases = ethlib_generators::cases();
    let expected: BTreeSet<PathBuf> = cases.iter().map(|case| root.join(case.path())).collect();
    let kinds: BTreeSet<&str> = cases.iter().map(Case::kind).collect();
    let kinds: Vec<PathBuf> = kinds.into_iter().map(|kind| root.join(kind)).collect();

    let mut trials: Vec<Trial> = cases.into_iter().map(|case| trial(case, &root, bless)).collect();
    trials.push(Trial::test("stale_vectors", move || stale(&kinds, &expected)));
    libtest_mimic::run(&args, trials).exit();
}

/// The trial that builds one case and compares it with its file.
fn trial(case: Case, root: &Path, bless: bool) -> Trial {
    let path = root.join(case.path());
    Trial::test(case.id(), move || {
        // Generating runs Lean, and fails if the outcome contradicts the specification.
        let actual = case.generate()?;
        let committed = fs::read_to_string(&path).ok();
        if committed.as_deref() == Some(actual.as_str()) {
            return Ok(());
        }

        // Asked to write: the generated text becomes the committed file.
        if bless {
            fs::create_dir_all(path.parent().expect("a case file has a directory")).map_err(|e| e.to_string())?;
            return fs::write(&path, actual).map_err(|e| Failed::from(e.to_string()));
        }
        Err(match committed {
            None => format!("{} is missing\nrerun with {BLESS}=1 to write it", path.display()).into(),
            Some(committed) => mismatch(&path, &committed, &actual).into(),
        })
    })
}

/// Describe the first line where the committed and generated texts differ.
fn mismatch(path: &Path, committed: &str, actual: &str) -> String {
    // Lines of a blob are 262 kB long, so each one is cut to a readable prefix.
    let cut = |line: &str| line.chars().take(120).collect::<String>();
    let (mut committed_lines, mut actual_lines) = (committed.lines(), actual.lines());
    let mut number = 1;
    loop {
        match (committed_lines.next(), actual_lines.next()) {
            (Some(c), Some(a)) if c == a => number += 1,
            (c, a) => {
                return format!(
                    "{} differs at line {number}\n  committed: {}\n  generated: {}\nrerun with {BLESS}=1 to write it",
                    path.display(),
                    c.map_or_else(|| "<end of file>".to_owned(), cut),
                    a.map_or_else(|| "<end of file>".to_owned(), cut),
                );
            }
        }
    }
}

/// Fail on any committed case file that no case produces.
///
/// A renamed or deleted case leaves its old file behind, which consumers would keep running.
fn stale(kinds: &[PathBuf], expected: &BTreeSet<PathBuf>) -> Result<(), Failed> {
    let mut found = Vec::new();
    for kind in kinds {
        collect(kind, &mut found).map_err(|e| e.to_string())?;
    }
    let stale: Vec<String> =
        found.iter().filter(|path| !expected.contains(*path)).map(|path| path.display().to_string()).collect();
    if stale.is_empty() { Ok(()) } else { Err(format!("no case produces these files:\n{}", stale.join("\n")).into()) }
}

/// Append every case file under `dir` to `out`.
fn collect(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect(&path, out)?;
        } else if path.file_name().is_some_and(|name| name == CASE_FILE) {
            out.push(path);
        }
    }
    Ok(())
}
