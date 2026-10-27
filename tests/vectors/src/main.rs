//! Check the pinned test vectors.
//!
//! ```text
//!     cargo run -p ethlib-vectors --bin check-vectors
//!     cargo run -p ethlib-vectors --bin check-vectors -- --upstream general.tar.gz
//! ```
//!
//! The first form checks every pinned case against its manifest.
//! The second also checks the manifests against the consensus-specs archive, downloaded beforehand.
//! Neither needs Lean.

use std::env;
use std::io;
use std::path::PathBuf;
use std::process::ExitCode;

use ethlib_vectors::pins::{self, Manifest, UPSTREAM_SHA256, UPSTREAM_URL};

/// How to call the binary.
const USAGE: &str = "usage: check-vectors [--upstream <general.tar.gz>]";

fn main() -> ExitCode {
    // The only option names the upstream archive.
    let upstream = match env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [] => None,
        [flag, archive] if flag == "--upstream" => Some(PathBuf::from(archive)),
        _ => {
            eprintln!("{USAGE}\n\nThe archive is {UPSTREAM_URL}\nwith sha256 {UPSTREAM_SHA256}.");
            return ExitCode::FAILURE;
        }
    };

    match run(upstream) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(err) => {
            eprintln!("check-vectors: {err}");
            ExitCode::FAILURE
        }
    }
}

/// Run the checks and print a report.
///
/// Returns whether every check passed.
fn run(upstream: Option<PathBuf>) -> io::Result<bool> {
    let root = ethlib_vectors::root();

    // The local check always runs: it is the one that catches a missing manifest.
    let mut problems = pins::check_local(&root)?;
    let report = upstream.map(|archive| pins::check_upstream(&archive, &root)).transpose()?;
    if let Some(report) = &report {
        problems.extend(report.problems.iter().cloned());
    }

    // Count the pins for the summary line.
    let mut pinned = 0;
    for suite in pins::pinned_suites(&root)? {
        pinned += Manifest::read(&root.join(suite))?.map_or(0, |manifest| manifest.digests.len());
    }

    for problem in &problems {
        eprintln!("{problem}");
    }
    if !problems.is_empty() {
        eprintln!("{} problem(s) in {pinned} pinned vectors", problems.len());
        return Ok(false);
    }
    println!("{pinned} pinned vectors match their digests");
    if let Some(report) = report {
        println!("upstream: {} match, {} not upstream (EthLib's own)", report.matching, report.own);
    }
    Ok(true)
}
