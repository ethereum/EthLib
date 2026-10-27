//! The pinned vectors: each case in a pinned suite must match a recorded digest.
//!
//! A suite is pinned when its directory holds a `SHA256SUMS` manifest:
//!
//! ```text
//!     tests/cryptography/kzg/SHA256SUMS
//!
//!     b8ced01c...aa31  blob_to_kzg_commitment/blob_to_kzg_commitment_case_invalid_blob_0/data.yaml
//!     <sha256>         <path relative to the suite>
//! ```
//!
//! The BLS and KZG suites must be pinned.
//! A missing manifest for one of them is a problem, so deleting it cannot switch the check off.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{self, Read};
use std::path::Path;

use flate2::read::GzDecoder;
use sha2::{Digest, Sha256};

use crate::CASE_FILE;

/// The suites that must be pinned.
pub const REQUIRED: [&str; 2] = ["bls", "kzg"];

/// The name of a suite's manifest.
pub const MANIFEST: &str = "SHA256SUMS";

/// The general test archive of consensus-specs `v1.7.0-alpha.12`.
///
/// That release is the last one before consensus-specs#5398.
/// That pull request moved the KZG specification and its generators into this repository.
/// Its cases were written by the Python specification, so they are an independent reference.
pub const UPSTREAM_URL: &str =
    "https://github.com/ethereum/consensus-specs/releases/download/v1.7.0-alpha.12/general.tar.gz";

/// The SHA-256 of the archive at the upstream URL.
pub const UPSTREAM_SHA256: &str = "329f3cf58927df2614ecafbce78eb3c5258a13e8731d2f410bb31d8e4a5b9eaf";

/// A suite's manifest: the digest of each case file, keyed by its path in the suite.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Manifest {
    /// Hex SHA-256 digests, keyed by case path such as `handler/case/data.yaml`.
    pub digests: BTreeMap<String, String>,
}

impl Manifest {
    /// Read the manifest of the suite at `dir`.
    ///
    /// Returns `None` when the suite has no manifest.
    ///
    /// # Errors
    ///
    /// Fails on an unreadable file, or a line that is not `<digest>  <path>`.
    pub fn read(dir: &Path) -> io::Result<Option<Self>> {
        let text = match fs::read_to_string(dir.join(MANIFEST)) {
            Ok(text) => text,
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(err) => return Err(err),
        };
        text.parse().map(Some)
    }
}

impl std::str::FromStr for Manifest {
    type Err = io::Error;

    /// Parse the `sha256sum` format: a digest, two spaces, and a path, per line.
    fn from_str(text: &str) -> io::Result<Self> {
        let mut digests = BTreeMap::new();
        for line in text.lines() {
            let Some((digest, case)) = line.split_once("  ") else {
                return Err(io::Error::new(io::ErrorKind::InvalidData, format!("malformed manifest line: {line}")));
            };
            digests.insert(case.to_owned(), digest.to_owned());
        }
        Ok(Self { digests })
    }
}

/// The suites to check: the required ones, and any other suite with a manifest.
///
/// # Errors
///
/// Fails if the vector root cannot be listed.
pub fn pinned_suites(root: &Path) -> io::Result<BTreeSet<String>> {
    let mut suites: BTreeSet<String> = REQUIRED.iter().map(|&suite| suite.to_owned()).collect();
    for entry in fs::read_dir(root)? {
        let path = entry?.path();
        // A directory with a manifest opts into the check.
        if path.join(MANIFEST).is_file()
            && let Some(name) = path.file_name().and_then(|name| name.to_str())
        {
            suites.insert(name.to_owned());
        }
    }
    Ok(suites)
}

/// Check every pinned suite under `root` against its manifest.
///
/// Returns one message per problem, in path order.
///
/// # Errors
///
/// Fails on an unreadable file or directory.
/// A missing or changed case is a problem in the result, not an error.
pub fn check_local(root: &Path) -> io::Result<Vec<String>> {
    let mut problems = Vec::new();
    for suite in pinned_suites(root)? {
        let dir = root.join(&suite);
        let Some(manifest) = Manifest::read(&dir)? else {
            problems.push(format!("{suite}/{MANIFEST}: missing, so nothing in {suite} is checked"));
            continue;
        };

        // Every case on disk must be listed.
        let on_disk = case_files(&dir)?;
        for case in on_disk.iter().filter(|case| !manifest.digests.contains_key(*case)) {
            problems.push(format!("{suite}/{case}: not listed in {MANIFEST}"));
        }

        // Every listed case must exist, with its listed digest.
        for (case, digest) in &manifest.digests {
            if !on_disk.contains(case) {
                problems.push(format!("{suite}/{case}: listed but missing"));
            } else if sha256_hex(&fs::read(dir.join(case))?) != *digest {
                problems.push(format!("{suite}/{case}: digest differs from {MANIFEST}"));
            }
        }
    }
    // Report in path order, the way a reader scans a tree.
    problems.sort();
    Ok(problems)
}

/// The result of comparing the pins with the upstream archive.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UpstreamReport {
    /// One message per disagreement, in path order.
    pub problems: Vec<String>,
    /// Pinned cases with an upstream counterpart and the same digest.
    pub matching: usize,
    /// Pinned cases with no upstream counterpart.
    ///
    /// Their expected values come from EthLib itself, so they check nothing independent.
    pub own: usize,
}

/// Compare every pin under `root` with the upstream archive at `archive`.
///
/// Upstream lays a case out in more directories than this repository does:
///
/// ```text
///     upstream: tests/general/<fork>/<kind>/<handler>/<suite>/<case>/data.yaml
///     here:     <kind>/<handler>/<case>/data.yaml
/// ```
///
/// # Errors
///
/// Fails on an unreadable archive or manifest.
pub fn check_upstream(archive: &Path, root: &Path) -> io::Result<UpstreamReport> {
    // Phase 1: the archive must be the one the digest names.
    if sha256_hex_reader(File::open(archive)?)? != UPSTREAM_SHA256 {
        let problems = vec!["the archive is not the pinned upstream archive".to_owned()];
        return Ok(UpstreamReport { problems, ..UpstreamReport::default() });
    }

    // Phase 2: hash every upstream case, keyed the way this repository names it.
    let upstream = upstream_digests(archive)?;

    // Phase 3: compare suite by suite.
    let mut report = UpstreamReport::default();
    for suite in pinned_suites(root)? {
        // A missing manifest is the local check's problem, which always runs too.
        let Some(manifest) = Manifest::read(&root.join(&suite))? else { continue };
        let theirs = upstream.get(&suite).cloned().unwrap_or_default();

        for (case, digest) in &manifest.digests {
            match theirs.get(case) {
                None => report.own += 1,
                Some(upstream) if upstream == digest => report.matching += 1,
                Some(_) => report.problems.push(format!("{suite}/{case}: digest differs from upstream")),
            }
        }
        for case in theirs.keys().filter(|case| !manifest.digests.contains_key(*case)) {
            report.problems.push(format!("{suite}/{case}: upstream case not pinned here"));
        }
    }
    report.problems.sort();
    Ok(report)
}

/// Digests of the upstream cases, by suite and then by case path.
///
/// The archive streams through memory: nothing is extracted to disk.
fn upstream_digests(archive: &Path) -> io::Result<BTreeMap<String, BTreeMap<String, String>>> {
    let mut digests: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    let mut tar = tar::Archive::new(GzDecoder::new(File::open(archive)?));
    for entry in tar.entries()? {
        let mut entry = entry?;
        if !entry.header().entry_type().is_file() {
            continue;
        }
        // Only `tests/general/<fork>/<kind>/<handler>/<suite>/<case>/data.yaml` is a case.
        let path = entry.path()?.to_string_lossy().into_owned();
        let parts: Vec<&str> = path.split('/').collect();
        let ["tests", "general", _fork, kind, handler, _suite, case, leaf] = parts[..] else { continue };
        if leaf != CASE_FILE {
            continue;
        }
        let (kind, case) = (kind.to_owned(), format!("{handler}/{case}/{CASE_FILE}"));
        let mut data = Vec::new();
        entry.read_to_end(&mut data)?;
        digests.entry(kind).or_default().insert(case, sha256_hex(&data));
    }
    Ok(digests)
}

/// Every case file under a suite, as paths relative to it with `/` separators.
fn case_files(dir: &Path) -> io::Result<BTreeSet<String>> {
    let mut found = BTreeSet::new();
    let mut pending = vec![(dir.to_path_buf(), String::new())];
    // Walk the tree depth first, carrying each directory's relative path.
    while let Some((path, prefix)) = pending.pop() {
        for entry in fs::read_dir(&path)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let relative = if prefix.is_empty() { name.clone() } else { format!("{prefix}/{name}") };
            if entry.file_type()?.is_dir() {
                pending.push((entry.path(), relative));
            } else if name == CASE_FILE {
                found.insert(relative);
            }
        }
    }
    Ok(found)
}

/// The lowercase hex SHA-256 of `data`.
fn sha256_hex(data: &[u8]) -> String {
    hex::encode(Sha256::digest(data))
}

/// The lowercase hex SHA-256 of everything `reader` yields.
///
/// It streams: the upstream archive is about 170 MB.
fn sha256_hex_reader(mut reader: impl Read) -> io::Result<String> {
    let mut hasher = Sha256::new();
    io::copy(&mut reader, &mut hasher)?;
    Ok(hex::encode(hasher.finalize()))
}

#[cfg(test)]
mod tests {
    use std::fmt::Write;
    use std::fs;
    use std::path::Path;

    use tempfile::TempDir;

    use super::*;

    /// Write one suite: its case files, and a manifest that lists them all.
    fn write_suite(root: &Path, suite: &str, cases: &[(&str, &[u8])]) {
        let mut manifest = String::new();
        for (case, data) in cases {
            let path = root.join(suite).join(case).join(CASE_FILE);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, data).unwrap();
            writeln!(manifest, "{}  {case}/{CASE_FILE}", sha256_hex(data)).unwrap();
        }
        fs::write(root.join(suite).join(MANIFEST), manifest).unwrap();
    }

    /// A tree with both required suites, intact.
    fn intact() -> TempDir {
        let tmp = TempDir::new().unwrap();
        write_suite(tmp.path(), "bls", &[("sign/case_0", b"bls 0")]);
        write_suite(tmp.path(), "kzg", &[("blob/case_0", b"kzg 0"), ("blob/case_1", b"kzg 1")]);
        tmp
    }

    /// The problems the local check reports.
    fn problems(root: &Path) -> Vec<String> {
        check_local(root).unwrap()
    }

    #[test]
    fn intact_tree_passes() {
        let tmp = intact();
        assert_eq!(problems(tmp.path()), Vec::<String>::new());
    }

    #[test]
    fn missing_manifest_fails() {
        // Deleting a required manifest must not switch its suite's check off.
        let tmp = intact();
        fs::remove_file(tmp.path().join("kzg").join(MANIFEST)).unwrap();
        assert_eq!(problems(tmp.path()), ["kzg/SHA256SUMS: missing, so nothing in kzg is checked"]);
    }

    #[test]
    fn missing_suite_fails() {
        // Deleting the whole suite is caught the same way.
        let tmp = intact();
        fs::remove_dir_all(tmp.path().join("kzg")).unwrap();
        assert_eq!(problems(tmp.path()), ["kzg/SHA256SUMS: missing, so nothing in kzg is checked"]);
    }

    #[test]
    fn changed_case_fails() {
        // Mutation: rewrite one case with other bytes.
        //
        //     manifest: sha256("kzg 0")
        //     on disk : sha256("changed")   → mismatch
        let tmp = intact();
        fs::write(tmp.path().join("kzg/blob/case_0").join(CASE_FILE), b"changed").unwrap();
        assert_eq!(problems(tmp.path()), ["kzg/blob/case_0/data.yaml: digest differs from SHA256SUMS"]);
    }

    #[test]
    fn unlisted_case_fails() {
        // Mutation: add a case the manifest does not know.
        let tmp = intact();
        let extra = tmp.path().join("kzg/blob/case_2");
        fs::create_dir_all(&extra).unwrap();
        fs::write(extra.join(CASE_FILE), b"kzg 2").unwrap();
        assert_eq!(problems(tmp.path()), ["kzg/blob/case_2/data.yaml: not listed in SHA256SUMS"]);
    }

    #[test]
    fn deleted_case_fails() {
        // Mutation: delete a listed case.
        let tmp = intact();
        fs::remove_file(tmp.path().join("kzg/blob/case_1").join(CASE_FILE)).unwrap();
        assert_eq!(problems(tmp.path()), ["kzg/blob/case_1/data.yaml: listed but missing"]);
    }

    #[test]
    fn other_pinned_suite_is_checked() {
        // A suite outside the required list opts in by holding a manifest.
        let tmp = intact();
        write_suite(tmp.path(), "xmss", &[("sign/case_0", b"xmss 0")]);
        fs::write(tmp.path().join("xmss/sign/case_0").join(CASE_FILE), b"changed").unwrap();
        assert_eq!(problems(tmp.path()), ["xmss/sign/case_0/data.yaml: digest differs from SHA256SUMS"]);
    }

    #[test]
    fn wrong_archive_is_rejected_before_reading_it() {
        // Any file other than the pinned archive fails the digest check first.
        let tmp = intact();
        let archive = tmp.path().join("general.tar.gz");
        fs::write(&archive, b"not the archive").unwrap();
        let report = check_upstream(&archive, tmp.path()).unwrap();
        assert_eq!(report.problems, ["the archive is not the pinned upstream archive"]);
    }

    #[test]
    fn malformed_manifest_is_an_error() {
        // A line without the two-space separator is not a manifest line.
        assert!("deadbeef data.yaml".parse::<Manifest>().is_err());
    }
}
