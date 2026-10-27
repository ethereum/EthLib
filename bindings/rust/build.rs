//! Link the Lean objects of EthLib and the Lean runtime into the crate.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The directories Lake writes the compiled C of each package to.
///
/// - The root package holds every EthLib module.
/// - The SSZ codec is a Lake dependency, so it builds in its own tree.
const OBJECT_ROOTS: [&str; 2] = [".lake/build/ir/EthLib", ".lake/packages/ssz/lean/.lake/build/ir"];

/// The suffix Lake gives an object compiled for export from a shared library.
const OBJECT_SUFFIX: &str = ".c.o.export";

fn main() {
    // The crate sits two levels below the repository root.
    let manifest = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR"));
    let repo = manifest.join("../..");

    // Phase 1: find the Lean toolchain that Lake used.
    //
    // The objects and the runtime must come from the same toolchain.
    // The repository pins it in `lean-toolchain`, and elan resolves it from the repository root.
    let prefix = lean_prefix(&repo);
    let include = prefix.join("include");
    let runtime = prefix.join("lib/lean");

    // Phase 2: collect every object Lake compiled for the library.
    //
    // Proofs produce no code that the library calls, so they stay out of the link.
    let mut objects = Vec::new();
    for root in OBJECT_ROOTS {
        collect_objects(&repo.join(root), &mut objects);
    }
    assert!(
        !objects.is_empty(),
        "no Lean objects under {}: run `lake build EthLib` first",
        repo.join(OBJECT_ROOTS[0]).display(),
    );
    objects.sort();

    // Phase 3: archive the shim and the objects into one static library.
    //
    // The linker then pulls in only the modules the exports reach.
    cc::Build::new().file("src/shim.c").include(&include).objects(&objects).compile("ethlib_lean");

    // Phase 4: link the Lean runtime dynamically.
    //
    // Its static archives are not position independent on Linux, so they cannot go into a PIE.
    println!("cargo::rustc-link-search=native={}", runtime.display());
    println!("cargo::rustc-link-lib=dylib=leanshared");

    // Phase 5: let every binary find the runtime without `LD_LIBRARY_PATH`.
    //
    //     this crate : rpath set here, for its own tests
    //     dependents : read `DEP_ETHLIB_LEAN_LIB_DIR` and set the same rpath
    println!("cargo::rustc-link-arg=-Wl,-rpath,{}", runtime.display());
    println!("cargo::metadata=lean_lib_dir={}", runtime.display());

    // Rebuild when the shim or any Lean object changes.
    println!("cargo::rerun-if-changed=src/shim.c");
    println!("cargo::rerun-if-changed={}", repo.join("lean-toolchain").display());
    for object in &objects {
        println!("cargo::rerun-if-changed={}", object.display());
    }
}

/// The installation prefix of the Lean toolchain pinned by the repository.
fn lean_prefix(repo: &Path) -> PathBuf {
    // `lean --print-prefix` prints the prefix followed by a newline.
    let output = Command::new("lean")
        .arg("--print-prefix")
        .current_dir(repo)
        .output()
        .expect("`lean` is not on PATH: install elan");
    assert!(output.status.success(), "`lean --print-prefix` failed");
    let prefix = String::from_utf8(output.stdout).expect("the Lean prefix is UTF-8");
    PathBuf::from(prefix.trim_end())
}

/// Append every exported object under `dir` to `out`, skipping proof modules.
fn collect_objects(dir: &Path, out: &mut Vec<PathBuf>) {
    // A missing tree means that package was never built, which the caller reports.
    let Ok(entries) = fs::read_dir(dir) else { return };
    // A new module adds an entry here, so a change to the directory reruns the script.
    println!("cargo::rerun-if-changed={}", dir.display());
    for entry in entries {
        let path = entry.expect("readable Lake output directory").path();
        if path.is_dir() {
            // Proof modules live under `Proofs/` at any depth.
            if path.file_name().is_some_and(|name| name == "Proofs") {
                continue;
            }
            collect_objects(&path, out);
        } else if path.to_str().is_some_and(|name| name.ends_with(OBJECT_SUFFIX)) {
            out.push(path);
        }
    }
}
