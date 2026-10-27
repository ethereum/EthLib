# Cryptography test vectors

Each primitive has a directory, each operation a subdirectory, and each case a `data.yaml`.

A `format.md` next to the cases of an operation describes their fields.

```text
tests/cryptography/<kind>/<handler>/<case>/data.yaml

input:  ...    what the operation receives
output: ...    what it returns, or null when it must reject the input
```

## Generators

The generators live in `tests/generators`, one Rust module per handler.

A handler is a struct that holds the operation's input, and serializes as the case's `input:`.

It implements `Operation`: its output type, the call into Lean through `bindings/rust`, and its cases.

A case only names an input and the outcome the specification requires: `valid`, `returns(output)` or `invalid`.

The framework runs Lean, checks that outcome, and writes the output, or null for a rejection.

They run as a test suite, one trial per case:

```bash
cargo test -p ethlib-generators --release --test vectors
cargo test -p ethlib-generators --release --test vectors -- verify_kzg_proof
```

A trial passes when the generated file matches the committed one byte for byte.

A run never writes a file.

To write the files instead, set `ETHLIB_BLESS`:

```bash
ETHLIB_BLESS=1 cargo test -p ethlib-generators --release --test vectors
```

The `stale_vectors` trial fails on a committed case that no generator produces.

## Pinned vectors

The `bls/` and `kzg/` directories are pinned, and so is any other directory with a `SHA256SUMS` file.

Every case under a pinned directory is listed there with its digest, so regenerating a case that changes its answer is caught.

A pinned directory without its `SHA256SUMS` is an error, so deleting the file cannot switch the check off.

The `kzg/` and `bls/` cases are pinned to consensus-specs `v1.7.0-alpha.12`.

They match the cases in its `general.tar.gz` byte for byte, and that archive has sha256 `329f3cf58927df2614ecafbce78eb3c5258a13e8731d2f410bb31d8e4a5b9eaf`.

That release came out before consensus-specs#5398, which removed the KZG specification and its generators from consensus-specs and pointed to this repository.

Its cases were written by the Python specification, not by EthLib.

The digests preserve that independent provenance for the cases committed here.

```text
upstream:  tests/general/<fork>/<kind>/<handler>/<suite>/<case>/data.yaml
here:      tests/cryptography/<kind>/<handler>/<case>/data.yaml
```

The YAML layout is part of what the digests pin.

The Rust encoder in `tests/vectors` reproduces the layout of the consensus-specs writer, `ruamel.yaml`, including where it wraps long lists.

## Checks

```bash
cargo run -p ethlib-vectors --bin check-vectors
```

It checks that every case in a pinned directory is listed, with the listed digest.

It does not link Lean, and CI runs it on every change.

```bash
cargo test -p ethlib-vectors
```

It checks the check itself, on small trees built in a temporary directory: a missing manifest, a changed case, an unlisted case and a deleted case must each fail.

It also parses every committed case and encodes it again, which must give the same bytes.

CI runs it with the check.

```bash
curl -LO https://github.com/ethereum/consensus-specs/releases/download/v1.7.0-alpha.12/general.tar.gz
cargo run -p ethlib-vectors --bin check-vectors -- --upstream general.tar.gz
```

It also checks the archive's digest, and that every upstream case is pinned here with the upstream digest.

A case that exists only here is allowed, and is reported as EthLib's own.

Its expected value comes from the code under test, so it is not a check against anything independent.

## Changing a pinned case

A pinned case changes only when the specification changes.

The pull request says why, updates `SHA256SUMS`, and is marked breaking.

The `--upstream` check then reports that case, because it no longer matches the archive.
