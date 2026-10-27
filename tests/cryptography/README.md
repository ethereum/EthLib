# Cryptography test vectors

Each primitive has a directory, each operation a subdirectory, and each case a `data.yaml`.

A `format.md` next to the cases of an operation describes their fields.

The generators under `bindings/python/tests/` write the cases through the Python bindings.

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

## Checks

```bash
python3 tests/cryptography/check_vectors.py
```

It checks that every case in a pinned directory is listed, with the listed digest.

It needs only Python's standard library, and CI runs it on every change.

```bash
python3 -m unittest tests/cryptography/test_check_vectors.py
```

It checks the check itself, on a small tree built in a temporary directory: a missing manifest, a changed case, an unlisted case and a deleted case must each fail.
CI runs it with the check.

```bash
python3 tests/cryptography/check_vectors.py --upstream
```

It also downloads the upstream archive, checks its digest, and checks that every upstream case is pinned here with the upstream digest.

Pass `--archive` with a local copy to skip the download.

A case that exists only here is allowed, and is reported as EthLib's own.

Its expected value comes from the code under test, so it is not a check against anything independent.

## Changing a pinned case

A pinned case changes only when the specification changes.

The pull request says why, updates `SHA256SUMS`, and is marked breaking.

The `--upstream` check then reports that case, because it no longer matches the archive.
