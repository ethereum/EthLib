# Cryptography test vectors

A test vector fixes one input and the output a correct implementation must return for it.
The vectors here let any client, and EthLib itself, check an implementation against those outputs.

Each primitive has a directory, each of its operations a subdirectory, and each case a `data.yaml`.
A `format.md` next to the cases of an operation describes their fields.
The generators under `bindings/python/tests/` write the cases through the Python bindings.

## Pinned vectors

A vector is only worth something if its expected output is right, and regenerating it from the code under test would silently accept whatever that code returns.
So some directories are pinned: the `bls/`, `kzg/` and `secp256k1/` directories, and any other directory with a `SHA256SUMS` file.
Every case under a pinned directory is listed in that file with its digest, so regenerating a case that changes its answer is caught.
A pinned directory without its `SHA256SUMS` is an error, so deleting the file cannot switch the check off.

The `kzg/` and `bls/` cases are pinned to consensus-specs `v1.7.0-alpha.12`.
They match the cases in its `general.tar.gz` byte for byte, and that archive has sha256 `329f3cf58927df2614ecafbce78eb3c5258a13e8731d2f410bb31d8e4a5b9eaf`.
That release came out before consensus-specs#5398, which removed the KZG specification and its generators from consensus-specs and pointed to this repository.
Its cases were written by the Python specification, not by EthLib, and the digests preserve that independent provenance for the cases committed here.
Only the path of a case differs from upstream:

```text
upstream:  tests/general/<fork>/<kind>/<handler>/<suite>/<case>/data.yaml
here:      tests/cryptography/<kind>/<handler>/<case>/data.yaml
```

## secp256k1

The `secp256k1/` cases come from the Wycheproof ECDSA sets of `C2SP/wycheproof`, at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`.
The `verify` and `verify_low_s` outputs are Wycheproof's, so they check EthLib against an independent source.
The `recover` outputs come from EthLib, checked against Wycheproof's keys, as `recover/format.md` explains.
The cases keep Wycheproof's licence, the Apache License 2.0, in `secp256k1/LICENSE`.
Each operation's `format.md` says which set its cases come from.

## leanXMSS

The `xmss/` cases are pinned too, but two of their operations are slow to regenerate.
Key generation and signing build `2^16` one-time keys per tree, which takes the compiled specification minutes per case.
So the generators rewrite the `key_gen` and `sign` cases only on request:

```bash
ETHLIB_SLOW_VECTORS=1 uv run --no-sync pytest bindings/python/tests/xmss
```

Every other run writes the `verify` cases and the rejections, and reads the slow cases back.

The cases differ in where their expected values come from.
`key_gen_known_answer` and `sign_known_answer` hold the bytes the proofs pin, which an independent implementation computed.
The other cases come from the code under test.

## leanSPHINCS

The `sphincs/` cases are pinned too, and their key generation and signing are slow in the same way.
Key generation builds `2^10` one-time keys, and signing builds the FORS key and three trees, which takes the compiled specification seconds per case.
So the generators rewrite the `key_gen` and `sign` cases only on request:

```bash
ETHLIB_SLOW_VECTORS=1 uv run --no-sync pytest bindings/python/tests/sphincs
```

`key_gen_known_answer` and `sign_known_answer` hold the bytes the proofs pin.
The kernel checks that this signature verifies under this key, and that the key's public parameter is the one the seed gives.
The other cases come from the code under test.

## SHA-256

The `sha256/` cases are pinned too.
Every pytest run rewrites them, and `SHA256SUMS` pins the tree.
Most cases come from the NIST CAVP `SHA256ShortMsg` and `SHA256LongMsg` distributions, and two are the SHA-256 examples of FIPS 180-2, Appendix B.

## Checks

The first check compares every pinned directory with its manifest:

```bash
uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py
```

It checks that every case in a pinned directory is listed, with the listed digest.
It needs only Python's standard library, and CI runs it on every change.

The second check tests the first one, on a small tree built in a temporary directory:

```bash
uv run --no-project --python 3.12 python -m unittest tests/cryptography/test_check_vectors.py
```

A missing manifest, a changed case, an unlisted case and a deleted case must each fail.
CI runs it with the check.

The third check goes back to the source:

```bash
uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py --upstream
```

It downloads the upstream archive, checks its digest, and checks that every upstream case is pinned here with the upstream digest.
Pass `--archive` with a local copy to skip the download.
A case that exists only here is allowed, and is reported as EthLib's own.
Its expected value comes from the code under test, so it is not a check against anything independent.

## Changing a pinned case

A pinned case changes only when the specification changes.
The pull request that changes it says why, updates `SHA256SUMS`, and is marked breaking.
The `--upstream` check then reports that case, because it no longer matches the archive.
