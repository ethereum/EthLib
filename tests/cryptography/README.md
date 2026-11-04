# Cryptography test vectors

A test vector fixes one input and the output a correct implementation must return for it.
The vectors here let any client, and EthLib itself, check an implementation against those outputs.

Each primitive has a directory, each of its operations a subdirectory, and each case a `data.yaml`.
A `format.md` next to the cases of an operation describes their fields.
The generators under `bindings/python/tests/` write the cases through the Python bindings.

## Pinned vectors

A vector is only worth something if its expected output is right, and regenerating it from the code under test would silently accept whatever that code returns.
So some directories are pinned: `bls/`, `kzg/`, `secp256k1/`, `secp256r1/`, and any other directory with a `SHA256SUMS` file.
Every case under a pinned directory is listed in that file with its digest, so regenerating a case that changes its answer is caught.
A pinned directory without its `SHA256SUMS` is an error, so deleting the file cannot switch the check off.

Each upstream repository has one pinned commit, recorded in [`tests/sources.toml`](../sources.toml).
A `SHA256SUMS` starts with one `# Source:` line for each source of its cases, and `sha256sum -c` skips these lines.

The `kzg/` cases and the `eth_*` cases of `bls/` come from the general test archive of consensus-specs `v1.7.0-alpha.12`.
They match the cases in its `general.tar.gz` byte for byte, and that archive has sha256 `329f3cf58927df2614ecafbce78eb3c5258a13e8731d2f410bb31d8e4a5b9eaf`.
That release came out before consensus-specs#5398, which removed the KZG specification and its generators from consensus-specs and pointed to this repository.
Its cases were written by the Python specification, not by EthLib, and the digests preserve that independent provenance for the cases committed here.

Later releases of consensus-specs hold no KZG cases, so the `kzg/` cases are pinned to `ethereum/c-kzg-4844` at commit `a751e2d92abcd63b01d1400789789f5ea289a8b0`.
Its `tests/` directory holds the same 344 cases, byte for byte.
The `eth_*` cases of `bls/` are pinned to consensus-specs `v1.7.0-beta.4`, at commit `aa16bb4c156184e9548a997d53efaf2a228a6304`.
Its `general.tar.gz` holds the same 20 cases, byte for byte, and has sha256 `c4f395f71f606c28093500e32067990e430cc73a2277be6f3bf5090adcce3f67`.
Only the path of a case differs from upstream:

```text
upstream:  tests/general/<fork>/<kind>/<handler>/<suite>/<case>/data.yaml
here:      tests/cryptography/<kind>/<handler>/<case>/data.yaml
```

## BLS signatures and hash to curve

The general archives of consensus-specs have no BLS signing or verification cases.
So the `sign`, `verify`, `aggregate`, `fast_aggregate_verify` and `aggregate_verify` cases of `bls/` come from `ethereum/bls12-381-tests` `v0.1.2`, at commit `89ff3a86f1a9b89a555495f7535c853cda589320`.
Its archive `bls_tests_yaml.tar.gz` has sha256 `a4ef909b6248395094949a3bcdeb4e1b5b999733d4436f2c5006edba99d29279`.
A case keeps its upstream bytes, and only its path differs:

```text
upstream:  <handler>/<case>.yaml
here:      tests/cryptography/bls/<handler>/<case>/data.yaml
```

The `hash_to_curve/` cases come from RFC 9380, Appendices J.10.1, K.1 and K.2.
A script transcribed them from the text of the RFC, so no code computed their expected values.

The Python tests read these cases and compare EthLib with them.
They never rewrite them.

## secp256k1

The `secp256k1/` cases come from the Wycheproof ECDSA sets of `C2SP/wycheproof`, at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`.
The `verify` and `verify_low_s` outputs are Wycheproof's, so they check EthLib against an independent source.
The `recover` outputs come from EthLib, checked against Wycheproof's keys, as `recover/format.md` explains.
The cases keep Wycheproof's licence, the Apache License 2.0, in `secp256k1/LICENSE`.
Each operation's `format.md` says which set its cases come from.

## secp256r1

The `secp256r1/` cases come from the Wycheproof set `ecdsa_secp256r1_sha256_p1363_test.json`, at the same commit.
Their outputs are Wycheproof's, and they keep its licence in `secp256r1/LICENSE`.

## leanXMSS

The `xmss/` cases are pinned too, but two of their operations are slow to regenerate.
Key generation and signing build `2^16` one-time keys per tree, which takes the compiled specification minutes per case.
So the generators rewrite the `key_gen` and `sign` cases only on request:

```bash
ETHLIB_SLOW_VECTORS=1 uv run --no-sync pytest bindings/python/tests/xmss
```

Every other run writes the `verify` cases and the rejections, and reads the slow cases back.

The cases differ in where their expected values come from.
`key_gen_known_answer` and `sign_known_answer` hold bytes that an independent implementation computed.
The other cases come from the code under test.

## leanSPHINCS

The `sphincs/` cases are pinned too, and their key generation and signing are slow in the same way.
Key generation builds `2^10` one-time keys, and signing builds the FORS key and three trees, which takes the compiled specification seconds per case.
So the generators rewrite the `key_gen` and `sign` cases only on request:

```bash
ETHLIB_SLOW_VECTORS=1 uv run --no-sync pytest bindings/python/tests/sphincs
```

`verify_valid_scheme_seed` holds a public key and a signature that an independent implementation computed.
The other cases come from the code under test.

## VRF tree

The `vrf/` cases are pinned too.
Every pytest run rewrites them, and `SHA256SUMS` pins the tree.
The two valid openings, and the secrets and outputs of one seed, come from an independent implementation of the specification.
The rejections come from the code under test.

## SHA-256

The `sha256/` cases are pinned too.
Every pytest run rewrites them, and `SHA256SUMS` pins the tree.
Most cases come from the NIST CAVP `SHA256ShortMsg` and `SHA256LongMsg` distributions, and two are the SHA-256 examples of FIPS 180-2, Appendix B.

## Keccak-256

The `keccak/` cases are pinned too.
Every pytest run rewrites them, and `SHA256SUMS` pins the tree.
Most are the 256 byte-aligned cases of the Keccak team's `ShortMsgKAT_256.txt`, which `bindings/python/tests/keccak/kat/` vendors with its source.
Two more come from the team's `LongMsgKAT_256.txt`, and one hashes `abc`.
The `permutation` cases are the two examples of the team's `KeccakPermutationIntermediateValues.txt`.

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

It downloads the two upstream archives, checks their digests, and checks that every upstream case is pinned here with the upstream digest.
Pass `--archive` and `--bls-archive` with local copies to skip the downloads.
A case that exists in no upstream archive is allowed, and is counted.
Most such cases have expected values from the code under test, so they are not a check against anything independent.
The RFC 9380 cases are the exception: they come from the RFC, which no archive holds.

## Changing a pinned case

A pinned case changes only when the specification changes.
The pull request that changes it says why, updates `SHA256SUMS`, and is marked breaking.
The `--upstream` check then reports that case, because it no longer matches the archive.
