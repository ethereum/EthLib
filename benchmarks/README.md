# Benchmarks

EthLib compiles its specification to native code, and the Python bindings call that code.
This directory times those calls against the Python specifications of Ethereum on the same inputs.
A pull request that changes the speed of a definition reports its numbers from this suite.

The suite is not a test.
It sits outside the `testpaths` of `pyproject.toml`, so `pytest` never collects it, and CI runs it only on manual dispatch.

## What runs on each side

Each row times one operation on three sides, each in its own process and virtual environment:

- `bench_ethlib.py` calls the EthLib bindings.
- `bench_eels.py` calls the execution specifications, with the Osaka fork modules.
- `bench_pyspec.py` calls the consensus specifications, with the Fulu mainnet preset.

The Python specifications call native code for most cryptography.
Keccak-256 runs in pycryptodome, SHA-256 in OpenSSL, secp256k1 recovery in `spec256k1`, BLS signatures in `py_arkworks_bls12381`, and KZG in c-kzg-4844.
A ratio against such a row is a ratio against C, C++ or Rust.
A row named `<op>@ckzg` or `<op>@snappy` calls that library directly on the same input.
A row named `<op>@py_ecc` calls `py_ecc`, a pure-Python reference.

Each side reduces the output of each row to a digest, and the comparison checks that the digests agree.
So the suite also reports any row on which EthLib and a reference disagree.

## Setting up

`sources.toml` pins one commit of each reference specification.
`setup.sh` clones each at its commit into `refs/`, installs it from its own lock file, generates the consensus pyspec, and writes the inputs into `data/`:

```bash
benchmarks/setup.sh
uv sync --extra test
```

The second command builds the EthLib bindings at the repository root.

The inputs are deterministic.
`gen_inputs.py` builds a block of 150 signed EIP-1559 transactions, a trie of 1000 pairs, a state of 200 accounts, the call data of each precompile, BLS keys and signatures, and six blobs.
`gen_cons_inputs.py` builds the Snappy streams, the SSZ cases and the KZG trusted setup in the format of c-kzg-4844.

## Running

`run.sh` runs the three sides in turn, each pinned to one core, so that no side competes with another:

```bash
benchmarks/run.sh
ROUNDS=1 CORE=6 BENCH_ONLY=rlp_decode_block,trie_root_1000 benchmarks/run.sh
```

Each row makes one warm-up call, then 5 repeats of `n` calls, with `n` chosen so that a repeat lasts about 0.3 s.
The garbage collector is off during a repeat, and the time per call is the best repeat.
`compare.py` merges the rounds into `results/table.md`: the best time over the rounds, the spread between the rounds, the ratio of EthLib to the reference, and whether the outputs agree.

`scaling.py` times one EthLib call at growing input sizes and prints the growth exponent between the last two.
An exponent near 1 means linear time, and near 2 quadratic time:

```bash
.venv/bin/python benchmarks/scaling.py rlp,ssz
```

## Password derivation

The password derivation test times one scrypt call through the bindings and checks its result against Python's `hashlib.scrypt`:

```bash
uv run --no-sync pytest -q -s bindings/python/tests/hmac_kdf/test_password_kdf.py::test_scrypt_keystore_cost
```

On 8 November 2026, one call took 7.413 s on an Apple M4 Pro with 24 GiB of memory, macOS 26.3, CPython 3.12.16 and Lean 4.35.0.
The password was `password`, the salt was `salt`, and the parameters were `N = 2^18`, `r = 8`, `p = 1` and 32 output bytes.
The table payload was 256 MiB.
