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

## Fp2 square roots

`bench_bls_sqrt.py` compares two built EthLib packages on 34 pinned Wycheproof hash-to-G2 inputs.
It decodes their compressed points with both signs, giving 68 decode inputs.
Each process warms the inputs before timing, and the process order alternates each round.
Copy each built `bindings/python/ethlib` tree into a separate directory, then pass its parent:

```bash
.venv/bin/python benchmarks/bench_bls_sqrt.py \
  --before /tmp/before --after /tmp/after --output /tmp/fp2-sqrt.json
```

On 9 November 2026, `f695099d` and `codex/fp2-sqrt-1413` ran for nine rounds of three passes.
The machine was an Apple M4 Pro with 24 GiB, macOS 26.3, CPython 3.12.16 and Lean 4.35.0.
The table gives the median microseconds per call, with the range across rounds in parentheses.
All output digests agreed, including the full signed affine output of `hash_to_g2`.

| Operation | Before (us) | After (us) | Before / after |
| --- | ---: | ---: | ---: |
| `decode_g2` | 448.4 (442.9-465.5) | 432.2 (429.9-465.2) | 1.037 |
| `hash_to_g2` | 1784.0 (1720.3-1853.3) | 1730.1 (1716.3-1746.2) | 1.031 |
