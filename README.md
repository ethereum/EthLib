# EthLib

Ethereum specifications, written in Lean. Each domain has its own folder
under `EthLib/`; cryptography lives in `EthLib/Cryptography/`.

## Specs

- `EthLib/Cryptography/Bls/`, BLS12-381 curve arithmetic, hash-to-curve, and signatures.
- `EthLib/Cryptography/Kzg/`, KZG polynomial commitments.

## Proofs

Formal proofs of properties of the specs exist in
`EthLib/Cryptography/Proofs/`, mirroring the layout above.

## Prerequisites

- [`elan`](https://github.com/leanprover/elan), for `lean` and `lake`.

## Building

```bash
lake exe cache get
lake build
```

Note: `lake exe cache get` is only needed after
the initial clone or after `lake update`; otherwise, `lake build is sufficient`.


## Tests

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e '.[test]'
pytest
```

*Note*: Pre-generated reference tests are written to `tests/` at the project
root. These tests are intended for use across implementations and may be pinned
by downstream consumers.
