# EthLib

Formally verified Ethereum primitives, written in Lean.
EthLib is intended to be the shared home for Ethereum definitions and proofs, so that Lean projects can build on a common implementation instead of each maintaining its own.
Some of these primitives can also be used by Ethereum clients via bindings.
Clients may use the bindings temporarily until a native implementation exists, or permanently if the performance of this library is sufficient.

## Primitives

### Cryptography

- [BLS12-381 signatures](EthLib/Cryptography/Bls/)
- [KZG polynomial commitments](EthLib/Cryptography/Kzg/)
- [XMSS signatures](EthLib/Cryptography/Xmss/)
- [VRF tree](EthLib/Cryptography/Vrf/)

### Precompiles

- [MODEXP](EthLib/Precompiles/Modexp/)
- [RIPEMD-160](EthLib/Precompiles/Ripemd160.lean)
- [BLAKE2F](EthLib/Precompiles/Blake2f/)

[`SOUNDNESS.md`](SOUNDNESS.md) says what the proofs establish, and what each use of EthLib trusts on top of them.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md) first.
It sets the terms under which you contribute, and points to the rules in [AGENTS.md](AGENTS.md).

### Prerequisites

Install [uv](https://docs.astral.sh/uv/getting-started/installation/) for repository Python checks.
CI uses uv 0.13.6.
The soundness checks select Python 3.12, which uv downloads if needed.

Install [elan](https://github.com/leanprover/elan):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Download [Mathlib](https://github.com/leanprover-community/mathlib4):

```bash
lake exe cache get
```

### Building

Compile the primitives and check every proof:

```bash
lake build
```

[BUILDING.md](BUILDING.md) covers module boundaries, CI caching and build timing reports.
When you refresh the dependencies, use `lake --keep-toolchain update`, so that the toolchain stays the one Mathlib expects.

### Testing

From the repository root, run the soundness checks used by CI:

```bash
uv run --no-project --python 3.12 python scripts/soundness_facts.py --check
uv run --no-project --python 3.12 python -m unittest scripts/test_soundness_facts.py
```

These checks use only the standard library.
`--no-project` runs them without installing the native bindings.

Run the binding test suite:

```bash
uv sync --frozen --extra test
uv run --no-sync pytest
```

Run `uv sync --frozen --extra test` again after changing Lean or C sources.
Sync rebuilds the native extension.
`uv run --no-sync` tests that build.
