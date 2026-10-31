# EthLib

Formally verified Ethereum primitives, written in Lean. EthLib is intended to be
the shared home for Ethereum definitions and proofs, so that Lean projects can
build on a common implementation instead of each maintaining its own. Some of
these primitives can also be used by Ethereum clients via bindings. Clients may
use the bindings temporarily until a native implementation exists, or
permanently if the performance of this library is sufficient.

## Primitives

### Cryptography

- [BLS12-381 signatures](EthLib/Cryptography/Bls/)
- [KZG polynomial commitments](EthLib/Cryptography/Kzg/)
- [XMSS signatures](EthLib/Cryptography/Xmss/)
- [VRF tree](EthLib/Cryptography/Vrf/)

### Precompiles

- [MODEXP](EthLib/Precompiles/Modexp/)
- [RIPEMD-160](EthLib/Precompiles/Ripemd160.lean)

[`SOUNDNESS.md`](SOUNDNESS.md) says what the proofs establish, and what each use of EthLib trusts on top of them.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md) first.
It sets the terms under which you contribute, and points to the rules in [AGENTS.md](AGENTS.md).

### Prerequisites

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

When refreshing dependencies, use `lake --keep-toolchain update` to retain the toolchain matching Mathlib.

### Testing

Run the test suite:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e '.[test]'
pytest
```
