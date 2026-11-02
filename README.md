# EthLib

Formally verified Ethereum primitives, written in Lean.
EthLib is intended to be the shared home for Ethereum definitions and proofs, so that Lean projects can build on a common implementation instead of each maintaining its own.
Some of these primitives can also be used by Ethereum clients via bindings.
Clients may use the bindings temporarily until a native implementation exists, or permanently if the performance of this library is sufficient.

## Architecture

EthLib is organised in layers, from the bytes and integers every specification uses up to the two layers of the protocol.
A module imports only from its own layer or from those below it, and the execution and consensus layers never import each other.

[ARCHITECTURE.md](ARCHITECTURE.md) gives the scope, the rules behind each layer, the types that modules share and how forks are written.

## Where things live

| Layer | Module | What it specifies |
| --- | --- | --- |
| Cryptography | [`Hash`](EthLib/Cryptography/Hash/) | Keccak-256, SHA-256, RIPEMD-160, the BLAKE2b compression function, CRC-32C |
| Cryptography | [`Secp256k1`](EthLib/Cryptography/Secp256k1/) | the secp256k1 curve, ECDSA, public key recovery, addresses |
| Cryptography | [`Bls`](EthLib/Cryptography/Bls/) | BLS12-381 and BLS signatures |
| Cryptography | [`Kzg`](EthLib/Cryptography/Kzg/) | KZG commitments to blobs and cells |
| Cryptography | [`Xmss`](EthLib/Cryptography/Xmss/) | leanXMSS, a hash-based signature for a post-quantum consensus layer |
| Cryptography | [`Vrf`](EthLib/Cryptography/Vrf/) | the VRF tree, one verifiable random output per index |
| Serialization | [`Rlp`](EthLib/Serialization/Rlp/) | Recursive Length Prefix, the encoding of the execution layer |
| Serialization | [`Ssz`](EthLib/Serialization/Ssz/) | Simple Serialize and its merkleization, the encoding of the consensus layer |
| Networking | [`Encoding`](EthLib/Networking/Encoding/) | the protobuf varint of req/resp messages |
| Networking | [`Snappy`](EthLib/Networking/Snappy/) | Snappy block decompression |
| Networking | [`Gossip`](EthLib/Networking/Gossip/) | the gossip message ID of Phase 0 and Altair |
| Execution | [`Fees`](EthLib/Fees/) | the EIP-1559 base fee |
| Execution | [`Precompiles`](EthLib/Precompiles/) | ECRECOVER, RIPEMD-160, MODEXP and BLAKE2F |

The theorems about a module live under `Proofs/` in its layer, and the C exports that the bindings call under `Exports/`.

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

[BUILDING.md](BUILDING.md) covers module boundaries, CI caching and build timing reports.
When you refresh the dependencies, use `lake --keep-toolchain update`, so that the toolchain stays the one Mathlib expects.

### Testing

Run the test suite:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e '.[test]'
pytest
```
