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
| Base | [`U256`](EthLib/Base/U256.lean) | the 256-bit word of the EVM, and its two's complement reading |
| Cryptography | [`Hash`](EthLib/Cryptography/Hash/) | Keccak-256, Keccak-512, SHA-256, RIPEMD-160, the BLAKE2b compression function, CRC-32C, HMAC-SHA-256, HKDF, the Concatenation KDF |
| Cryptography | [`Secp256k1`](EthLib/Cryptography/Secp256k1/) | the secp256k1 curve, ECDSA, public key recovery, addresses |
| Cryptography | [`Secp256r1`](EthLib/Cryptography/Secp256r1/) | the secp256r1 curve, also called P-256, and ECDSA verification |
| Cryptography | [`AltBn128`](EthLib/Cryptography/AltBn128/) | the alt_bn128 curve of EIP-196 and EIP-197, also called BN254, and its pairing |
| Cryptography | [`Aes`](EthLib/Cryptography/Aes/) | the AES block cipher for 128-bit and 256-bit keys, and the CTR and GCM modes |
| Cryptography | [`Bls`](EthLib/Cryptography/Bls/) | BLS12-381 and BLS signatures |
| Cryptography | [`Kzg`](EthLib/Cryptography/Kzg/) | KZG commitments to blobs and cells |
| Cryptography | [`Merkle`](EthLib/Cryptography/Merkle/) | the perfect binary Merkle tree that leanXMSS, leanSPHINCS, SSZ and the VRF share |
| Cryptography | [`Xmss`](EthLib/Cryptography/Xmss/) | leanXMSS, a hash-based signature for a post-quantum consensus layer |
| Cryptography | [`Sphincs`](EthLib/Cryptography/Sphincs/) | leanSPHINCS, a stateless hash-based signature with FORS for `2^30` signatures |
| Cryptography | [`Vrf`](EthLib/Cryptography/Vrf/) | the VRF tree, one verifiable random output per index |
| Serialization | [`Rlp`](EthLib/Serialization/Rlp/) | Recursive Length Prefix, the encoding of the execution layer |
| Serialization | [`Ssz`](EthLib/Serialization/Ssz/) | Simple Serialize and its merkleization, the encoding of the consensus layer |
| Networking | [`Encoding`](EthLib/Networking/Encoding/) | the protobuf varint of req/resp messages |
| Networking | [`Enr`](EthLib/Networking/Enr/) | Ethereum Node Records of EIP-778, their text form, the "v4" identity scheme, node IDs and the consensus entries |
| Networking | [`Snappy`](EthLib/Networking/Snappy/) | Snappy block decompression, a literal block encoder and the framing format |
| Networking | [`Gossip`](EthLib/Networking/Gossip/) | topic strings, the message ID of Phase 0 and Altair, and the attestation subnets of a node |
| Networking | [`Discv5`](EthLib/Networking/Discv5/) | the node distance, the "v4" handshake cryptography, the packets and the messages of discv5 |
| Networking | [`ReqResp`](EthLib/Networking/ReqResp/) | the `ssz_snappy` encoding of requests and response chunks, with its size bounds |
| Execution | [`Fees`](EthLib/Execution/Fees/) | the EIP-1559 base fee and the blob base fee |
| Execution | [`Evm`](EthLib/Execution/Evm/) | the opcodes of each fork, the stack, frame and memory of the EVM, its stack and memory instructions, and the gas prices |
| Execution | [`Precompiles`](EthLib/Execution/Evm/Precompiles/) | all 18 precompiles, from ECRECOVER to P256VERIFY, each run by address from the fork that adds it |
| Execution | [`State`](EthLib/Execution/State/) | accounts, the state, the state and storage roots, and the writes of a block and a transaction with their rollback |
| Execution | [`Transactions`](EthLib/Execution/Transactions/) | the five kinds of transaction, their bytes and hashes, the sender at each fork, and the intrinsic gas and validity of one transaction |
| Execution | [`Blocks`](EthLib/Execution/Blocks/) | the header, withdrawals, logs, receipts and block of each fork, the logs bloom filter and the header hash |
| Execution | [`Trie`](EthLib/Execution/Trie/) | the root of the Merkle Patricia Trie, plain and secured, its Merkle proofs, and the hex-prefix encoding of its paths |
| Consensus | [`Consensus`](EthLib/Consensus/) | the configuration, presets and constants, the execution payload, and models of Casper FFG and the LMD-GHOST fork choice |

The theorems about a module live under `Proofs/` in its layer, and the C exports that the bindings call under `Exports/`.

[`SOUNDNESS.md`](SOUNDNESS.md) says what the proofs establish, and what each use of EthLib trusts on top of them.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md) first.
It sets the rules and the terms under which you contribute.

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
Sync rebuilds the native extension when its source or build inputs change.
`uv run --no-sync` tests that build.
