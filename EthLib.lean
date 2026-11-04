module

public import EthLib.Base
public import EthLib.Consensus
public import EthLib.Cryptography
public import EthLib.Networking
public import EthLib.Execution
public import EthLib.Serialization

/-!
# `EthLib`

Ethereum specifications, written in Lean.

Each domain lives in its own subtree:

- `EthLib.Base` holds the bytes and integers every layer uses.
- `EthLib.Consensus` holds the consensus layer: the values and types of the beacon chain.
- `EthLib.Cryptography` holds the cryptographic primitives.
- `EthLib.Networking` holds the wire formats of the networking layer.
- `EthLib.Execution` holds the execution layer: the fees of a block, the EVM, its precompiled contracts and the Merkle Patricia Trie.
- `EthLib.Serialization` holds the encodings of Ethereum data.
-/
