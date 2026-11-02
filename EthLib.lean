module

public import EthLib.Cryptography
public import EthLib.Networking
public import EthLib.Execution
public import EthLib.Serialization

/-!
# `EthLib`

Ethereum specifications, written in Lean.

Each domain lives in its own subtree:

- `EthLib.Cryptography` holds the cryptographic primitives.
- `EthLib.Networking` holds the wire formats of the networking layer.
- `EthLib.Execution` holds the execution layer: the fees of a block and the precompiled contracts of the EVM.
- `EthLib.Serialization` holds the encodings of Ethereum data.
-/
