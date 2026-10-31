import EthLib.Serialization.Rlp
import EthLib.Serialization.Ssz

/-!
# `EthLib.Serialization`

Encodings of Ethereum data, shared by the consensus and execution layers.

- `EthLib.Serialization.Rlp` holds Recursive Length Prefix, the encoding of the execution layer.
- `EthLib.Serialization.Ssz` holds Simple Serialize, the encoding and Merkleization of typed values.
-/
