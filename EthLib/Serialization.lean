module

public import EthLib.Serialization.E2store
public import EthLib.Serialization.JsonRpc
public import EthLib.Serialization.Rlp
public import EthLib.Serialization.Ssz

/-!
# `EthLib.Serialization`

Encodings of Ethereum data, shared by the consensus and execution layers.

- `EthLib.Serialization.E2store` holds e2store records, the container of the era1 and era files.
- `EthLib.Serialization.JsonRpc` holds the JSON form of the base types of the JSON-RPC APIs.
- `EthLib.Serialization.Rlp` holds Recursive Length Prefix, the encoding of the execution layer.
- `EthLib.Serialization.Ssz` holds Simple Serialize, the encoding and Merkleization of typed values.
-/
