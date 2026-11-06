module

public import EthLib.Serialization.Ssz.Type.Desc
public import EthLib.Serialization.Ssz.Type.Value
public import EthLib.Serialization.Ssz.Type.Valid
public import EthLib.Serialization.Ssz.Type.Default
public import EthLib.Serialization.Ssz.Type.Paths
public import EthLib.Serialization.Ssz.Codec.Error
public import EthLib.Serialization.Ssz.Codec.Serialize
public import EthLib.Serialization.Ssz.Codec.Deserialize
public import EthLib.Serialization.Ssz.Codec.Layout
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Ssz.Codec.Root
public import EthLib.Serialization.Ssz.Codec.Proof
public import EthLib.Serialization.Ssz.Merkle.Chunk
public import EthLib.Serialization.Ssz.Merkle.Merkleize
public import EthLib.Serialization.Ssz.Merkle.Tree
public import EthLib.Serialization.Ssz.Merkle.Gindex
public import EthLib.Serialization.Ssz.Merkle.Verify
public import EthLib.Serialization.Ssz.Merkle.Branch
public import EthLib.Serialization.Ssz.Typed.Class
public import EthLib.Serialization.Ssz.Typed.Basic
public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Ssz.Typed.Container
public import EthLib.Serialization.Ssz.Typed.ForkKind
public import EthLib.Serialization.Ssz.Typed.Gindex
public import EthLib.Serialization.Ssz.Typed.Since
public import EthLib.Serialization.Ssz.Typed.Rooted

/-!
# `EthLib.Serialization.Ssz`

Simple Serialize (SSZ), the serialization and merkleization of the consensus layer.

Source: the SSZ specification in [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs).

Progressive lists follow [EIP-7916](https://eips.ethereum.org/EIPS/eip-7916).

Progressive containers follow [EIP-7495](https://eips.ethereum.org/EIPS/eip-7495).

Compatible unions follow [EIP-8016](https://eips.ethereum.org/EIPS/eip-8016).

- `Ssz/Type`: declarations, values, well-formedness, defaults and paths.
- `Ssz/Codec`: serialization, deserialization, layouts, roots and proofs.
- `Ssz/Merkle`: bounded and progressive trees, indices and verification.
- `Ssz/Typed`: Lean types as SSZ types, encoded and rooted through the codec.

Hashing uses SHA-256.

The proofs about these definitions mirror this layout under `EthLib.Serialization.Proofs.Ssz`.
-/
