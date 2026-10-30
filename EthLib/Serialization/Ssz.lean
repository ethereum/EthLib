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

/-!
# `EthLib.Serialization.Ssz`

Simple Serialize (SSZ), as `consensus-specs` defines it in `ssz/simple-serialize.md` and `ssz/merkle-proofs.md`.

    Ssz/Type    declarations, values, well-formedness, defaults, and paths
    Ssz/Codec   serialization, deserialization, layouts, roots, and proofs
    Ssz/Merkle  bounded and progressive trees, indices, and verification

Hashing uses `EthLib.Cryptography.Hash.Sha256`.

The properties proved of these definitions sit under `EthLib.Serialization.Proofs.Ssz`, mirroring this layout.
-/
