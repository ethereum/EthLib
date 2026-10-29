import EthLib.Serialization.Ssz.Type.Desc
import EthLib.Serialization.Ssz.Type.Value
import EthLib.Serialization.Ssz.Type.Valid
import EthLib.Serialization.Ssz.Type.Default
import EthLib.Serialization.Ssz.Type.Paths
import EthLib.Serialization.Ssz.Codec.Error
import EthLib.Serialization.Ssz.Codec.Serialize
import EthLib.Serialization.Ssz.Codec.Deserialize
import EthLib.Serialization.Ssz.Codec.Layout
import EthLib.Serialization.Ssz.Codec.Json
import EthLib.Serialization.Ssz.Codec.Root
import EthLib.Serialization.Ssz.Codec.Proof
import EthLib.Serialization.Ssz.Merkle.Chunk
import EthLib.Serialization.Ssz.Merkle.Merkleize
import EthLib.Serialization.Ssz.Merkle.Tree
import EthLib.Serialization.Ssz.Merkle.Gindex
import EthLib.Serialization.Ssz.Merkle.Verify

/-!
# `EthLib.Serialization.Ssz`

Simple Serialize (SSZ), as `consensus-specs` defines it in `ssz/simple-serialize.md` and `ssz/merkle-proofs.md`.

    Ssz/Type    declarations, values, well-formedness, defaults, and paths
    Ssz/Codec   serialization, deserialization, layouts, roots, and proofs
    Ssz/Merkle  bounded and progressive trees, indices, and verification

Hashing uses `EthLib.Cryptography.Hash.Sha256`.

The properties proved of these definitions sit under `EthLib.Serialization.Proofs.Ssz`, mirroring this layout.
-/
