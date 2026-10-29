import EthLib.Consensus.Ssz.Type.Desc
import EthLib.Consensus.Ssz.Type.Value
import EthLib.Consensus.Ssz.Type.Valid
import EthLib.Consensus.Ssz.Type.Default
import EthLib.Consensus.Ssz.Type.Paths
import EthLib.Consensus.Ssz.Codec.Error
import EthLib.Consensus.Ssz.Codec.Serialize
import EthLib.Consensus.Ssz.Codec.Deserialize
import EthLib.Consensus.Ssz.Codec.Layout
import EthLib.Consensus.Ssz.Codec.Json
import EthLib.Consensus.Ssz.Codec.Root
import EthLib.Consensus.Ssz.Codec.Proof
import EthLib.Consensus.Ssz.Merkle.Chunk
import EthLib.Consensus.Ssz.Merkle.Merkleize
import EthLib.Consensus.Ssz.Merkle.Tree
import EthLib.Consensus.Ssz.Merkle.Gindex
import EthLib.Consensus.Ssz.Merkle.Verify

/-!
# `EthLib.Consensus.Ssz`

Simple Serialize (SSZ), as `consensus-specs` defines it in `ssz/simple-serialize.md` and `ssz/merkle-proofs.md`.

    Ssz/Type    declarations, values, well-formedness, defaults, and paths
    Ssz/Codec   serialization, deserialization, layouts, roots, and proofs
    Ssz/Merkle  bounded and progressive trees, indices, and verification

Hashing uses `EthLib.Cryptography.Hash.Sha256`.

The properties proved of these definitions sit under `EthLib.Consensus.Proofs.Ssz`, mirroring this layout.
-/
