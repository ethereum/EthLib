module

public import EthLib.Base.Bytes
public import EthLib.Base.LittleEndian
public import EthLib.Cryptography.Vrf.Constants

/-!
# VRF types

The objects of the VRF tree, with their sizes in their types.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-- A 32-byte value: a root, a node, a leaf secret or an output. -/
abbrev Digest := Vector UInt8 VRF_HASH_SIZE

/-- The holder's seed, from which every leaf secret derives. -/
abbrev Seed := Vector UInt8 VRF_SEED_SIZE

/-- An opening at one index: what the holder reveals to prove the output there. -/
structure Opening where
  /-- The secret of the leaf at the index. -/
  secret : Digest
  /-- The siblings of the leaf and of its ancestors, from the leaf up to the root. -/
  path : Vector Digest VRF_TREE_HEIGHT
  deriving DecidableEq, Repr

/-! ## Bytes -/

export EthLib.Base (packBytes readBytes uintToBytes)

end EthLib.Cryptography.Vrf
