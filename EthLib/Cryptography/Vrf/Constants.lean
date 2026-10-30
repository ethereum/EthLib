/-!
# `Vrf.Constants`

The parameters of the VRF tree.
-/

namespace EthLib.Cryptography.Vrf.Constants

/-- The height of the tree.

One leaf per index, so the indices are `[0, 2^32)`. -/
def VRF_TREE_HEIGHT : Nat := 32

/-- The size in bytes of a root, a node, a leaf secret and an output.

Uniqueness must hold against the validator that built the tree.

That validator only needs a collision, which costs about `2^(4n)` hashes for `n` bytes.

So 32 bytes give `2^128`, where 16 bytes would give only `2^64`. -/
def VRF_HASH_SIZE : Nat := 32

/-- The size in bytes of an opening: the secret, then one sibling per level.

```text
    32 * (1 + 32) = 1056
```
-/
def VRF_OPENING_SIZE : Nat := 1056

/-- The size in bytes of the seed every leaf secret derives from.

256 bits, so guessing the seed is no easier than guessing a secret. -/
def VRF_SEED_SIZE : Nat := 32

/-- The prefix of a leaf hash: the ASCII bytes of `PQ_VRF_LEAF`. -/
def VRF_LEAF_DST : Vector UInt8 11 :=
  #v[0x50, 0x51, 0x5f, 0x56, 0x52, 0x46, 0x5f, 0x4c, 0x45, 0x41, 0x46]

/-- The prefix of a node hash: the ASCII bytes of `PQ_VRF_NODE`. -/
def VRF_NODE_DST : Vector UInt8 11 :=
  #v[0x50, 0x51, 0x5f, 0x56, 0x52, 0x46, 0x5f, 0x4e, 0x4f, 0x44, 0x45]

/-- The prefix of an output hash: the ASCII bytes of `PQ_VRF_OUTPUT`. -/
def VRF_OUTPUT_DST : Vector UInt8 13 :=
  #v[0x50, 0x51, 0x5f, 0x56, 0x52, 0x46, 0x5f, 0x4f, 0x55, 0x54, 0x50, 0x55, 0x54]

/-- The prefix of a leaf secret: the ASCII bytes of `PQ_VRF_SECRET`. -/
def VRF_SECRET_DST : Vector UInt8 13 :=
  #v[0x50, 0x51, 0x5f, 0x56, 0x52, 0x46, 0x5f, 0x53, 0x45, 0x43, 0x52, 0x45, 0x54]

end EthLib.Cryptography.Vrf.Constants
