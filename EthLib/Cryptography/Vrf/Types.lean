import EthLib.Cryptography.Vrf.Constants

/-!
# `Vrf.Types`

The objects of the VRF tree, with their sizes in their types.
-/

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

/-- The bytes of a fixed-size object, in order. -/
def packBytes {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  -- The length is in the type, so nothing is checked here.
  ⟨v.toArray⟩

/-- Read the `n` bytes of a buffer that start at an offset.

The caller proves the buffer has room, so no byte is invented. -/
def readBytes (b : ByteArray) (offset n : Nat) (h : offset + n ≤ b.size) : Vector UInt8 n :=
  -- Byte `i` of the object is byte `offset + i` of the buffer.
  Vector.ofFn fun i => b.data[offset + i.val]'(by
    simp only [ByteArray.size] at h
    omega)

/-- `LE32(i)`: the four bytes of an index, least significant first.

Example: `indexBytes 0x01020304 = #v[0x04, 0x03, 0x02, 0x01]`. -/
def indexBytes (i : UInt32) : Vector UInt8 4 :=
  -- Byte `k` holds bits `8k` to `8k + 7`.
  Vector.ofFn fun k => UInt8.ofNat (i.toNat >>> (8 * k.val))

end EthLib.Cryptography.Vrf
