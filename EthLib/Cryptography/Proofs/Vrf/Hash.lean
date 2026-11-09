module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Cryptography.Vrf.Hash

/-!
# Proofs: VRF hashes

The four hash inputs are separated.

- Each prefix is the ASCII string the specification names.
- Each input determines its arguments.
- No input of one hash is an input of another: they are 43, 75, 49 and 74 bytes long.

So a collision among these hashes is a Keccak-256 collision on two inputs of one kind.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## The constants -/

/-- The leaf prefix is the string `PQ_VRF_LEAF`. -/
theorem VRF_LEAF_DST_eq : VRF_LEAF_DST.toList = "PQ_VRF_LEAF".toUTF8.toList := by
  -- Use the public string equation before reducing the ASCII bytes.
  rw [String.toUTF8_eq_toByteArray]
  decide +kernel

/-- The node prefix is the string `PQ_VRF_NODE`. -/
theorem VRF_NODE_DST_eq : VRF_NODE_DST.toList = "PQ_VRF_NODE".toUTF8.toList := by
  -- Use the public string equation before reducing the ASCII bytes.
  rw [String.toUTF8_eq_toByteArray]
  decide +kernel

/-- The output prefix is the string `PQ_VRF_OUTPUT`. -/
theorem VRF_OUTPUT_DST_eq : VRF_OUTPUT_DST.toList = "PQ_VRF_OUTPUT".toUTF8.toList := by
  -- Use the public string equation before reducing the ASCII bytes.
  rw [String.toUTF8_eq_toByteArray]
  decide +kernel

/-- The mix prefix is the string `PQ_VRF_MIX`. -/
theorem VRF_MIX_DST_eq : VRF_MIX_DST.toList = "PQ_VRF_MIX".toUTF8.toList := by
  -- Use the public string equation before reducing the ASCII bytes.
  rw [String.toUTF8_eq_toByteArray]
  decide +kernel

/-- An opening is a secret and one sibling per level, 32 bytes each. -/
theorem VRF_OPENING_SIZE_eq : VRF_OPENING_SIZE = VRF_HASH_SIZE * (1 + VRF_TREE_HEIGHT) :=
  rfl

/-! ## Sizes -/

export EthLib.Base (size_packBytes packBytes_injective)

/-- A leaf hash reads 11 + 32 = 43 bytes. -/
@[simp] theorem size_leafInput (s : Digest) : (leafInput s).size = 43 := by
  simp only [leafInput, ByteArray.size_append, size_packBytes]
  rfl

/-- A node hash reads 11 + 32 + 32 = 75 bytes. -/
@[simp] theorem size_nodeInput (l r : Digest) : (nodeInput l r).size = 75 := by
  simp only [nodeInput, ByteArray.size_append, size_packBytes]
  rfl

/-- An output hash reads 13 + 4 + 32 = 49 bytes. -/
@[simp] theorem size_outputInput (i : UInt32) (s : Digest) : (outputInput i s).size = 49 := by
  simp only [outputInput, ByteArray.size_append, size_packBytes]
  rfl

/-- A mixed value reads 10 + 32 + 32 = 74 bytes. -/
@[simp] theorem size_mixInput (y r : Digest) : (mixInput y r).size = 74 := by
  simp only [mixInput, ByteArray.size_append, size_packBytes]
  rfl

/-! ## Each input determines its arguments -/

/-- Two packed objects of fixed sizes split back one way. -/
private theorem packBytes_append_inj {m n : Nat} {a a' : Vector UInt8 m} {b b' : Vector UInt8 n}
    (h : packBytes a ++ packBytes b = packBytes a' ++ packBytes b') : a = a' ∧ b = b' := by
  have hd := congrArg ByteArray.data h
  simp only [ByteArray.data_append, packBytes] at hd
  -- The first object has the same size on both sides, so the split point is the same.
  obtain ⟨h1, h2⟩ := Array.append_inj hd (by simp)
  exact ⟨Vector.toArray_inj.mp h1, Vector.toArray_inj.mp h2⟩

/-- A leaf hash input determines its secret. -/
theorem leafInput_inj {s s' : Digest} : leafInput s = leafInput s' ↔ s = s' := by
  constructor
  · intro h
    exact (packBytes_append_inj h).2
  · rintro rfl
    rfl

/-- A node hash input determines its two children. -/
theorem nodeInput_inj {l r l' r' : Digest} : nodeInput l r = nodeInput l' r' ↔ l = l' ∧ r = r' := by
  constructor
  · intro h
    have hd := congrArg ByteArray.data h
    simp only [nodeInput, ByteArray.data_append, packBytes] at hd
    -- The right child starts at byte 43 on both sides.
    obtain ⟨hpl, hr⟩ := Array.append_inj hd (by simp)
    -- The left child starts at byte 11 on both sides.
    obtain ⟨-, hl⟩ := Array.append_inj hpl (by simp)
    exact ⟨Vector.toArray_inj.mp hl, Vector.toArray_inj.mp hr⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- An output hash input determines its index and its secret. -/
theorem outputInput_inj {i i' : UInt32} {s s' : Digest} :
    outputInput i s = outputInput i' s' ↔ i = i' ∧ s = s' := by
  constructor
  · intro h
    have hd := congrArg ByteArray.data h
    simp only [outputInput, ByteArray.data_append, packBytes] at hd
    -- The secret starts at byte 17 on both sides.
    obtain ⟨hpi, hs⟩ := Array.append_inj hd (by simp)
    -- The index starts at byte 13 on both sides.
    obtain ⟨-, hi⟩ := Array.append_inj hpi (by simp)
    -- Both indices are below `2^32 = 256^4`, so their four little-endian bytes are exact.
    exact ⟨UInt32.toNat_inj.mp (Base.uintToBytes_inj
      (lt_of_lt_of_eq i.toNat_lt (by decide)) (lt_of_lt_of_eq i'.toNat_lt (by decide))
      (Vector.toArray_inj.mp hi)), Vector.toArray_inj.mp hs⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A mixed input determines its output and its randomness. -/
theorem mixInput_inj {y r y' r' : Digest} : mixInput y r = mixInput y' r' ↔ y = y' ∧ r = r' := by
  constructor
  · intro h
    have hd := congrArg ByteArray.data h
    simp only [mixInput, ByteArray.data_append, packBytes] at hd
    -- The randomness starts at byte 42 on both sides.
    obtain ⟨hpy, hr⟩ := Array.append_inj hd (by simp)
    -- The output starts at byte 10 on both sides.
    obtain ⟨-, hy⟩ := Array.append_inj hpy (by simp)
    exact ⟨Vector.toArray_inj.mp hy, Vector.toArray_inj.mp hr⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## No input of one hash is an input of another -/

/-- A leaf input is never a node input. -/
theorem leafInput_ne_nodeInput (s l r : Digest) : leafInput s ≠ nodeInput l r := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A leaf input is never an output input. -/
theorem leafInput_ne_outputInput (s : Digest) (i : UInt32) (s' : Digest) :
    leafInput s ≠ outputInput i s' := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A node input is never an output input. -/
theorem nodeInput_ne_outputInput (l r : Digest) (i : UInt32) (s : Digest) :
    nodeInput l r ≠ outputInput i s := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A mixed input is never a leaf input. -/
theorem mixInput_ne_leafInput (y r s : Digest) : mixInput y r ≠ leafInput s := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A mixed input is never a node input. -/
theorem mixInput_ne_nodeInput (y r l r' : Digest) : mixInput y r ≠ nodeInput l r' := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A mixed input is never an output input. -/
theorem mixInput_ne_outputInput (y r : Digest) (i : UInt32) (s : Digest) :
    mixInput y r ≠ outputInput i s := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

end EthLib.Cryptography.Vrf
