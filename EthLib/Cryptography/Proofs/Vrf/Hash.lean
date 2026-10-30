import EthLib.Cryptography.Vrf.Hash

/-!
# Proofs: `Vrf.Hash`

The three hash inputs are separated.

- Each prefix is the ASCII string the specification names.
- Each input determines its arguments.
- No input of one hash is an input of another: they are 43, 75 and 45 bytes long.

So a collision found among the tree's hashes is a collision of Keccak-256 on two inputs of one kind.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## The constants -/

/-- The leaf prefix is the string `PQ_VRF_LEAF`. -/
theorem VRF_LEAF_DST_eq : VRF_LEAF_DST.toList = "PQ_VRF_LEAF".toUTF8.toList := by
  decide +kernel

/-- The node prefix is the string `PQ_VRF_NODE`. -/
theorem VRF_NODE_DST_eq : VRF_NODE_DST.toList = "PQ_VRF_NODE".toUTF8.toList := by
  decide +kernel

/-- The output prefix is the string `PQ_VRF_OUTPUT`. -/
theorem VRF_OUTPUT_DST_eq : VRF_OUTPUT_DST.toList = "PQ_VRF_OUTPUT".toUTF8.toList := by
  decide +kernel

/-- An opening is a secret and one sibling per level, 32 bytes each. -/
theorem VRF_OPENING_SIZE_eq : VRF_OPENING_SIZE = VRF_HASH_SIZE * (1 + VRF_TREE_HEIGHT) :=
  rfl

/-! ## Sizes -/

/-- An object packs to as many bytes as it has. -/
@[simp] theorem size_packBytes {n : Nat} (v : Vector UInt8 n) : (packBytes v).size = n := by
  simp [packBytes, ByteArray.size]

/-- A leaf hash reads 11 + 32 = 43 bytes. -/
@[simp] theorem size_leafInput (s : Digest) : (leafInput s).size = 43 := by
  simp only [leafInput, ByteArray.size_append, size_packBytes]
  rfl

/-- A node hash reads 11 + 32 + 32 = 75 bytes. -/
@[simp] theorem size_nodeInput (l r : Digest) : (nodeInput l r).size = 75 := by
  simp only [nodeInput, ByteArray.size_append, size_packBytes]
  rfl

/-- An output hash reads 13 + 32 = 45 bytes. -/
@[simp] theorem size_outputInput (s : Digest) : (outputInput s).size = 45 := by
  simp only [outputInput, ByteArray.size_append, size_packBytes]
  rfl

/-! ## Each input determines its arguments -/

/-- Packing is injective. -/
theorem packBytes_inj {n : Nat} {v w : Vector UInt8 n} (h : packBytes v = packBytes w) : v = w := by
  simp only [packBytes, ByteArray.mk.injEq] at h
  exact Vector.toArray_inj.mp h

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

/-- An output hash input determines its secret. -/
theorem outputInput_inj {s s' : Digest} : outputInput s = outputInput s' ↔ s = s' := by
  constructor
  · intro h
    exact (packBytes_append_inj h).2
  · rintro rfl
    rfl

/-! ## No input of one hash is an input of another -/

/-- A leaf input is never a node input. -/
theorem leafInput_ne_nodeInput (s l r : Digest) : leafInput s ≠ nodeInput l r := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A leaf input is never an output input. -/
theorem leafInput_ne_outputInput (s s' : Digest) : leafInput s ≠ outputInput s' := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A node input is never an output input. -/
theorem nodeInput_ne_outputInput (l r s : Digest) : nodeInput l r ≠ outputInput s := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

end EthLib.Cryptography.Vrf
