module

public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Cryptography.Vrf.KeyGen
public import EthLib.Cryptography.Proofs.Vrf.Verify

/-!
# Proofs: VRF key generation

- A secret input is 49 bytes, so it is never a leaf, node or output input.
- A secret input determines its seed and its index.
- The tree of a seed verifies at every index, with the output of that index's secret.
- Every valid opening of that tree gives that output.
  Otherwise the collision search returns a Keccak-256 collision.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## The secret input -/

/-- The secret prefix is the string `PQ_VRF_SECRET`. -/
theorem VRF_SECRET_DST_eq : VRF_SECRET_DST.toList = "PQ_VRF_SECRET".toUTF8.toList := by
  -- Use the public string equation before reducing the ASCII bytes.
  rw [String.toUTF8_eq_toByteArray]
  decide +kernel

/-- A secret hash reads 13 + 32 + 4 = 49 bytes. -/
@[simp] theorem size_secretInput (seed : Seed) (i : UInt32) : (secretInput seed i).size = 49 := by
  simp only [secretInput, ByteArray.size_append, size_packBytes]
  rfl

/-- A secret input determines its seed and its index. -/
theorem secretInput_inj {seed seed' : Seed} {i i' : UInt32} :
    secretInput seed i = secretInput seed' i' ↔ seed = seed' ∧ i = i' := by
  constructor
  · intro h
    have hd := congrArg ByteArray.data h
    simp only [secretInput, ByteArray.data_append, packBytes] at hd
    -- The index starts at byte 45 on both sides.
    obtain ⟨hps, hi⟩ := Array.append_inj hd (by simp)
    -- The seed starts at byte 13 on both sides.
    obtain ⟨-, hs⟩ := Array.append_inj hps (by simp)
    -- Both indices are below `2^32 = 256^4`, so their four little-endian bytes are exact.
    exact ⟨Vector.toArray_inj.mp hs, UInt32.toNat_inj.mp (Base.uintToBytes_inj
      (lt_of_lt_of_eq i.toNat_lt (by decide)) (lt_of_lt_of_eq i'.toNat_lt (by decide))
      (Vector.toArray_inj.mp hi))⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A secret input is never a leaf input. -/
theorem secretInput_ne_leafInput (seed : Seed) (i : UInt32) (s : Digest) :
    secretInput seed i ≠ leafInput s := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A secret input is never a node input. -/
theorem secretInput_ne_nodeInput (seed : Seed) (i : UInt32) (l r : Digest) :
    secretInput seed i ≠ nodeInput l r := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-- A secret input is never an output input. -/
theorem secretInput_ne_outputInput (seed : Seed) (i : UInt32) (s : Digest) :
    secretInput seed i ≠ outputInput s := by
  intro h
  have := congrArg ByteArray.size h
  simp at this

/-! ## The tree of a seed -/

/-- The opening at index `i` of a seed's tree verifies under its root, with the output at `i`. -/
theorem verify_prove (seed : Seed) (i : UInt32) :
    verify (keyGen seed) i (prove seed i) = some (evaluate seed i) :=
  verify_opening (secret seed) i

/-- Every valid opening of a seed's tree at index `i` gives the output at `i`.

Otherwise the collision search returns a Keccak-256 collision with the honest opening. -/
theorem verify_keyGen_unique {seed : Seed} {i : UInt32} {o : Opening} {y : Digest}
    (h : verify (keyGen seed) i o = some y) :
    y = evaluate seed i ∨
      ∃ p, findHashCollision i o (prove seed i) = some p ∧ IsHashCollision p :=
  verify_root_unique h

end EthLib.Cryptography.Vrf
