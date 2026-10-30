import EthLib.Cryptography.Vrf.KeyGen
import EthLib.Cryptography.Proofs.Vrf.Verify

/-!
# Proofs: `Vrf.KeyGen`

- A secret input is 49 bytes, so it is never a leaf, node or output input.
- A secret input determines its seed and its index.
- The tree of a seed verifies at every index, with the output of that index's secret.
- Every valid opening of that tree gives that output, or Keccak-256 collides.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## The secret input -/

/-- The secret prefix is the string `PQ_VRF_SECRET`. -/
theorem VRF_SECRET_DST_eq : VRF_SECRET_DST.toList = "PQ_VRF_SECRET".toUTF8.toList := by
  decide +kernel

/-- A secret hash reads 13 + 32 + 4 = 49 bytes. -/
@[simp] theorem size_secretInput (seed : Seed) (i : UInt32) : (secretInput seed i).size = 49 := by
  simp only [secretInput, ByteArray.size_append, size_packBytes]
  rfl

/-- Byte `k` of an index is `floor(i / 2^(8k)) mod 256`. -/
private theorem indexBytes_toNat (x : UInt32) (k : Nat) (hk : k < 4) :
    ((indexBytes x)[k]).toNat = x.toNat / 2 ^ (8 * k) % 256 := by
  simp [indexBytes, Nat.shiftRight_eq_div_pow]

/-- The four bytes of an index determine it. -/
theorem indexBytes_inj {i j : UInt32} (h : indexBytes i = indexBytes j) : i = j := by
  -- Read the same byte on both sides, for each of the four bytes.
  have same : ∀ k (hk : k < 4), i.toNat / 2 ^ (8 * k) % 256 = j.toNat / 2 ^ (8 * k) % 256 :=
    fun k hk => by rw [← indexBytes_toNat i k hk, ← indexBytes_toNat j k hk, h]
  have h0 := same 0 (by decide)
  have h1 := same 1 (by decide)
  have h2 := same 2 (by decide)
  have h3 := same 3 (by decide)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] at h0 h1 h2 h3
  -- Four equal bytes of numbers below `2^32` make equal numbers.
  have hi := i.toNat_lt
  have hj := j.toNat_lt
  apply UInt32.toNat_inj.mp
  simp only [Nat.reducePow] at hi hj
  omega

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
    exact ⟨Vector.toArray_inj.mp hs, indexBytes_inj (Vector.toArray_inj.mp hi)⟩
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

/-- Every valid opening of a seed's tree at index `i` gives the output at `i`, or Keccak-256 collides. -/
theorem verify_keyGen_unique {seed : Seed} {i : UInt32} {o : Opening} {y : Digest}
    (h : verify (keyGen seed) i o = some y) : y = evaluate seed i ∨ HashCollision :=
  verify_root_unique h

end EthLib.Cryptography.Vrf
