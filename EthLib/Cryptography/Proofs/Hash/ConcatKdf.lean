module

public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Cryptography.Hash.ConcatKdf

/-!
# Proofs: the Concatenation KDF

A successful derivation has exactly the requested length.

A shorter output is a prefix of a longer one.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.ConcatKdf

/-- The blocks of the derivation are 32 bytes each. -/
theorem blocks_size (z fixedInfo : ByteArray) (i count : Nat) :
    (blocks z fixedInfo i count).size = HASH_LEN * count := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [blocks, ByteArray.size_append, Sha256.hash_size, ih, HASH_LEN]
    omega

/-- More blocks extend fewer: the counter of each block depends only on its position. -/
theorem blocks_add (z fixedInfo : ByteArray) (i a b : Nat) :
    blocks z fixedInfo i (a + b) = blocks z fixedInfo i a ++ blocks z fixedInfo (i + a) b := by
  induction a generalizing i with
  | zero => simp [blocks]
  | succ a ih =>
    rw [Nat.add_right_comm, blocks, ih, blocks, ByteArray.append_assoc, Nat.add_right_comm i 1 a]
    rfl

/-- The blocks of a successful derivation, before the cut to the requested length. -/
theorem concatKdf_eq_extract {z fixedInfo key : ByteArray} {length : Nat}
    (h : concatKdf z fixedInfo length = .ok key) :
    key = (blocks z fixedInfo 1 ((length + HASH_LEN - 1) / HASH_LEN)).extract 0 length := by
  unfold concatKdf at h
  by_cases empty : length = 0
  · simp [empty] at h
  by_cases long : 2 ^ 32 - 1 < (length + HASH_LEN - 1) / HASH_LEN
  · simp [empty, long] at h
  by_cases input : 2 ^ 61 ≤ 4 + z.size + fixedInfo.size
  · simp [empty, long, input] at h
  simp only [empty, long, input, ite_false] at h
  exact (Except.ok.inj h).symm

/-- A successful derivation has exactly the requested length. -/
theorem concatKdf_size {z fixedInfo key : ByteArray} {length : Nat}
    (h : concatKdf z fixedInfo length = .ok key) : key.size = length := by
  -- The blocks cover the output, so the extraction keeps the requested length.
  rw [concatKdf_eq_extract h]
  simp only [ByteArray.size_extract, blocks_size, HASH_LEN]
  omega

/-- A shorter output is a prefix of a longer one, for one shared secret and one context.

SP 800-56C Rev. 2 §4.1 builds the output block by block, so the length only cuts it. -/
theorem concatKdf_prefix {z fixedInfo key key' : ByteArray} {length length' : Nat}
    (h : concatKdf z fixedInfo length = .ok key) (h' : concatKdf z fixedInfo length' = .ok key')
    (le : length ≤ length') : key = key'.extract 0 length := by
  rw [concatKdf_eq_extract h, concatKdf_eq_extract h']
  -- The longer derivation has at least as many blocks, and starts with the shorter one's.
  obtain ⟨more, hmore⟩ : ∃ more, (length' + HASH_LEN - 1) / HASH_LEN =
      (length + HASH_LEN - 1) / HASH_LEN + more :=
    ⟨_, (Nat.add_sub_cancel' (Nat.div_le_div_right (by omega))).symm⟩
  rw [hmore, blocks_add, ByteArray.extract_extract, Nat.zero_add, Nat.zero_add,
    Nat.min_eq_left le, ByteArray.extract_append]
  -- The shorter derivation's blocks already cover its length, so nothing comes from the rest.
  have covers : length ≤ (blocks z fixedInfo 1 ((length + HASH_LEN - 1) / HASH_LEN)).size := by
    simp only [blocks_size, HASH_LEN]
    omega
  rw [Nat.sub_eq_zero_of_le covers, Nat.zero_sub, ByteArray.extract_same, ByteArray.append_empty]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem ConcatKdfError.code_injective (e₁ e₂ : ConcatKdfError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ConcatKdfError.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Hash.ConcatKdf
