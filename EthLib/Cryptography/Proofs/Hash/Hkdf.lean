module

public import EthLib.Cryptography.Proofs.Hash.Hmac
public import EthLib.Cryptography.Hash.Hkdf

/-!
# Proofs: HKDF-SHA-256

A successful expansion has exactly the requested length.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Hkdf

open EthLib.Cryptography.Hash.Hmac

/-! ## Lengths -/

/-- The blocks of the expansion are 32 bytes each. -/
theorem expandBlocks_size (prk info previous : ByteArray) (i count : Nat) :
    (expandBlocks prk info previous i count).size = HASH_LEN * count := by
  induction count generalizing previous i with
  | zero => rfl
  | succ count ih =>
    simp only [expandBlocks, ByteArray.size_append, hmac_size, ih, HASH_LEN]
    omega

/-- A successful expansion has exactly the requested length. -/
theorem expand_size {prk info okm : ByteArray} {length : Nat}
    (h : expand prk info length = .ok okm) : okm.size = length := by
  unfold expand at h
  by_cases short : prk.size < HASH_LEN
  · simp [short] at h
  by_cases long : 255 * HASH_LEN < length
  · simp [short, long] at h
  simp only [short, long, ite_false] at h
  -- The blocks cover the output, so the extraction keeps the requested length.
  obtain rfl := Except.ok.inj h
  simp only [ByteArray.size_extract, expandBlocks_size, HASH_LEN]
  omega

/-- The pseudorandom key is 32 bytes, so HKDF fails only on an output longer than `255 * 32`. -/
theorem hkdf_error {salt ikm info : ByteArray} {length : Nat} {e : HkdfError}
    (h : hkdf salt ikm info length = .error e) :
    e = .outputTooLong length ∧ 255 * HASH_LEN < length := by
  unfold hkdf expand extract at h
  simp only [hmac_size, HASH_LEN, show ¬ 32 < 32 by decide, ite_false] at h
  by_cases long : 255 * 32 < length
  · simp only [long, ite_true] at h
    exact ⟨(Except.error.inj h).symm, long⟩
  · simp [long] at h

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem HkdfError.code_injective (e₁ e₂ : HkdfError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [HkdfError.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Hash.Hkdf
