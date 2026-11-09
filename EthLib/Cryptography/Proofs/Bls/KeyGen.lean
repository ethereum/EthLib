module

public import EthLib.Cryptography.Bls.KeyGen
public import EthLib.Cryptography.Proofs.Hash.Hkdf

/-!
# Proofs: BLS key generation

Source: draft-irtf-cfrg-bls-signature-04, §2.3.

The output length is the one the draft derives from the bit length of `r`.

HKDF never fails inside key generation.

So key generation fails only on a short input, or when every attempt gives a multiple of `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Signatures

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Hash

/-- `r` has 255 bits, so `ceil(log2(r)) = 255`, and `L = ceil(3 * 255 / 16)`. -/
theorem keyGen_L_eq : 2 ^ 254 < Fr.modulus ∧ Fr.modulus < 2 ^ 255 ∧
    KEYGEN_L = (3 * 255 + 15) / 16 :=
  ⟨by decide, by decide, rfl⟩

/-- Key generation rejects fewer than 32 bytes of input keying material. -/
theorem keyGen_ikmTooShort {ikm : ByteArray} (h : ikm.size < 32) (keyInfo : ByteArray) :
    keyGen ikm keyInfo = .error (.keyGenIkmTooShort ikm.size) := by
  unfold keyGen
  simp only [h, ↓reduceIte]

/-- A success relabelled and passed on is the value passed on.

It is stated on variables, so the kernel never reduces a field element to compare two forms. -/
private theorem mapError_ok_bind {ε ε' α β : Type} (f : ε → ε') (a : α)
    (k : α → Except ε' β) : (Except.mapError f (.ok a) >>= k) = k a :=
  rfl

/-- HKDF never fails in an attempt: its pseudorandom key has 32 bytes, and its output 48. -/
theorem keyGenLoop_ne_hkdf (ikm keyInfo salt : ByteArray) (attempts : Nat) :
    keyGenLoop ikm keyInfo salt attempts ≠ .error .keyGenHkdf := by
  induction attempts generalizing salt with
  | zero => intro h; cases h
  | succ attempts ih =>
    intro h
    rw [keyGenLoop] at h
    -- Name the expansion, so that no tactic evaluates the hashes.
    generalize hx : Hkdf.expand _ _ KEYGEN_L = r at h
    -- The key has 32 bytes and the output 48, so the expansion succeeds.
    obtain ⟨okm, rfl⟩ : ∃ okm, r = .ok okm :=
      ⟨_, hx.symm.trans (Hkdf.expand_eq (by simp [Hkdf.extract, Hkdf.HASH_LEN])
        (by simp [KEYGEN_L, Hkdf.HASH_LEN]))⟩
    rw [mapError_ok_bind] at h
    generalize Fr.ofNat (Base.bytesToNat okm.data.toList) = sk at h
    dsimp only at h
    split at h
    · exact ih _ h
    · cases h

/-- Key generation never fails inside HKDF. -/
theorem keyGen_ne_hkdf (ikm keyInfo : ByteArray) :
    keyGen ikm keyInfo ≠ .error .keyGenHkdf := by
  unfold keyGen
  split
  · intro h; cases h
  · exact keyGenLoop_ne_hkdf _ _ _ _

/-- An attempt gives a key, or the attempts run out.

The expansion inside an attempt always succeeds, so running out is the only failure. -/
theorem keyGenLoop_eq_ok_or_noKey (ikm keyInfo salt : ByteArray) (attempts : Nat) :
    (∃ sk, keyGenLoop ikm keyInfo salt attempts = .ok sk) ∨
      keyGenLoop ikm keyInfo salt attempts = .error .keyGenNoKey := by
  induction attempts generalizing salt with
  | zero => exact Or.inr rfl
  | succ attempts ih =>
    rw [keyGenLoop]
    -- Name the expansion, so that no tactic evaluates the hashes.
    generalize hx : Hkdf.expand _ _ KEYGEN_L = r
    -- The key has 32 bytes and the output 48, so the expansion succeeds.
    obtain ⟨okm, rfl⟩ : ∃ okm, r = .ok okm :=
      ⟨_, hx.symm.trans (Hkdf.expand_eq (by simp [Hkdf.extract, Hkdf.HASH_LEN])
        (by simp [KEYGEN_L, Hkdf.HASH_LEN]))⟩
    rw [mapError_ok_bind]
    generalize Fr.ofNat (Base.bytesToNat okm.data.toList) = sk
    dsimp only
    split
    · exact ih _
    · exact Or.inl ⟨_, rfl⟩

/-- Long enough input keying material gives a key, or the attempts run out. -/
theorem keyGen_eq_ok_or_noKey_of_size {ikm : ByteArray} (h : 32 ≤ ikm.size)
    (keyInfo : ByteArray) :
    (∃ sk, keyGen ikm keyInfo = .ok sk) ∨ keyGen ikm keyInfo = .error .keyGenNoKey := by
  unfold keyGen
  simp only [Nat.not_lt.mpr h, ↓reduceIte]
  exact keyGenLoop_eq_ok_or_noKey _ _ _ _

/-- Key generation fails only on a short input, or on a multiple of `r` in every attempt.

A caller that reads the error code needs this to rule out the other codes. -/
theorem keyGen_eq_ikmTooShort_or_ok_or_noKey (ikm keyInfo : ByteArray) :
    keyGen ikm keyInfo = .error (.keyGenIkmTooShort ikm.size) ∨
      (∃ sk, keyGen ikm keyInfo = .ok sk) ∨
      keyGen ikm keyInfo = .error .keyGenNoKey := by
  by_cases h : ikm.size < 32
  · exact Or.inl (keyGen_ikmTooShort h keyInfo)
  · exact Or.inr (keyGen_eq_ok_or_noKey_of_size (Nat.not_lt.mp h) keyInfo)

/-- The first attempt decides the key, unless its expansion is a multiple of `r`.

The draft repeats an attempt only to avoid a zero key.

This names the key of one attempt: `OS2IP(OKM) mod r` under the hashed salt. -/
theorem keyGenLoop_eq_ok_of_ne_zero (ikm keyInfo salt okm : ByteArray) (attempts : Nat)
    (hokm : Hkdf.expand (Hkdf.extract (Sha256.hash salt) (ikm ++ HashToCurve.i2osp 0 1))
      (keyInfo ++ HashToCurve.i2osp KEYGEN_L 2) KEYGEN_L = .ok okm)
    (h : Fr.ofNat (Base.bytesToNat okm.data.toList) ≠ 0) :
    keyGenLoop ikm keyInfo salt (attempts + 1) = .ok ⟨_, h⟩ := by
  rw [keyGenLoop, hokm, mapError_ok_bind]
  dsimp only
  split
  · exact absurd ‹_› h
  · rfl

/-- A multiple of `r` moves to the next attempt, under the hashed salt.

The draft hashes the salt between attempts, so the next attempt uses `SHA-256(salt)`. -/
theorem keyGenLoop_eq_of_eq_zero (ikm keyInfo salt okm : ByteArray) (attempts : Nat)
    (hokm : Hkdf.expand (Hkdf.extract (Sha256.hash salt) (ikm ++ HashToCurve.i2osp 0 1))
      (keyInfo ++ HashToCurve.i2osp KEYGEN_L 2) KEYGEN_L = .ok okm)
    (h : Fr.ofNat (Base.bytesToNat okm.data.toList) = 0) :
    keyGenLoop ikm keyInfo salt (attempts + 1) =
      keyGenLoop ikm keyInfo (Sha256.hash salt) attempts := by
  rw [keyGenLoop, hokm, mapError_ok_bind]
  dsimp only
  split
  · rfl
  · exact absurd h ‹_›

end EthLib.Cryptography.Bls.Signatures
