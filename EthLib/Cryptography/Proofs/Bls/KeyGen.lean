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
    cases r with
    | error e' =>
      have := Hkdf.hkdf_error hx
      simp [KEYGEN_L, Hkdf.HASH_LEN] at this
    | ok okm =>
      simp only [Except.mapError, bind, Except.bind] at h
      generalize Fr.ofNat (Fr.bytesBEToNat okm) = sk at h
      by_cases hs : sk = 0
      · simp only [hs, ↓reduceDIte] at h
        exact ih _ h
      · simp only [hs, ↓reduceDIte] at h
        cases h

/-- Key generation never fails inside HKDF. -/
theorem keyGen_ne_hkdf (ikm keyInfo : ByteArray) :
    keyGen ikm keyInfo ≠ .error .keyGenHkdf := by
  unfold keyGen
  split
  · intro h; cases h
  · exact keyGenLoop_ne_hkdf _ _ _ _

end EthLib.Cryptography.Bls.Signatures
