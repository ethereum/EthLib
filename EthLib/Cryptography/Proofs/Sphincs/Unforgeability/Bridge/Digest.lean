module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Fors

/-!
# Proofs: EthLib's message digest is the model's

EthLib's message digest makes the model's two digest calls, in the same order.

EthLib keeps the 64 bytes of the calls, and the model keeps their low 266 bits.

Both read the index from bits 0 to 25 and the leaf of tree `κ` from bits `26 + 10 κ` to `35 + 10 κ`.

So EthLib's index and leaves are the model's, read from the same calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity.Concrete (sequenceFin)

/-- The model's digest calls as EthLib's digest bytes, call 0 first. -/
def ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) : MessageDigest :=
  (Vector.ofFn fun call : Fin DIGEST_CALLS => ofOutput (outs ⟨call.val, call.isLt⟩)).flatten

/-- A fold from the most significant byte down adds the start, scaled past the bytes. -/
theorem foldr_bytes_acc (l : List UInt8) (acc : Nat) :
    l.foldr (fun byte acc => byte.toNat + 256 * acc) acc
      = l.foldr (fun byte acc => byte.toNat + 256 * acc) 0 + 256 ^ l.length * acc := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldr_cons, ih, List.length_cons, pow_succ]
    ring

/-- Two byte strings in a row read as one number: the first is the low part. -/
theorem bytesToUint_flatten_two {k : Nat} (g : Fin 2 → Vector UInt8 k) :
    bytesToUint (Vector.ofFn g).flatten = bytesToUint (g 0) + 256 ^ k * bytesToUint (g 1) := by
  have hl : (Vector.ofFn g).flatten.toList = (g 0).toList ++ (g 1).toList := by
    simp [Vector.flatten, Vector.toList, Array.toList_flatten, Array.toList_ofFn, List.ofFn_succ,
      Function.comp_def]
  rw [Base.bytesToUint_eq_foldr, hl, List.foldr_append, foldr_bytes_acc,
    Base.bytesToUint_eq_foldr, Base.bytesToUint_eq_foldr, Vector.length_toList]

/-- The bytes of the two calls read as one number: call 0 is the low part. -/
theorem bytesToUint_ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) :
    bytesToUint (ofOutputs outs) = SphincsSecurity.digestValue outs := by
  have h := bytesToUint_flatten_two fun call : Fin 2 => ofOutput (outs ⟨call.val, call.isLt⟩)
  have hsum : SphincsSecurity.digestValue outs
      = (outs ⟨0, by decide⟩).toNat + 2 ^ 256 * (outs ⟨1, by decide⟩).toNat :=
    (Fin.sum_univ_two fun call : Fin 2 =>
      (outs ⟨call.val, call.isLt⟩).toNat * 2 ^ (256 * call.val)).trans (by simp; ring)
  refine h.trans ?_
  have hb (x : HashSig.HashOutput) : bytesToUint (ofOutput x) = x.toNat :=
    HashSig.bytesToUint_ofBV 32 x
  simp only [hsum, hb]
  rfl

/-- Bits `a` to `a + b - 1` of a number are those of its low `n` bits, when `a + b ≤ n`. -/
theorem mod_two_pow_div_mod (v n a b : Nat) (h : a + b ≤ n) :
    v % 2 ^ n / 2 ^ a % 2 ^ b = v / 2 ^ a % 2 ^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < b
  · have hn : i + a < n := by omega
    simp [hi, hn]
  · simp [hi]

/-- EthLib's index is the model's index of the same calls. -/
theorem digestIndex_ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) :
    digestIndex (ofOutputs outs)
      = (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest outs)).val := by
  rw [digestIndex, bytesToUint_ofOutputs]
  simp only [SphincsSecurity.Concrete.digestIndex, SphincsSecurity.truncateMessageDigest,
    BitVec.val_toFin, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  exact (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2
    (by decide : SphincsSecurity.totalHeight ≤ SphincsSecurity.messageDigestBits))).symm

/-- EthLib's leaves are the model's leaves of the same calls. -/
theorem digestLeaves_ofOutputs (outs : SphincsSecurity.DigestCall → HashSig.HashOutput) :
    digestLeaves (ofOutputs outs)
      = ofLeaves (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest outs)) := by
  apply Vector.ext
  intro i hi
  simp only [digestLeaves, ofLeaves, Vector.getElem_ofFn, bytesToUint_ofOutputs,
    SphincsSecurity.Concrete.digestLeaves, SphincsSecurity.truncateMessageDigest,
    SphincsSecurity.Concrete.leafOffset]
  apply Fin.ext
  simp only [BitVec.val_toFin, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have hle : SphincsSecurity.totalHeight + SphincsSecurity.forsHeight * i
      + SphincsSecurity.forsHeight ≤ SphincsSecurity.messageDigestBits := by
    change 26 + 10 * i + 10 ≤ 266
    simp only [FORS_TREES] at hi
    omega
  exact (mod_two_pow_div_mod _ _ _ _ hle).symm

section Query

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-- EthLib's message digest is the model's digest calls, in EthLib's bytes. -/
theorem messageDigest_queryH (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (msg : SphincsSecurity.Message) (rho : SphincsSecurity.Randomness) :
    messageDigest (queryH (m := m)) (ofParam P) (ofMessage msg) (ofRandomizer rho)
      = ofOutputs <$> sequenceFin (m := m)
          (SphincsSecurity.Concrete.messageDigestCall P root msg rho) := by
  have h : DIGEST_CALLS = SphincsSecurity.digestCalls := rfl
  have hcalls : (fun call : Fin DIGEST_CALLS => thFull (queryH (m := m)) (ofParam P)
      (addrMsg call) (packBytes (ofMessage msg) ++ packBytes (ofRandomizer rho)))
      = fun call => (ofOutput <$> SphincsSecurity.Concrete.messageDigestCall (m := m) P root msg
          rho (Fin.cast h call) : m EthLib.Cryptography.Sphincs.HashOutput) :=
    funext fun call => digestCall_queryH P root msg rho (Fin.cast h call)
  rw [messageDigest, hcalls,
    ofFnInOrder_eq_sequenceFin_cast (β := EthLib.Cryptography.Sphincs.HashOutput) h
    (SphincsSecurity.Concrete.messageDigestCall (m := m) P root msg rho) ofOutput]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

end Query

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
