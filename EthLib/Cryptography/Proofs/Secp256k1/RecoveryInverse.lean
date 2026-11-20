module

public import EthLib.Cryptography.Secp256k1.RecoveryInverse
import all EthLib.Cryptography.Secp256k1.RecoveryInverse
public import EthLib.Cryptography.Proofs.Secp256k1.Field
public import EthLib.Cryptography.Proofs.Inverse
public import EthLib.Cryptography.Proofs.Montgomery.Fin
import EthLib.Cryptography.Proofs.Secp256k1.RecoveryField

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.RecoveryInverse

/-- A candidate that passes the check equals the inverse computed by exponentiation. -/
theorem check_eq {m : Nat} [NeZero m] [Fact m.Prime] (hm : 2 < m) (c : Option Nat) (a : Fin m) :
    check c a = Fin.inversePrime a := by
  cases c with
  | none => rfl
  | some c =>
    simp only [check]
    split
    · rename_i h
      have hmul : (c : ZMod m) * (a.val : ZMod m) = 1 := by
        rw [← Nat.cast_mul, ← ZMod.natCast_mod (c * a.val) m, h.2, Nat.cast_one]
      have he : (c : ZMod m) = (a.val : ZMod m)⁻¹ := eq_inv_of_mul_eq_one_left hmul
      rw [Fin.inversePrime_eq_inverse hm a]
      apply Fin.ext
      have hv := congrArg ZMod.val (he.trans (Fin.inverse_val a).symm)
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt h.1,
        Nat.mod_eq_of_lt (Fin.inverse a).isLt] using hv
    · rfl

/-- The recovery denominator inverse agrees with exponentiation. -/
theorem invFp_eq (a : Fp) : invFp a = Fin.inversePrime a :=
  check_eq (by decide) _ _

private theorem fn_inversePrime_eq (a : Fn) : Fin.inversePrime a = Fn.inv a :=
  Fin.inversePrime_eq_inverse (by decide) a

/-- The recovery signature component inverse agrees with the standard scalar inverse. -/
theorem invFn_eq (a : Fn) : invFn a = Fn.inv a :=
  (check_eq (by decide) _ a).trans (fn_inversePrime_eq a)

open Fp.RecoveryField in
private theorem checkMontgomery_eq (c : Option Element) (a : Element) :
    checkMontgomery c a = ofFin (Fin.inversePrime (toFin a)) := by
  cases c with
  | none => rfl
  | some b =>
    simp only [checkMontgomery]
    split
    · rename_i h
      have hb : toFin (b * a) = toFin b * toFin a := by
        simp only [toFin_eq, toMont_mul, Montgomery.toFin_mul]
        rfl
      have h1 : toFin (1 : Element) = 1 := by
        rw [toFin_eq, toMont_one, Montgomery.toFin_one]
        rfl
      have hprod : toFin b * toFin a = 1 :=
        hb.symm.trans ((congrArg toFin h).trans h1)
      have hz : Fp.toZMod (toFin b) * Fp.toZMod (toFin a) = 1 := by
        simpa only [map_mul, map_one] using congrArg Fp.toZMod hprod
      have hinj : Function.Injective toFin := by
        rw [show toFin = Montgomery.toFin ∘ toMont from funext toFin_eq]
        exact Montgomery.toFin_injective.comp toMont_injective
      apply hinj
      have decode (x : Fp) : toFin (ofFin x) = x :=
        (toFin_eq _).trans ((congrArg Montgomery.toFin (toMont_ofFin x)).trans
          (Montgomery.toFin_ofFin (M := Fp.params) x))
      rw [decode, Fin.inversePrime_eq_inverse (by decide)]
      apply Fp.toZMod.injective
      change Fp.toZMod (toFin b) = Fp.toZMod (toFin a).inv
      rw [Fp.toZMod_inv]
      exact eq_inv_of_mul_eq_one_left hz
    · rfl

open Fp.RecoveryField in
/-- The denominator inverse agrees with the canonical inverse. -/
theorem invMontgomery_eq (a : Element) :
    invMontgomery a = ofFin (invFp (toFin a)) := by
  rw [invFp_eq]
  unfold invMontgomery
  exact checkMontgomery_eq _ a

section

open Fp.RecoveryField (Raw rawToNat_eq lowValue wordRadix)
open FnRecoveryWords (fromFin toFin)

private theorem wordOne_value (q : Raw)
    (h : q.w0 = 1 ∧ q.w1 = 0 ∧ q.w2 = 0 ∧ q.w3 = 0) : q.val = 1 := by
  simp only [Raw.val, Raw.words, lowValue, h.1, h.2.1, h.2.2.1, h.2.2.2,
    UInt64.toNat_one, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]

private theorem checkFnWords_eq (c : Option Raw) (a : Raw) :
    checkFnWords c a = fromFin (Fin.inversePrime (toFin a)) := by
  cases c with
  | none => rfl
  | some b =>
    simp only [checkFnWords]
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      have hless : b.val < Fn.modulus := by
        by_contra! hge
        have he := (FnRecoveryWords.geOrder_iff b.words).mpr (b.val_eq ▸ hge)
        have bad := h.2.2.2.2
        rw [he] at bad
        contradiction
      have hproduct := wordOne_value (FnRecoveryWords.mul b a)
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      rw [FnRecoveryWords.mul_val] at hproduct
      have hmod : b.val * (toFin a).val % Fn.modulus = 1 := by
        change b.val * (Fp.RecoveryField.rawToNat a % Fn.modulus) % Fn.modulus = 1
        rw [rawToNat_eq, Nat.mul_mod_mod]
        exact hproduct
      have hcheck : b.val < Fn.modulus ∧ b.val * (toFin a).val % Fn.modulus = 1 :=
        ⟨hless, hmod⟩
      have hc : check (some b.val) (toFin a) = toFin b := by
        rw [check, dite_eq_left hcheck]
        apply Fin.ext
        exact (FnRecoveryWords.toFin_val_of_lt b hless).symm
      have hinv : check (some b.val) (toFin a) = Fin.inversePrime (toFin a) :=
        check_eq (by decide) _ _
      rw [← hinv, hc, FnRecoveryWords.fromFin_toFin_of_lt b hless]
    · rfl

/-- The checked word inverse agrees with the standard scalar inverse. -/
theorem invFnWords_eq (a : Raw) : invFnWords a = fromFin (Fn.inv (toFin a)) := by
  unfold invFnWords
  exact (checkFnWords_eq _ a).trans (congrArg fromFin (fn_inversePrime_eq (toFin a)))

end

end EthLib.Cryptography.Secp256k1.RecoveryInverse
