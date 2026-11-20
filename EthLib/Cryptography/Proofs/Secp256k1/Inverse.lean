module

public import EthLib.Cryptography.Secp256k1.Inverse
import all EthLib.Cryptography.Secp256k1.Inverse
public import EthLib.Cryptography.Proofs.Secp256k1.Field
public import EthLib.Cryptography.Proofs.Secp256k1.Montgomery
public import EthLib.Cryptography.Proofs.Inverse

/-!
# Proofs: the inverses of secp256k1

Each inverse is the Euclidean inverse, for every input.

The divsteps only propose a candidate.

The check accepts a candidate whose product with the input is one.

In a prime field, that candidate is the inverse.

Any other candidate gives way to the Euclidean inverse.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Inverse

/-- The checked candidate is the Euclidean inverse, whatever the candidate. -/
theorem check_eq {m : Nat} [NeZero m] [Fact m.Prime] (c : Option Nat) (a : Fin m) :
    check c a = Fin.inverse a := by
  cases c with
  | none => rfl
  | some c =>
    simp only [check]
    split
    · rename_i h
      -- `c a = 1` in the field, so `c` is the inverse of `a`.
      have hmul : (c : ZMod m) * (a.val : ZMod m) = 1 := by
        rw [← Nat.cast_mul, ← ZMod.natCast_mod (c * a.val) m, h.2, Nat.cast_one]
      have he : (c : ZMod m) = (a.val : ZMod m)⁻¹ := eq_inv_of_mul_eq_one_left hmul
      apply Fin.ext
      have hv := congrArg ZMod.val (he.trans (Fin.inverse_val a).symm)
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt h.1,
        Nat.mod_eq_of_lt (Fin.inverse a).isLt] using hv
    · rfl

open Secp256k1.Montgomery in
/-- The checked candidate in Montgomery form reads back as the Euclidean inverse. -/
theorem toFin_checkMontgomery (c : Option Montgomery) (a : Montgomery) :
    toFin (checkMontgomery c a) = Fin.inverse (toFin a) := by
  cases c with
  | none => exact toFin_ofFin _
  | some b =>
    simp only [checkMontgomery]
    split
    · rename_i h
      -- `b a = 1` in the field, so `b` reads back as the inverse of `a`.
      have hprod : toFin b * toFin a = 1 := by
        rw [← toFin_mul, h, toFin_one]
      have hz : Fp.toZMod (toFin b) * Fp.toZMod (toFin a) = 1 := by
        simpa only [map_mul, map_one] using congrArg Fp.toZMod hprod
      have : Fact (Nat.Prime Fp.modulus) := ⟨Fp.modulus_prime⟩
      apply Fp.toZMod.injective
      rw [Fin.inverse_map Fp.toZMod (fun x => (ZMod.natCast_zmod_val (Fp.toZMod x)).symm)]
      exact eq_inv_of_mul_eq_one_left hz
    · exact toFin_ofFin _

end Inverse

namespace Fn

/-- The inverse is the Euclidean inverse, for every input. -/
theorem inv_eq_inverse (a : Fn) : a.inv = Fin.inverse a := by
  have : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩
  exact Inverse.check_eq _ a

/-- The inverse is the field inverse, and it sends `0` to `0`. -/
@[simp] theorem toZMod_inv (a : Fn) : toZMod a.inv = (toZMod a)⁻¹ := by
  rw [inv_eq_inverse]
  exact Fin.inverse_map toZMod (fun x => (ZMod.natCast_zmod_val (toZMod x)).symm) a

end Fn

namespace Montgomery

/-- The inverse reads back as the Euclidean inverse, for every input. -/
theorem toFin_inv (a : Montgomery) : toFin a.inv = Fin.inverse (toFin a) :=
  Inverse.toFin_checkMontgomery _ a

end Montgomery

namespace Fp

/-- The inverse is the Euclidean inverse, for every input. -/
theorem inv_eq_inverse (a : Fp) : a.inv = Fin.inverse a := by
  rw [inv, Montgomery.toFin_inv, Montgomery.toFin_ofFin]

/-- The inverse is the field inverse, and it sends `0` to `0`. -/
@[simp] theorem toZMod_inv (a : Fp) : toZMod a.inv = (toZMod a)⁻¹ := by
  have : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩
  rw [inv_eq_inverse]
  exact Fin.inverse_map toZMod (fun x => (ZMod.natCast_zmod_val (toZMod x)).symm) a

end Fp

end EthLib.Cryptography.Secp256k1
