module

public import EthLib.Cryptography.Montgomery.Fin
-- The conversion laws read the bodies of the two conversions.
import all EthLib.Cryptography.Montgomery.Fin
public import EthLib.Cryptography.Proofs.Montgomery
public import EthLib.Cryptography.Proofs.Inverse

/-!
# Proofs: Montgomery forms of `Fin p`

Leaving Montgomery form undoes entering it.

Leaving it maps each operation of the forms to the same operation of `Fin p`.

So a chain of products on forms gives the chain of products on `Fin p`.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

variable {n : Nat} [Words n] [Limbs n] {M : Modulus n}

/-- An element of `Fin p` read in `ZMod p`. -/
private abbrev cast (a : Fin M.p) : ZMod M.p := (a.val : ZMod M.p)

private theorem cast_injective : Function.Injective (cast (M := M)) := by
  intro a b h
  apply Fin.ext
  have h := congrArg ZMod.val h
  simpa only [cast, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h

private theorem cast_toFin (a : Montgomery M) : cast (toFin a) = toZMod a := by
  change (a.toNat : ZMod M.p) = _
  rw [toNat_eq, ZMod.natCast_zmod_val]

/-- Entering Montgomery form keeps the value. -/
theorem toZMod_ofFin (a : Fin M.p) : toZMod (ofFin a) = (a.val : ZMod M.p) :=
  toZMod_ofNat a.val

/-- Leaving Montgomery form undoes entering it. -/
@[simp] theorem toFin_ofFin (a : Fin M.p) : toFin (ofFin a) = a := by
  apply cast_injective
  rw [cast_toFin, toZMod_ofFin]

/-- Distinct forms stand for distinct elements of `Fin p`. -/
theorem toFin_injective : Function.Injective (toFin (M := M)) := by
  intro a b h
  apply toZMod_injective
  rw [← cast_toFin, ← cast_toFin, h]

/-- Two forms are equal exactly when their elements are. -/
@[simp] theorem toFin_eq_iff (a b : Montgomery M) : toFin a = toFin b ↔ a = b :=
  toFin_injective.eq_iff

private theorem cast_add (x y : Fin M.p) : cast (x + y) = cast x + cast y := by
  simp only [cast, Fin.val_add, ZMod.natCast_mod, Nat.cast_add]

private theorem cast_mul (x y : Fin M.p) : cast (x * y) = cast x * cast y := by
  simp only [cast, Fin.val_mul, ZMod.natCast_mod, Nat.cast_mul]

private theorem cast_sub (x y : Fin M.p) : cast (x - y) = cast x - cast y := by
  simp only [cast, Fin.val_sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub y.isLt.le,
    ZMod.natCast_self]
  ring

/-- Leaving Montgomery form keeps sums. -/
@[simp] theorem toFin_add (a b : Montgomery M) : toFin (a + b) = toFin a + toFin b := by
  apply cast_injective
  rw [cast_add, cast_toFin, cast_toFin, cast_toFin, toZMod_add]

/-- Leaving Montgomery form keeps products. -/
@[simp] theorem toFin_mul (a b : Montgomery M) : toFin (a * b) = toFin a * toFin b := by
  apply cast_injective
  rw [cast_mul, cast_toFin, cast_toFin, cast_toFin, toZMod_mul]

/-- Leaving Montgomery form keeps differences. -/
@[simp] theorem toFin_sub (a b : Montgomery M) : toFin (a - b) = toFin a - toFin b := by
  apply cast_injective
  rw [cast_sub, cast_toFin, cast_toFin, cast_toFin, toZMod_sub]

/-- The form of `k` stands for `k mod p`. -/
@[simp] theorem toFin_ofNat (k : Nat) : toFin (ofNat k : Montgomery M) = Fin.ofNat M.p k := by
  apply cast_injective
  rw [cast_toFin, toZMod_ofNat]
  change (k : ZMod M.p) = ((k % M.p : Nat) : ZMod M.p)
  rw [ZMod.natCast_mod]

/-- The form of `0` stands for `0`. -/
@[simp] theorem toFin_zero : toFin (0 : Montgomery M) = 0 := by
  apply cast_injective
  rw [cast_toFin, toZMod_zero]
  simp [cast]

/-- The form of `1` stands for `1`. -/
@[simp] theorem toFin_one : toFin (1 : Montgomery M) = 1 := by
  apply cast_injective
  rw [cast_toFin, toZMod_one]
  change (1 : ZMod M.p) = ((1 % M.p : Nat) : ZMod M.p)
  rw [ZMod.natCast_mod, Nat.cast_one]

/-- For a prime modulus, the Fermat inverse of a form is the Euclidean inverse, also at `0`. -/
theorem toFin_inv [Fact M.p.Prime] (a : Montgomery M) :
    toFin a⁻¹ = Fin.inverse (toFin a) := by
  apply cast_injective
  show _ = ((Fin.inverse (toFin a)).val : ZMod M.p)
  rw [cast_toFin, toZMod_inv, Fin.inverse_val]
  exact congrArg _ (cast_toFin a).symm

end EthLib.Cryptography.Montgomery
