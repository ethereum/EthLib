module

public import EthLib.Cryptography.Secp256k1.Field

-- The conversion laws need the bodies of `Fp.toMontgomery` and `Fp.ofMontgomery`.
import all EthLib.Cryptography.Secp256k1.Field
public import EthLib.Cryptography.Proofs.Montgomery
public import EthLib.Cryptography.Proofs.Inverse
public import EthLib.Cryptography.Proofs.Jacobian

/-!
# Montgomery coordinates of secp256k1

The conversion to `Fin p` preserves each field operation and every Jacobian step.

These equalities hold for all coordinates, including forms off the curve.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open Fin.CommRing in
/-- Square and multiply computes `a^e`, when `e < 2^fuel`. -/
theorem Fin.powBits_eq_pow {m : Nat} [NeZero m] (fuel : Nat) (a : Fin m) (e : Nat)
    (he : e < 2 ^ fuel) :
    Fin.powBits fuel a e = a ^ e := by
  induction fuel generalizing a e with
  | zero =>
    obtain rfl : e = 0 := by simpa using he
    simp [Fin.powBits]
  | succ fuel ih =>
    have h2 : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at he; omega
    -- `a^e = a^(e mod 2) * (a^2)^(e / 2)`.
    rw [Fin.powBits, ih _ _ h2, ← pow_two, ← pow_mul]
    split <;> [rw [← pow_succ']; skip] <;> congr 1 <;> omega

/-- Bounded square and multiply reads only the low `fuel` bits of the exponent. -/
private theorem powBits_mod {m : Nat} [NeZero m] (fuel : Nat) (a : Fin m) (e : Nat) :
    Fin.powBits fuel a (e % 2 ^ fuel) = Fin.powBits fuel a e := by
  induction fuel generalizing a e with
  | zero => rfl
  | succ fuel ih =>
    simp only [Fin.powBits, Nat.pow_succ, Nat.mod_mul_left_div_self, Nat.mod_mul_left_mod, ih]

open Fin.CommRing in
/-- Bounded square and multiply raises to the exponent of its low `fuel` bits. -/
theorem Fin.powBits_eq_pow_mod {m : Nat} [NeZero m] (fuel : Nat) (a : Fin m) (e : Nat) :
    Fin.powBits fuel a e = a ^ (e % 2 ^ fuel) :=
  (powBits_mod fuel a e).symm.trans
    (Fin.powBits_eq_pow fuel a (e % 2 ^ fuel) (Nat.mod_lt _ (Nat.two_pow_pos fuel)))

namespace Fp

private instance : NeZero params.p := ⟨by decide⟩

/-- A coordinate as an integer modulo the Montgomery modulus. -/
private def residue (a : Fp) : ZMod params.p := (a.val : ZMod params.p)

private theorem residue_injective : Function.Injective residue := by
  intro a b h
  apply Fin.ext
  have ha : a.val < params.p := a.isLt
  have hb : b.val < params.p := b.isLt
  have h := congrArg ZMod.val h
  simpa only [residue, ZMod.val_natCast, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] using h

private theorem residue_add (a b : Fp) : residue (a + b) = residue a + residue b := by
  change (((a.val + b.val) % params.p : Nat) : ZMod params.p) = _
  rw [ZMod.natCast_mod, Nat.cast_add]
  rfl

private theorem residue_mul (a b : Fp) : residue (a * b) = residue a * residue b := by
  change (((a.val * b.val) % params.p : Nat) : ZMod params.p) = _
  rw [ZMod.natCast_mod, Nat.cast_mul]
  rfl

private theorem residue_sub (a b : Fp) : residue (a - b) = residue a - residue b := by
  change ((((params.p - b.val) + a.val) % params.p : Nat) : ZMod params.p) = _
  have hb : b.val ≤ params.p := b.isLt.le
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hb, ZMod.natCast_self]
  simp only [residue]
  ring

private theorem residue_ofMontgomery (a : Montgomery) :
    residue (ofMontgomery a) = EthLib.Cryptography.Montgomery.toZMod a := by
  unfold ofMontgomery
  change (a.toNat : ZMod params.p) = _
  rw [EthLib.Cryptography.Montgomery.toNat_eq, ZMod.natCast_zmod_val]

private theorem toZMod_toMontgomery (a : Fp) :
    EthLib.Cryptography.Montgomery.toZMod (toMontgomery a) = residue a := by
  unfold toMontgomery
  exact EthLib.Cryptography.Montgomery.toZMod_ofNat a.val

@[local simp] theorem ofMontgomery_toMontgomery (a : Fp) :
    ofMontgomery (toMontgomery a) = a := by
  apply residue_injective
  rw [residue_ofMontgomery, toZMod_toMontgomery]

@[local simp] theorem ofMontgomery_add (a b : Montgomery) :
    ofMontgomery (a + b) = ofMontgomery a + ofMontgomery b := by
  apply residue_injective
  simp only [residue_ofMontgomery, residue_add,
    EthLib.Cryptography.Montgomery.toZMod_add]

@[local simp] theorem ofMontgomery_sub (a b : Montgomery) :
    ofMontgomery (a - b) = ofMontgomery a - ofMontgomery b := by
  apply residue_injective
  simp only [residue_ofMontgomery, residue_sub,
    EthLib.Cryptography.Montgomery.toZMod_sub]

@[local simp] theorem ofMontgomery_mul (a b : Montgomery) :
    ofMontgomery (a * b) = ofMontgomery a * ofMontgomery b := by
  apply residue_injective
  simp only [residue_ofMontgomery, residue_mul,
    EthLib.Cryptography.Montgomery.toZMod_mul]

@[local simp] theorem ofMontgomery_ofNat (k : Nat) :
    ofMontgomery (EthLib.Cryptography.Montgomery.ofNat k) = Fin.ofNat modulus k := by
  apply residue_injective
  rw [residue_ofMontgomery, EthLib.Cryptography.Montgomery.toZMod_ofNat]
  change (k : ZMod params.p) = ((k % params.p : Nat) : ZMod params.p)
  rw [ZMod.natCast_mod]

@[local simp] theorem ofMontgomery_zero : ofMontgomery (0 : Montgomery) = 0 :=
  ofMontgomery_ofNat 0

@[local simp] theorem ofMontgomery_one : ofMontgomery (1 : Montgomery) = 1 :=
  ofMontgomery_ofNat 1

/-- The public power is the same bounded square-and-multiply calculation on `Fin p`. -/
theorem pow_eq_powBits (a : Fp) (e : Nat) : a.pow e = Fin.powBits 256 a e := by
  apply residue_injective
  rw [pow, residue_ofMontgomery, EthLib.Cryptography.Montgomery.toZMod_powLimbs,
    EthLib.Cryptography.Montgomery.Limbs.val_ofNat, toZMod_toMontgomery,
    Fin.powBits_eq_pow_mod]
  have cast (b : Fp) : residue b = (show ZMod params.p from b) :=
    ZMod.natCast_zmod_val (show ZMod params.p from b)
  change residue a ^ (e % 2 ^ 256) = residue (a ^ (e % 2 ^ 256))
  rw [cast, cast]
  rfl

/-- For the prime base modulus, Fermat and Euclid give the same inverse, including at zero. -/
theorem inv_eq_inverse (hprime : Nat.Prime modulus) (a : Fp) : inv a = Fin.inverse a := by
  let : Fact (Nat.Prime params.p) := ⟨hprime⟩
  apply residue_injective
  change residue (ofMontgomery (EthLib.Cryptography.Montgomery.inv (toMontgomery a))) = _
  rw [residue_ofMontgomery]
  change EthLib.Cryptography.Montgomery.toZMod ((toMontgomery a)⁻¹) = _
  rw [EthLib.Cryptography.Montgomery.toZMod_inv, toZMod_toMontgomery]
  exact (Fin.inverse_val (m := params.p) a).symm

/-- Reading a Montgomery inverse gives the same base-field inverse, including at zero. -/
theorem ofMontgomery_inv (hprime : Nat.Prime modulus) (a : Montgomery) :
    ofMontgomery (EthLib.Cryptography.Montgomery.inv a) = Fin.inverse (ofMontgomery a) := by
  let : Fact (Nat.Prime params.p) := ⟨hprime⟩
  apply residue_injective
  rw [residue_ofMontgomery]
  change EthLib.Cryptography.Montgomery.toZMod (a⁻¹) = _
  rw [EthLib.Cryptography.Montgomery.toZMod_inv]
  have h := Fin.inverse_val (m := params.p) (ofMontgomery a)
  change residue (Fin.inverse (ofMontgomery a)) = (residue (ofMontgomery a))⁻¹ at h
  rw [h, residue_ofMontgomery]

/-- The representation change distinguishes all field elements. -/
theorem ofMontgomery_injective : Function.Injective ofMontgomery := by
  intro a b h
  apply EthLib.Cryptography.Montgomery.toZMod_injective
  simpa only [residue_ofMontgomery] using congrArg residue h

@[local simp] theorem ofMontgomery_eq_zero (a : Montgomery) : ofMontgomery a = 0 ↔ a = 0 := by
  have h : ofMontgomery (0 : Montgomery) = 0 := ofMontgomery_ofNat 0
  rw [← h, ofMontgomery_injective.eq_iff]

@[local simp] theorem ofMontgomery_scale (n : Nat) (a : Montgomery) :
    ofMontgomery (Jacobian.Coords.scale n a) = Jacobian.Coords.scale n (ofMontgomery a) := by
  exact Jacobian.Coords.map_scale ofMontgomery ofMontgomery_zero ofMontgomery_add n a

/-- Reading each converted coordinate leaves the form unchanged. -/
@[local simp] theorem map_ofMontgomery_toMontgomery (p : Jacobian.Coords Fp) :
    (p.map toMontgomery).map ofMontgomery = p := by
  cases p
  simp [Jacobian.Coords.map]

@[local simp] theorem map_infinity :
    (Jacobian.Coords.infinity : Jacobian.Coords Montgomery).map ofMontgomery =
      Jacobian.Coords.infinity := by
  simp [Jacobian.Coords.map, Jacobian.Coords.infinity]

/-- Both forms normalize with the same inverse and affine coordinates. -/
theorem map_toAffine (hprime : Nat.Prime modulus) (p : Jacobian.Coords Montgomery) :
    (p.toAffine EthLib.Cryptography.Montgomery.inv).map
        (fun q => (ofMontgomery q.1, ofMontgomery q.2)) =
      (p.map ofMontgomery).toAffine Fin.inverse := by
  simp only [Jacobian.Coords.toAffine, Jacobian.Coords.map, ofMontgomery_eq_zero]
  split_ifs <;> simp only [Option.map_none, Option.map_some, ofMontgomery_mul,
    ofMontgomery_inv hprime]

/-- Each multiplication and subtraction in the doubling formula commutes with conversion. -/
theorem map_double (a : Montgomery) (p : Jacobian.Coords Montgomery) :
    (Jacobian.Coords.double a p).map ofMontgomery =
      Jacobian.Coords.double (ofMontgomery a) (p.map ofMontgomery) := by
  simp only [Jacobian.Coords.double, Jacobian.Coords.map, ofMontgomery_eq_zero]
  split_ifs <;> simp

/-- Conversion preserves the exceptional cases as well as the addition formula. -/
theorem map_add (a : Montgomery) (p q : Jacobian.Coords Montgomery) :
    (Jacobian.Coords.add a p q).map ofMontgomery =
      Jacobian.Coords.add (ofMontgomery a) (p.map ofMontgomery) (q.map ofMontgomery) := by
  exact Jacobian.Coords.map_add ofMontgomery ofMontgomery_zero ofMontgomery_one
    ofMontgomery_add ofMontgomery_sub ofMontgomery_mul ofMontgomery_injective map_double a p q

/-- The same bits select the same additions in both coordinate representations. -/
theorem map_mulBits (a : Montgomery) (fuel k : Nat) (p : Jacobian.Coords Montgomery) :
    (Jacobian.Coords.mulBits a fuel k p).map ofMontgomery =
      Jacobian.Coords.mulBits (ofMontgomery a) fuel k (p.map ofMontgomery) := by
  induction fuel generalizing k p with
  | zero => exact map_infinity
  | succ fuel ih =>
    simp only [Jacobian.Coords.mulBits]
    split <;> simp only [map_add, map_double, ih]

/-- The simultaneous chain commutes with conversion for every bit sequence. -/
theorem map_mulAddAux (a : Montgomery) (p q pq : Jacobian.Coords Montgomery)
    (fuel k l : Nat) :
    (Jacobian.Coords.mulAddAux a p q pq fuel k l).map ofMontgomery =
      Jacobian.Coords.mulAddAux (ofMontgomery a) (p.map ofMontgomery) (q.map ofMontgomery)
        (pq.map ofMontgomery) fuel k l := by
  induction fuel generalizing k l with
  | zero => exact map_infinity
  | succ fuel ih =>
    simp only [Jacobian.Coords.mulAddAux]
    split_ifs <;> simp only [map_add, map_double, ih]

/-- Reading the result gives exactly the simultaneous multiplication on `Fin p`. -/
theorem map_mulAdd (a : Montgomery) (fuel k : Nat) (p : Jacobian.Coords Montgomery)
    (l : Nat) (q : Jacobian.Coords Montgomery) :
    (Jacobian.Coords.mulAdd a fuel k p l q).map ofMontgomery =
      Jacobian.Coords.mulAdd (ofMontgomery a) fuel k (p.map ofMontgomery) l
        (q.map ofMontgomery) := by
  simp only [Jacobian.Coords.mulAdd, map_mulAddAux, map_add]

end Fp

end EthLib.Cryptography.Secp256k1
