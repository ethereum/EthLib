module

public import EthLib.Cryptography.AltBn128.Pairing
public import EthLib.Cryptography.Proofs.AltBn128.Field
public import EthLib.Cryptography.Proofs.Fp2
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Proofs: `Fp2` of alt_bn128

`Fp2` is `Fp[i] / (i^2 + 1)`, and it is a field with the operations of the specification.

It has `p^2` elements.

The laws come from the generic quadratic extension.

They are read through the injective map of `Fp` into `ZMod p`.

They need `-1` not to be a square mod `p`, which holds since `p = 3 mod 4`.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

/-- `Fp` maps into `ZMod p`, injectively and respecting each field operation. -/
def Fp.embedding : FieldOps.Embedding Fp (ZMod Fp.modulus) where
  toFun := Fp.toZMod
  injective := Fp.toZMod.injective
  map_add := map_add Fp.toZMod
  map_sub := Fp.toZMod_sub
  map_mul := map_mul Fp.toZMod
  map_neg := Fp.toZMod_neg
  map_zero := Fp.toZMod_zero
  map_one := Fp.toZMod_one
  map_inverse := Fp.toZMod_inv
  beq_iff _ _ := beq_iff_eq.trans Fp.toZMod.injective.eq_iff.symm
  isZero_iff _ := beq_iff_eq.trans (map_eq_zero_iff Fp.toZMod Fp.toZMod.injective).symm

/-- The zero of the field operations is the numeral `0`. -/
@[simp] theorem Fp.fieldOps_zero : (FieldOps.zero : Fp) = 0 := rfl

/-- The one of the field operations is the numeral `1`. -/
@[simp] theorem Fp.fieldOps_one : (FieldOps.one : Fp) = 1 := rfl

end EthLib.Cryptography.AltBn128

namespace EthLib.Cryptography.AltBn128.Fp2

/-! ## Components -/

@[ext]
theorem ext {a b : Fp2} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem zero_c0 : (0 : Fp2).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2).c1 = 0 := rfl
@[simp] theorem ofFp_c0 (x : Fp) : (ofFp x).c0 = x := rfl
@[simp] theorem ofFp_c1 (x : Fp) : (ofFp x).c1 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp2) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp2) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp2) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp2) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

/-! ## The ring

The laws are those of the generic quadratic extension, at `Fp`. -/

section Ring

open scoped Fin.CommRing

/-- `n` as an element of `Fp2`: the element `n` of `Fp`. -/
instance : NatCast Fp2 := ⟨fun n => ofFp n⟩

/-- `n` as an element of `Fp2`: the element `n` of `Fp`. -/
instance : IntCast Fp2 := ⟨fun n => ofFp n⟩

@[simp] theorem natCast_c0 (n : Nat) : (n : Fp2).c0 = n := rfl
@[simp] theorem natCast_c1 (n : Nat) : (n : Fp2).c1 = 0 := rfl
@[simp] theorem intCast_c0 (n : Int) : (n : Fp2).c0 = n := rfl
@[simp] theorem intCast_c1 (n : Int) : (n : Fp2).c1 = 0 := rfl

instance : CommRing Fp2 where
  add_assoc := Cryptography.Fp2.add_assoc Fp.embedding
  zero_add := Cryptography.Fp2.zero_add Fp.embedding
  add_zero := Cryptography.Fp2.add_zero Fp.embedding
  add_comm := Cryptography.Fp2.add_comm Fp.embedding
  neg_add_cancel := Cryptography.Fp2.neg_add_cancel Fp.embedding
  sub_eq_add_neg := Cryptography.Fp2.sub_eq_add_neg Fp.embedding
  mul_assoc := Cryptography.Fp2.mul_assoc Fp.embedding
  one_mul := Cryptography.Fp2.one_mul Fp.embedding
  mul_one := Cryptography.Fp2.mul_one Fp.embedding
  zero_mul := Cryptography.Fp2.zero_mul Fp.embedding
  mul_zero := Cryptography.Fp2.mul_zero Fp.embedding
  left_distrib := Cryptography.Fp2.left_distrib Fp.embedding
  right_distrib := Cryptography.Fp2.right_distrib Fp.embedding
  mul_comm := Cryptography.Fp2.mul_comm Fp.embedding
  natCast_zero := by apply ext <;> simp
  natCast_succ _ := by apply ext <;> simp
  intCast_ofNat _ := by apply ext <;> simp
  intCast_negSucc _ := by apply ext <;> simp [Int.negSucc_eq]
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem i_mul_i : i * i = -1 := by
  apply ext <;> simp [Cryptography.Fp2.i]

/-- The constant `2` of the twist addition is the numeral of `Fp2`. -/
@[simp] theorem ofFp_two : ofFp 2 = 2 := rfl

/-- The constant `3` of the twist addition is the numeral of `Fp2`. -/
@[simp] theorem ofFp_three : ofFp 3 = 3 := rfl

end Ring

/-! ## The inverse -/

/-- `-1` is not a square in `Fp`, because `p = 3 mod 4`. -/
theorem mul_self_ne_neg_one (y : ZMod Fp.modulus) : y * y ≠ -1 :=
  Cryptography.Fp2.zmod_mul_self_ne_neg_one (by decide) y

/-- The norm `c0^2 + c1^2` is zero only at zero. -/
theorem norm_eq_zero {c0 c1 : ZMod Fp.modulus} (h : c0 * c0 + c1 * c1 = 0) : c0 = 0 ∧ c1 = 0 :=
  Cryptography.Fp2.norm_eq_zero mul_self_ne_neg_one h

theorem mul_inv_cancel' {a : Fp2} (h : a ≠ 0) : a * a.inv = 1 :=
  Cryptography.Fp2.mul_inverse_cancel Fp.embedding mul_self_ne_neg_one h

theorem inv_zero' : (0 : Fp2).inv = 0 :=
  Cryptography.Fp2.inverse_zero Fp.embedding

instance instField : Field Fp2 where
  inv := inv
  exists_pair_ne := ⟨0, 1, Cryptography.Fp2.zero_ne_one Fp.embedding⟩
  mul_inv_cancel _ h := mul_inv_cancel' h
  inv_zero := inv_zero'
  nnqsmul := _
  qsmul := _

/-- The inverse of the specification is the field inverse. -/
@[simp] theorem inv_eq_inv (a : Fp2) : a.inv = a⁻¹ := rfl

/-! ## Powers -/

/-- Square and multiply computes `a^e`. -/
theorem powNat_eq_pow (a : Fp2) (e : Nat) : Fp2.powNat a e = a ^ e :=
  Cryptography.Fp2.powNat_eq_npow _ rfl (fun _ _ => rfl) a e

end EthLib.Cryptography.AltBn128.Fp2

namespace EthLib.Cryptography.AltBn128

/-! ## Size -/

/-- An element of `Fp2` is its two coefficients. -/
def fp2Equiv : Fp2 ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Fp2` is finite. -/
noncomputable instance : Fintype Fp2 := Fintype.ofEquiv _ fp2Equiv.symm

/-- `Fp2` has `p^2` elements. -/
theorem card_fp2 : Fintype.card Fp2 = Fp.modulus ^ 2 := by
  rw [Fintype.card_eq_nat_card, Nat.card_congr fp2Equiv, Nat.card_prod, Nat.card_fin, sq]

end EthLib.Cryptography.AltBn128
