module

public import EthLib.Cryptography.Bls.Fp
public import EthLib.Cryptography.Proofs.Pratt
public import EthLib.Cryptography.Proofs.Inverse
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.FieldTheory.Finite.Basic
public import EthLib.Cryptography.Proofs.Montgomery
public import EthLib.Cryptography.Proofs.BaseField

/-!
# Proofs: `Fp` as a Mathlib finite field

This file maps `Fp`, held in Montgomery form, to Mathlib's `ZMod p`, as the scalar field proofs do.

The notes of the scalar field proofs on the scoped field instance apply here too.

The square root is not treated here, but with the decompression proofs that need it.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Fp

-- The `decide`-checked powers and factorization identities exceed the default depth.
set_option maxRecDepth 8000

/-! ## The Lucas certificate chain (Pratt tree) for `p` -/

-- The factors of `p - 1` reach 234 bits, beyond the range of `norm_num`.
--
-- So the primality of `p` is a chain of Lucas certificates, a Pratt tree.
--
-- The factorization is `p - 1 = 2 * 3^2 * 11 * 23 * 47 * 10177 * 859267 * 52437899 * q1 * q2`.
--
-- The two large primes are these:
-- - `q1 = 2584487767265781317813`.
-- - `q2 = 15778400344354997994418419698270088123916926905054652752758194827714659`.
--
-- Each of the two large factors carries its own certificate, with ten auxiliary primes in total.
--
-- The kernel checks every modular power, so the whole tree needs no compiled code.

/-- Pratt-tree node: `9272813673901` is prime (Lucas certificate, witness `2`). -/
private theorem prime_9272813673901 : Nat.Prime 9272813673901 :=
  Pratt.prime_of_lucas 9272813673901 2
    [(2, 2), (3, 1), (5, 2), (7, 1), (7577, 1), (582767, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `1928745244171409` is prime (Lucas certificate, witness `3`). -/
private theorem prime_1928745244171409 : Nat.Prime 1928745244171409 :=
  Pratt.prime_of_lucas 1928745244171409 3 [(2, 4), (13, 1), (9272813673901, 1)] (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_9272813673901
        | norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `7259797099061183477` is prime (Lucas certificate, witness `2`). -/
private theorem prime_7259797099061183477 : Nat.Prime 7259797099061183477 :=
  Pratt.prime_of_lucas 7259797099061183477 2 [(2, 2), (941, 1), (1928745244171409, 1)] (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_1928745244171409
        | norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `2584487767265781317813` is prime (Lucas certificate, witness `2`). -/
private theorem prime_2584487767265781317813 : Nat.Prime 2584487767265781317813 :=
  Pratt.prime_of_lucas 2584487767265781317813 2
    [(2, 2), (89, 1), (7259797099061183477, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_7259797099061183477
        | norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `64881703735777` is prime (Lucas certificate, witness `5`). -/
private theorem prime_64881703735777 : Nat.Prime 64881703735777 :=
  Pratt.prime_of_lucas 64881703735777 5 [(2, 5), (3, 7), (927093389, 1)] (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `92691255082156974996979` is prime (Lucas certificate, witness `3`). -/
private theorem prime_92691255082156974996979 : Nat.Prime 92691255082156974996979 :=
  Pratt.prime_of_lucas 92691255082156974996979 3
    [(2, 1), (3, 1), (31, 1), (467, 1), (16447, 1), (64881703735777, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_64881703735777
        | norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `43670061551` is prime (Lucas certificate, witness `7`). -/
private theorem prime_43670061551 : Nat.Prime 43670061551 :=
  Pratt.prime_of_lucas 43670061551 7 [(2, 1), (5, 2), (17, 1), (51376543, 1)] (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `13090036741` is prime (Lucas certificate, witness `10`). -/
private theorem prime_13090036741 : Nat.Prime 13090036741 :=
  Pratt.prime_of_lucas 13090036741 10
    [(2, 2), (3, 1), (5, 1), (11, 1), (47, 1), (421987, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `3819663927398918131021` is prime (Lucas certificate, witness `6`). -/
private theorem prime_3819663927398918131021 : Nat.Prime 3819663927398918131021 :=
  Pratt.prime_of_lucas 3819663927398918131021 6
    [(2, 2), (3, 2), (5, 1), (19, 1), (113, 1), (755057, 1), (13090036741, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_13090036741
        | norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `1125266252156850182658904441386709967` is prime (Lucas certificate, witness `5`). -/
private theorem prime_1125266252156850182658904441386709967 : Nat.Prime 1125266252156850182658904441386709967 :=
  Pratt.prime_of_lucas 1125266252156850182658904441386709967 5
    [(2, 1), (3373, 1), (43670061551, 1), (3819663927398918131021, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        first
        | exact prime_43670061551
        | exact prime_3819663927398918131021
        | norm_num)
    (by decide) (by decide)

/-- Pratt-tree node: `15778400344354997994418419698270088123916926905054652752758194827714659` is prime (Lucas certificate, witness `2`). -/
private theorem prime_15778400344354997994418419698270088123916926905054652752758194827714659 : Nat.Prime 15778400344354997994418419698270088123916926905054652752758194827714659 :=
  Pratt.prime_of_lucas 15778400344354997994418419698270088123916926905054652752758194827714659 2
    [(2, 1), (3, 1), (53, 1), (475709467, 1), (92691255082156974996979, 1),
     (1125266252156850182658904441386709967, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_92691255082156974996979
        | exact prime_1125266252156850182658904441386709967
        | norm_num)
    (by decide) (by decide)

/-- The BLS12-381 base field modulus is prime, by a Lucas certificate chain (Pratt tree).

Every prime factor of `p - 1` beyond `norm_num` range carries its own certificate above.

Witness: `2` is a primitive root mod `p`. -/
theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 2
    [(2, 1), (3, 2), (11, 1), (23, 1), (47, 1), (10177, 1), (859267, 1), (52437899, 1),
     (2584487767265781317813, 1),
     (15778400344354997994418419698270088123916926905054652752758194827714659, 1)]
    (by decide)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_2584487767265781317813
        | exact prime_15778400344354997994418419698270088123916926905054652752758194827714659
        | norm_num)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

open EthLib.Cryptography.Montgomery (toZMod_injective toZMod_pow toZMod_inv toZMod_natCast)

instance : Fact (Nat.Prime params.p) := ⟨modulus_prime⟩

instance : Fact (1 < params.p) := ⟨by decide⟩

/-! ## The map to `ZMod p` -/

/-- The element of `Fp` that an element of `ZMod p` stands for. -/
def ofZMod (z : ZMod modulus) : Fp := Fp.ofNat z.val

/-- An element of `ZMod p` maps back to itself. -/
theorem toZMod_ofZMod (z : ZMod modulus) : Montgomery.toZMod (ofZMod z) = z :=
  (Montgomery.toZMod_ofNat z.val).trans (ZMod.natCast_zmod_val z)

/-- An element of `Fp` maps back to itself. -/
theorem ofZMod_toZMod (a : Fp) : ofZMod (Montgomery.toZMod a) = a :=
  toZMod_injective (toZMod_ofZMod _)

/-- `Fp` and Mathlib's `ZMod p` are isomorphic rings.

The map sends an element to the integer mod `p` that it stands for. -/
def toZMod : Fp ≃+* ZMod modulus where
  toFun := Montgomery.toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod
  map_mul' := Montgomery.toZMod_mul
  map_add' := Montgomery.toZMod_add

/-- The isomorphism is the map of the Montgomery form. -/
theorem toZMod_apply (a : Fp) : toZMod a = Montgomery.toZMod a := rfl

/-- The map to `ZMod p` sends a sum to the sum. -/
@[simp] theorem toZMod_add (a b : Fp) : toZMod (a + b) = toZMod a + toZMod b :=
  Montgomery.toZMod_add a b

/-- The map to `ZMod p` sends a product to the product. -/
@[simp] theorem toZMod_mul (a b : Fp) : toZMod (a * b) = toZMod a * toZMod b :=
  Montgomery.toZMod_mul a b

/-- The map to `ZMod p` sends a difference to the difference. -/
@[simp] theorem toZMod_sub (a b : Fp) : toZMod (a - b) = toZMod a - toZMod b :=
  Montgomery.toZMod_sub a b

/-- The map to `ZMod p` sends a negation to the negation. -/
@[simp] theorem toZMod_neg (a : Fp) : toZMod (-a) = -toZMod a :=
  Montgomery.toZMod_neg a

/-- The map to `ZMod p` sends zero to zero. -/
@[simp] theorem toZMod_zero : toZMod (0 : Fp) = 0 := by
  rw [toZMod_apply, Montgomery.toZMod_zero]
  rfl

/-- The map to `ZMod p` sends one to one. -/
@[simp] theorem toZMod_one : toZMod (1 : Fp) = 1 := by
  rw [toZMod_apply, Montgomery.toZMod_one]
  rfl

/-- Two elements with the same image in `ZMod p` are equal. -/
theorem toZMod_inj {a b : Fp} : toZMod a = toZMod b ↔ a = b :=
  toZMod.injective.eq_iff

/-- The map to `ZMod p` sends the element of `n` to the cast of `n`. -/
theorem toZMod_ofNat (n : Nat) : toZMod (Fp.ofNat n) = n := by
  rw [toZMod_apply]
  exact Montgomery.toZMod_ofNat n

/-- `Fp` is finite, through the isomorphism. -/
noncomputable instance : Fintype Fp := Fintype.ofEquiv _ toZMod.symm.toEquiv

/-- `Fp` has `p` elements. -/
theorem card_eq : Fintype.card Fp = modulus :=
  (Fintype.card_congr toZMod.toEquiv).trans (ZMod.card modulus)

/-! ## The integer of an element

These lemmas give the integer of each result, so a proof does not need the representation of `Fp`.
-/

/-- The integer of an element is its value in `ZMod p`. -/
theorem val_eq (a : Fp) : a.val = (toZMod a).val := by
  unfold val
  exact Montgomery.toNat_eq a

/-- The integer of an element is below `p`. -/
theorem val_lt (a : Fp) : a.val < modulus := by
  unfold val
  exact Montgomery.toNat_lt a

/-- Two elements with the same integer are equal. -/
theorem ext {a b : Fp} (h : a.val = b.val) : a = b := by
  rw [val_eq, val_eq] at h
  exact toZMod.injective (ZMod.val_injective _ h)

/-- The element of `n` has the integer `n mod p`. -/
theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := by
  rw [val_eq, toZMod_ofNat]
  exact ZMod.val_natCast _ n

/-- The element of an integer below `p` has that integer. -/
theorem val_ofNat_of_lt {n : Nat} (h : n < modulus) : (ofNat n).val = n := by
  rw [val_ofNat, Nat.mod_eq_of_lt h]

/-- Zero has the integer `0`. -/
@[simp] theorem val_zero : (0 : Fp).val = 0 := by
  rw [val_eq, toZMod_apply, Montgomery.toZMod_zero]
  exact ZMod.val_zero

/-- One has the integer `1`. -/
@[simp] theorem val_one : (1 : Fp).val = 1 := by
  rw [val_eq, toZMod_apply, Montgomery.toZMod_one]
  exact ZMod.val_one _

/-- The integer of a sum is the sum mod `p`. -/
theorem val_add (a b : Fp) : (a + b).val = (a.val + b.val) % modulus := by
  rw [val_eq, val_eq, val_eq, map_add]
  exact ZMod.val_add _ _

/-- The integer of a product is the product mod `p`. -/
theorem val_mul (a b : Fp) : (a * b).val = a.val * b.val % modulus := by
  rw [val_eq, val_eq, val_eq, map_mul]
  exact ZMod.val_mul _ _

/-- The integer of a negation is `p` minus the integer, mod `p`. -/
theorem val_neg (a : Fp) : (-a).val = (modulus - a.val) % modulus := by
  have hneg : toZMod (-a) = -toZMod a := Montgomery.toZMod_neg a
  rw [val_eq, val_eq, hneg, ZMod.neg_val]
  split_ifs with h
  · rw [h, ZMod.val_zero, Nat.sub_zero, Nat.mod_self]
  · have h0 : (toZMod a).val ≠ 0 := fun h0 => h ((ZMod.val_eq_zero _).mp h0)
    have hlt := ZMod.val_lt (toZMod a)
    rw [Nat.mod_eq_of_lt (by omega)]

/-- The integer of a difference is `p` minus the second integer, plus the first, mod `p`. -/
theorem val_sub (a b : Fp) : (a - b).val = (modulus - b.val + a.val) % modulus := by
  have h : a - b = a + -b :=
    toZMod.injective (by rw [toZMod_sub, toZMod_add, toZMod_neg, sub_eq_add_neg])
  rw [h, val_add, val_neg, Nat.add_mod_mod, Nat.add_comm]

/-- The Boolean equality of `Fp` is equality.

Proofs use it instead of unifying with the Boolean equality, which would compute its arguments. -/
theorem beq_iff {a b : Fp} : a.beq b = true ↔ a = b := beq_iff_eq

/-- The zero test reads the integer. -/
theorem isZero_eq (a : Fp) : a.isZero = (a.val == 0) := by
  have h0 : (zero : Fp).val = 0 := val_zero
  unfold isZero
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => h ▸ h0, fun h => ext (h.trans h0.symm)⟩

/-- The zero test of `Fp` holds exactly at zero. -/
theorem isZero_iff {a : Fp} : a.isZero = true ↔ a = 0 := by
  rw [isZero_eq, beq_iff_eq]
  exact ⟨fun h => ext (h.trans val_zero.symm), fun h => h ▸ val_zero⟩

/-- Zero passes the zero test. -/
theorem zero_isZero : Fp.zero.isZero = true :=
  (isZero_eq 0).trans (by rw [val_zero]; rfl)

/-- One fails the zero test. -/
theorem one_isZero : Fp.one.isZero = false :=
  (isZero_eq 1).trans (by rw [val_one]; rfl)

/-! ## The base-field operations of `Fp` -/

/-- The extensions read the equality of `Fp` as its boolean equality. -/
@[simp] theorem baseField_beq (a b : Fp) : BaseField.beq a b = a.beq b := rfl

/-- The extensions read the zero test of `Fp` as its own. -/
@[simp] theorem baseField_isZero (a : Fp) : BaseField.isZero a = a.isZero := rfl

/-- The extensions read the inverse of `Fp` as its own. -/
@[simp] theorem baseField_inverse (a : Fp) : BaseField.inverse a = a.inverse := rfl

/-- The zero that the extensions read is the zero of `Fp`. -/
@[simp] theorem baseField_zero : (BaseField.zero : Fp) = 0 := rfl

/-- The one that the extensions read is the one of `Fp`. -/
@[simp] theorem baseField_one : (BaseField.one : Fp) = 1 := rfl

/-- The curves read the natural numbers in `Fp` through its own map. -/
@[simp] theorem baseField_ofNat (n : Nat) : (BaseField.ofNat n : Fp) = Fp.ofNat n := rfl

/-- Hash-to-curve raises `Fp` to a natural power through its own map. -/
@[simp] theorem baseField_powNat (a : Fp) (n : Nat) : BaseField.powNat a n = Fp.powNat a n := rfl

/-- The sign of an `Fp` element is the parity of its value. -/
@[simp] theorem baseField_sgn0 (a : Fp) : BaseField.sgn0 a = (a.val % 2 == 1) := rfl

/-- The square root that the extensions read from `Fp` is its own square root, as an option. -/
theorem baseField_sqrt (a : Fp) : BaseField.sqrt a = (Fp.sqrt a).toOption := rfl

/-- The candidate root that the extensions read from `Fp` is its own candidate. -/
@[simp] theorem baseField_sqrtCandidate (a : Fp) :
    BaseField.sqrtCandidate a = Fp.sqrtCandidate a := rfl

/-- The square root's power by limbs is the power by `(p + 1) / 4`. -/
theorem powLimbs_sqrtExponent (a : Fp) :
    (Montgomery.powLimbs a sqrtExponent : Fp) = powNat a ((modulus + 1) / 4) := by
  apply toZMod_injective
  rw [Montgomery.toZMod_powLimbs, val_sqrtExponent]
  exact (toZMod_pow a _).symm

/-! ## Bridge: spec operations = Mathlib operations -/

/-- The map to `ZMod p` sends a power to the power. -/
theorem toZMod_powNat (a : Fp) (n : Nat) : toZMod (a.powNat n) = toZMod a ^ n :=
  toZMod_pow a n

/-- The Euclidean inverse is the inverse of `ZMod p`, and both send `0` to `0`. -/
theorem toZMod_inverse (a : Fp) : toZMod a.inverse = (toZMod a)⁻¹ := by
  have hx : (Fin.ofNat modulus a.val).val = a.val := by
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (val_lt a)]
  have h := Fin.inverse_val (Fin.ofNat modulus a.val)
  rw [hx] at h
  rw [show toZMod a = (a.val : ZMod modulus) by rw [val_eq, ZMod.natCast_zmod_val], ← h,
    Fin.inverse, Fin.val_ofNat, ZMod.natCast_mod, hx]
  exact toZMod_ofNat _

/-- The field structure of `ZMod p`, carried to `Fp` by the isomorphism.

The operations are those of the specification: the sum, the product, the power and the division.

The inverse is the one of the Montgomery form, equal to the inverse of the specification.

It is scoped, as for the scalar field, to avoid coercion loops.

Activate it with `open scoped EthLib.Cryptography.Bls.Fp`. -/
scoped instance instField : Field Fp :=
  -- The scalar actions and the casts from the integers and the rationals go through `ZMod p`.
  --
  -- Proofs alone use them.
  letI : SMul ℕ Fp := ⟨fun n a => ofZMod (n • Montgomery.toZMod a)⟩
  letI : SMul ℤ Fp := ⟨fun n a => ofZMod (n • Montgomery.toZMod a)⟩
  letI : SMul ℚ≥0 Fp := ⟨fun q a => ofZMod (q • Montgomery.toZMod a)⟩
  letI : SMul ℚ Fp := ⟨fun q a => ofZMod (q • Montgomery.toZMod a)⟩
  letI : Pow Fp ℤ := ⟨fun a n => ofZMod (Montgomery.toZMod a ^ n)⟩
  letI : IntCast Fp := ⟨fun n => ofZMod n⟩
  letI : NNRatCast Fp := ⟨fun q => ofZMod q⟩
  letI : RatCast Fp := ⟨fun q => ofZMod q⟩
  Function.Injective.field (Montgomery.toZMod : Fp → ZMod modulus) toZMod_injective
    Montgomery.toZMod_zero Montgomery.toZMod_one Montgomery.toZMod_add Montgomery.toZMod_mul
    Montgomery.toZMod_neg Montgomery.toZMod_sub toZMod_inv
    (fun a b => by
      change Montgomery.toZMod (a * b.inverse) = _
      rw [Montgomery.toZMod_mul, ← toZMod_apply b.inverse, toZMod_inverse, div_eq_mul_inv]
      rfl)
    (fun _ _ => toZMod_ofZMod _) (fun _ _ => toZMod_ofZMod _) (fun _ _ => toZMod_ofZMod _)
    (fun _ _ => toZMod_ofZMod _) toZMod_pow (fun _ _ => toZMod_ofZMod _)
    toZMod_natCast (fun _ => toZMod_ofZMod _) (fun _ => toZMod_ofZMod _)
    (fun _ => toZMod_ofZMod _)

@[simp] theorem zero_def : Fp.zero = (0 : Fp) := rfl

@[simp] theorem one_def : Fp.one = (1 : Fp) := rfl

/-- The spec's `Fp.ofNat` is Mathlib's `Nat.cast`. -/
theorem ofNat_eq_natCast (n : Nat) : Fp.ofNat n = (n : Fp) := rfl

/-- The map to `ZMod p` sends a numeral to the same numeral. -/
@[simp] theorem toZMod_numeral (n : Nat) [n.AtLeastTwo] :
    toZMod (no_index (OfNat.ofNat n : Fp)) = OfNat.ofNat n :=
  map_ofNat toZMod n

/-- The spec's `Fp.powNat` is Mathlib's monoid power. -/
theorem powNat_eq_pow (a : Fp) (n : Nat) : a.powNat n = a ^ n := rfl

/-- The Euclidean inverse is the field inverse, and both send `0` to `0`. -/
theorem inverse_eq_inv (a : Fp) : a.inverse = a⁻¹ :=
  toZMod.injective (by rw [toZMod_inverse]; exact (toZMod_inv a).symm)

/-- The spec's division, a product by the inverse, is field division. -/
theorem div_eq_mul_inv' (a b : Fp) : a / b = a * b⁻¹ := by
  show a * b.inverse = a * b⁻¹
  rw [inverse_eq_inv]

/-- Push the map to `ZMod p` through the ring operations and the numerals.

The algebra then runs in `ZMod p`. -/
macro "push_toZMod" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Fp.toZMod_add, Fp.toZMod_mul, Fp.toZMod_sub, Fp.toZMod_neg,
    Fp.toZMod_ofNat, Fp.toZMod_one, Fp.toZMod_zero, Nat.cast_ofNat] $[$loc]?)

-- Smoke tests: the lemmas of the scoped field apply to the operations of the specification.
example (a b : Fp) : a * b = b * a := mul_comm a b
example (a b : Fp) : a - b = a + -b := sub_eq_add_neg a b
example (a : Fp) (h : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ h

/-- `Fp` maps into `ZMod p`, injectively and respecting each field operation. -/
def embedding : FieldOps.Embedding Fp (ZMod modulus) where
  toFun := toZMod
  injective := toZMod.injective
  map_add := toZMod_add
  map_sub := toZMod_sub
  map_mul := toZMod_mul
  map_neg := toZMod_neg
  map_zero := toZMod_zero
  map_one := toZMod_one
  map_inverse := toZMod_inverse
  beq_iff _ _ := beq_iff.trans toZMod_inj.symm
  isZero_iff _ := isZero_iff.trans (by rw [← toZMod_zero, toZMod_inj])

end EthLib.Cryptography.Bls.Fp
