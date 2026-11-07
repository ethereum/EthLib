module

public import EthLib.Cryptography.Bls.Fr
public import EthLib.Cryptography.Proofs.Bls.Fr
public import EthLib.Cryptography.Proofs.PowMod
public import EthLib.Cryptography.Proofs.Montgomery
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Proofs: `Fr` as a Mathlib finite field

This file maps `Fr` to Mathlib's `ZMod r`.

An element of `Fr` holds its Montgomery form, and the map sends it to the integer it stands for.

The map is a ring isomorphism, so `Fr` is a field as `ZMod r` is.

## Primality of the modulus

The prime `r` has a Lucas certificate: `7` has order `r - 1` in the units of `ZMod r`.

The certificate uses the full factorization of `r - 1`, which is the product of:

- `2^32 * 3 * 11 * 19 * 10177 * 125527 * 859267`.
- `906349^2 * 2508409 * 2529403 * 52437899 * 254760293^2`.

It checks `7^(r - 1) = 1`, and `7^((r - 1) / q) ≠ 1` for each prime factor `q`.

The kernel computes those powers by square and multiply on natural numbers, in seconds.

The same two facts give the order of `7` exactly.

So `7` is a primitive `(r - 1)`-th root of unity.

And `7^((r - 1) / n)` is a primitive `n`-th root of unity for every `n` that divides `r - 1`.

Those roots are the domains of the FFT and of barycentric evaluation.

## The bridge to Mathlib

The last section carries the field structure of `ZMod r` to `Fr` through the isomorphism.

Its operations are those of `Fr`: the sum, the product, the power, the inverse and the division.

So each operation of the specification is the operation of the field, by definition.

The inverse is `a ^ (r - 2)`, which equals the field inverse because `r` is prime.

Later proofs open the field structure with `open scoped EthLib.Cryptography.Bls.Fr`.

It is scoped, as Mathlib scopes the ring instance of `Fin`, to avoid coercion loops.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Fr

-- Kernel evaluation of `powModAux` (256 recursion steps) exceeds the default `maxRecDepth`.
--
-- The `decide` calls below need the higher depth.
set_option maxRecDepth 4000

private theorem seven_pow_div_ne_one (q : Nat)
    (hne : PowMod.powModAux 256 modulus 7 ((modulus - 1) / q) ≠ 1 % modulus) :
    ((7 : ℕ) : ZMod modulus) ^ ((modulus - 1) / q) ≠ 1 :=
  PowMod.natCast_pow_div_ne_one modulus 256 7 q (by decide) hne

/-- First half of the Lucas certificate: `7 ^ (r - 1) = 1` in `ZMod r`. -/
theorem seven_pow_card_sub_one : ((7 : ℕ) : ZMod modulus) ^ (modulus - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff modulus 256 7 (modulus - 1) (by decide)]
  decide

/-- Second half of the Lucas certificate.

For every prime factor `q` of `r - 1`, `7 ^ ((r - 1) / q) ≠ 1` in `ZMod r`.

Together with `seven_pow_card_sub_one` this pins the order of `7` to exactly `r - 1`. -/
theorem seven_pow_div_prime_ne_one : ∀ q : Nat, q.Prime → q ∣ modulus - 1 →
    ((7 : ℕ) : ZMod modulus) ^ ((modulus - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p : Nat, p.Prime → q ∣ p → q = p := fun p hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : modulus - 1 =
      2 ^ 32 * (3 * (11 * (19 * (10177 * (125527 * (859267 * (906349 ^ 2 *
        (2508409 * (2529403 * (52437899 * 254760293 ^ 2)))))))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact seven_pow_div_ne_one 2 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact seven_pow_div_ne_one 3 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact seven_pow_div_ne_one 11 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 19 (by norm_num) h
    exact seven_pow_div_ne_one 19 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 10177 (by norm_num) h
    exact seven_pow_div_ne_one 10177 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 125527 (by norm_num) h
    exact seven_pow_div_ne_one 125527 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 859267 (by norm_num) h
    exact seven_pow_div_ne_one 859267 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 906349 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact seven_pow_div_ne_one 906349 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2508409 (by norm_num) h
    exact seven_pow_div_ne_one 2508409 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2529403 (by norm_num) h
    exact seven_pow_div_ne_one 2529403 (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 52437899 (by norm_num) h
    exact seven_pow_div_ne_one 52437899 (by decide)
  · obtain rfl := heq 254760293 (by norm_num) (hq.dvd_of_dvd_pow hdvd)
    exact seven_pow_div_ne_one 254760293 (by decide)

/-- The scalar field modulus `r` is prime, by a Lucas certificate with witness `7`.

`7` is a primitive root mod `r`, and KZG derives its roots of unity from it. -/
theorem modulus_prime : Nat.Prime modulus :=
  lucas_primality modulus ((7 : ℕ) : ZMod modulus)
    seven_pow_card_sub_one seven_pow_div_prime_ne_one

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

instance : Fact (Nat.Prime params.p) := ⟨modulus_prime⟩

/-- The element of `Fr` that an element of `ZMod r` stands for. -/
def ofZMod (z : ZMod modulus) : Fr := Fr.ofNat z.val

/-- An element of `ZMod r` maps back to itself. -/
theorem toZMod_ofZMod (z : ZMod modulus) : Montgomery.toZMod (ofZMod z) = z :=
  (Montgomery.toZMod_ofNat z.val).trans (ZMod.natCast_zmod_val z)

/-- An element of `Fr` maps back to itself. -/
theorem ofZMod_toZMod (a : Fr) : ofZMod (Montgomery.toZMod a) = a :=
  Montgomery.toZMod_injective (toZMod_ofZMod _)

/-- `Fr` and Mathlib's `ZMod r` are isomorphic rings.

The map sends an element to the integer mod `r` that it stands for. -/
def toZMod : Fr ≃+* ZMod modulus where
  toFun := Montgomery.toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod
  map_mul' := Montgomery.toZMod_mul
  map_add' := Montgomery.toZMod_add

/-- `Fr` is finite, through the isomorphism. -/
instance : Fintype Fr := Fintype.ofEquiv _ toZMod.symm.toEquiv

/-- `Fr` has `r` elements. -/
theorem card_eq : Fintype.card Fr = modulus :=
  (Fintype.card_congr toZMod.toEquiv).trans (ZMod.card modulus)

/-- With primality, `ZMod r` is a finite field, and `Fr` is one through the isomorphism. -/
example : Field (ZMod modulus) := inferInstance

/-! ## Roots of unity -/

/-- `7` has multiplicative order exactly `r - 1` in `ZMod r`.

So it is a generator of the multiplicative group.

Reuses the two halves of the Lucas certificate. -/
theorem orderOf_seven : orderOf ((7 : ℕ) : ZMod modulus) = modulus - 1 :=
  orderOf_eq_of_pow_and_pow_div_prime (by decide)
    seven_pow_card_sub_one seven_pow_div_prime_ne_one

/-- `7` is a primitive `(r-1)`-th root of unity in `ZMod r`. -/
theorem isPrimitiveRoot_seven :
    IsPrimitiveRoot ((7 : ℕ) : ZMod modulus) (modulus - 1) :=
  orderOf_seven ▸ IsPrimitiveRoot.orderOf _

/-- `7 ^ ((r-1)/n)` is a primitive `n`-th root of unity for every `n ∣ r - 1`.

This is the root the KZG spec's `computeRootsOfUnity` builds its evaluation domains from. -/
theorem isPrimitiveRoot_seven_pow {n : Nat} (hn : n ∣ modulus - 1) :
    IsPrimitiveRoot (((7 : ℕ) : ZMod modulus) ^ ((modulus - 1) / n)) n :=
  isPrimitiveRoot_seven.pow (by decide) (Nat.div_mul_cancel hn).symm

/-! ## Bridge: spec operations = Mathlib operations -/

/-- The field structure of `ZMod r`, carried to `Fr` by the isomorphism.

The operations are those of the specification: the sum, the product, the power and the inverse.

So `a / b` in the specification is the division of the field, by definition.

The scalar actions and the casts from the integers and the rationals go through `ZMod r`.

Proofs alone use them.

It is scoped, as Mathlib scopes the ring instance of `Fin`, to avoid coercion loops.

Activate with `open scoped EthLib.Cryptography.Bls.Fr`. -/
scoped instance instField : Field Fr :=
  letI : SMul ℕ Fr := ⟨fun n a => ofZMod (n • Montgomery.toZMod a)⟩
  letI : SMul ℤ Fr := ⟨fun n a => ofZMod (n • Montgomery.toZMod a)⟩
  letI : SMul ℚ≥0 Fr := ⟨fun q a => ofZMod (q • Montgomery.toZMod a)⟩
  letI : SMul ℚ Fr := ⟨fun q a => ofZMod (q • Montgomery.toZMod a)⟩
  letI : Pow Fr ℤ := ⟨fun a n => ofZMod (Montgomery.toZMod a ^ n)⟩
  letI : IntCast Fr := ⟨fun n => ofZMod n⟩
  letI : NNRatCast Fr := ⟨fun q => ofZMod q⟩
  letI : RatCast Fr := ⟨fun q => ofZMod q⟩
  Function.Injective.field (Montgomery.toZMod : Fr → ZMod modulus) Montgomery.toZMod_injective
    Montgomery.toZMod_zero Montgomery.toZMod_one Montgomery.toZMod_add Montgomery.toZMod_mul
    Montgomery.toZMod_neg Montgomery.toZMod_sub Montgomery.toZMod_inv
    (fun a b => by
      change Montgomery.toZMod (a * b⁻¹) = _
      rw [Montgomery.toZMod_mul, Montgomery.toZMod_inv, div_eq_mul_inv])
    (fun _ _ => toZMod_ofZMod _) (fun _ _ => toZMod_ofZMod _) (fun _ _ => toZMod_ofZMod _)
    (fun _ _ => toZMod_ofZMod _) Montgomery.toZMod_pow (fun _ _ => toZMod_ofZMod _)
    Montgomery.toZMod_natCast (fun _ => toZMod_ofZMod _) (fun _ => toZMod_ofZMod _)
    (fun _ => toZMod_ofZMod _)

@[simp] theorem zero_def : Fr.zero = (0 : Fr) := rfl

@[simp] theorem one_def : Fr.one = (1 : Fr) := rfl

/-- The spec's `Fr.ofNat` is Mathlib's `Nat.cast`. -/
theorem ofNat_eq_natCast (n : Nat) : Fr.ofNat n = (n : Fr) := rfl

/-- The spec's `Fr.powNat` is Mathlib's monoid power. -/
theorem powNat_eq_pow (a : Fr) (n : Nat) : a.powNat n = a ^ n := rfl

/-- The spec's `HPow Fr Fr Fr` (used as `a ^ b`) is Mathlib's monoid power at the exponent's value.
-/
theorem hpow_eq_pow (a b : Fr) : a ^ b = a ^ b.val :=
  powNat_eq_pow a b.val

/-- Specialization of `hpow_eq_pow` to an `ofNat`-embedded exponent:
when `w` is canonical the round-trip through `Fr` is invisible. -/
theorem hpow_ofNat_eq_pow (a : Fr) {w : Nat} (hw : w < modulus) :
    a ^ Fr.ofNat w = a ^ w := by
  rw [hpow_eq_pow, val_ofNat_of_lt hw]

/-- The inverse of the specification is the field inverse, and both send `0` to `0`. -/
theorem inverse_eq_inv (a : Fr) : a.inverse = a⁻¹ := rfl

/-- The spec's division, a product by the inverse, is field division. -/
theorem div_eq_mul_inv' (a b : Fr) : a / b = a * b⁻¹ := rfl

/-- The cast of the integer of an element is the element. -/
theorem natCast_val (x : Fr) : ((x.val : Nat) : Fr) = x := by
  apply Montgomery.toZMod_injective
  rw [Montgomery.toZMod_natCast, val_eq, ZMod.natCast_zmod_val]

/-- The cast of a natural number is zero exactly when `r` divides it. -/
theorem natCast_eq_zero_iff (n : Nat) : (n : Fr) = 0 ↔ modulus ∣ n := by
  have h := ZMod.natCast_eq_zero_iff n modulus
  constructor
  · intro hn
    have hz := congrArg Montgomery.toZMod hn
    rw [Montgomery.toZMod_natCast, Montgomery.toZMod_zero] at hz
    exact h.mp hz
  · intro hn
    apply Montgomery.toZMod_injective
    rw [Montgomery.toZMod_natCast, Montgomery.toZMod_zero]
    exact h.mpr hn

/-- The cast of a natural number strictly between `0` and `r` is not zero. -/
theorem natCast_ne_zero {n : Nat} (h0 : 0 < n) (hn : n < modulus) : (n : Fr) ≠ 0 := by
  intro h
  have hv := congrArg Fr.val h
  rw [← ofNat_eq_natCast, val_ofNat_of_lt hn, val_zero] at hv
  omega

/-- `Fr`-facing form of `isPrimitiveRoot_seven_pow`.

It is phrased with the spec's own operations: `Fr.ofNat` and the `Fr`-exponent power.

The root `computeRootsOfUnity n` starts from is a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_ofNat_seven_pow {n : Nat} (hn : n ∣ modulus - 1) :
    IsPrimitiveRoot (Fr.ofNat 7 ^ Fr.ofNat ((modulus - 1) / n)) n := by
  have hlt : (modulus - 1) / n < modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt Fr.modulus_pos Nat.one_pos)
  rw [hpow_eq_pow, val_ofNat_of_lt hlt, ofNat_eq_natCast]
  have h := (isPrimitiveRoot_seven_pow hn).map_of_injective (f := toZMod.symm) toZMod.symm.injective
  rwa [map_pow, map_natCast] at h

-- Smoke tests: the scoped field structure uses the operations of the executable spec.
example (a b : Fr) : a * b = b * a := mul_comm a b
example (a b : Fr) : a - b = a + -b := sub_eq_add_neg a b
example (a : Fr) (h : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ h

end EthLib.Cryptography.Bls.Fr
