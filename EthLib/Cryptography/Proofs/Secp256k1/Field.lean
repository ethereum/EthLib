import EthLib.Cryptography.Secp256k1.Field
import EthLib.Cryptography.Proofs.Pratt
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: the fields of secp256k1

Both moduli are prime, so `ZMod p` and `ZMod n` are fields.

`Fp` is `Fin p`, which is `ZMod p` by definition, with the same ring operations.

So a proof states its algebra over `ZMod p`, where `ring` and `field_simp` work, and an `Fp` crosses over unchanged.

- `Fp.modulus_prime` and `Fn.modulus_prime`: Pratt certificates, which the kernel checks.
- `Fin.powBits_eq_pow`: square and multiply computes the power.
- `Fp.inv_eq_inv` and `Fn.inv_eq_inv`: Fermat's inverse is the field inverse.
- `Fp.sqrt_mul_self` and `Fp.sqrt_isSome`: `sqrt` returns a square root exactly when one exists.
-/

namespace EthLib.Cryptography.Secp256k1

open Fin.CommRing in
/-- Square and multiply computes `a^e`, when `e < 2^fuel`. -/
theorem Fin.powBits_eq_pow {m : Nat} [NeZero m] (fuel : Nat) (a : Fin m) (e : Nat) (he : e < 2 ^ fuel) :
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

namespace Fp

-- The certificates evaluate `powModAux` on 256-bit numbers, deeper than the default.
set_option maxRecDepth 8000

/-- `13331831` is prime, with witness `13`. -/
private theorem prime_13331831 : Nat.Prime 13331831 :=
  Pratt.prime_of_lucas 13331831 13 256 [(2, 1), (5, 1), (971, 1), (1373, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `173378833005251801` is prime, with witness `6`. -/
private theorem prime_173378833005251801 : Nat.Prime 173378833005251801 :=
  Pratt.prime_of_lucas 173378833005251801 6 256 [(2, 3), (5, 2), (2621, 1), (24809, 1), (13331831, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_13331831)
    (by decide) (by decide)

/-- `22149492674086928081353` is prime, with witness `5`. -/
private theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 :=
  Pratt.prime_of_lucas 22149492674086928081353 5 256 [(2, 3), (3, 1), (5323, 1), (173378833005251801, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_173378833005251801)
    (by decide) (by decide)

/-- `132896956044521568488119` is prime, with witness `6`. -/
private theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 :=
  Pratt.prime_of_lucas 132896956044521568488119 6 256 [(2, 1), (3, 1), (22149492674086928081353, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_22149492674086928081353)
    (by decide) (by decide)

/-- `1206781` is prime, with witness `10`. -/
private theorem prime_1206781 : Nat.Prime 1206781 :=
  Pratt.prime_of_lucas 1206781 10 256 [(2, 2), (3, 1), (5, 1), (20113, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `7240687` is prime, with witness `3`. -/
private theorem prime_7240687 : Nat.Prime 7240687 :=
  Pratt.prime_of_lucas 7240687 3 256 [(2, 1), (3, 1), (1206781, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_1206781)
    (by decide) (by decide)

/-- `107590001` is prime, with witness `3`. -/
private theorem prime_107590001 : Nat.Prime 107590001 :=
  Pratt.prime_of_lucas 107590001 3 256 [(2, 4), (5, 4), (7, 1), (29, 1), (53, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `255515944373312847190720520512484175977` is prime, with witness `3`. -/
private theorem prime_255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 :=
  Pratt.prime_of_lucas 255515944373312847190720520512484175977 3 256 [(2, 3), (7, 2), (11, 1), (1627, 1), (2657, 1), (4423, 1), (41201, 1), (96557, 1), (7240687, 1), (107590001, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_7240687
    · exact prime_107590001)
    (by decide) (by decide)

/-- `205115282021455665897114700593932402728804164701536103180137503955397371` is prime, with witness `10`. -/
private theorem prime_205115282021455665897114700593932402728804164701536103180137503955397371 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 :=
  Pratt.prime_of_lucas 205115282021455665897114700593932402728804164701536103180137503955397371 10 256 [(2, 1), (3, 1), (5, 1), (29, 2), (31, 1), (7723, 1), (132896956044521568488119, 1), (255515944373312847190720520512484175977, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_132896956044521568488119
    · exact prime_255515944373312847190720520512484175977)
    (by decide) (by decide)

theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 3 256 [(2, 1), (3, 1), (7, 1), (13441, 1), (205115282021455665897114700593932402728804164701536103180137503955397371, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_205115282021455665897114700593932402728804164701536103180137503955397371)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fp` is `ZMod modulus` as a ring.

The map is the identity, so it carries every operation over, and the algebra of `ZMod` applies. -/
def toZMod : Fp ≃+* ZMod modulus := RingEquiv.refl _

@[simp] theorem toZMod_zero : toZMod 0 = 0 := rfl

@[simp] theorem toZMod_one : toZMod 1 = 1 := rfl

@[simp] theorem toZMod_neg (a : Fp) : toZMod (-a) = -toZMod a := rfl

@[simp] theorem toZMod_sub (a b : Fp) : toZMod (a - b) = toZMod a - toZMod b := rfl

/-- `pow` computes `a^e`, for an exponent below `2^256`. -/
theorem toZMod_pow (a : Fp) (e : Nat) (he : e < 2 ^ 256) : toZMod (a.pow e) = toZMod a ^ e :=
  Fin.powBits_eq_pow 256 a e he

/-- Fermat's inverse is the field inverse, and both send `0` to `0`. -/
@[simp] theorem toZMod_inv (a : Fp) : toZMod a.inv = (toZMod a)⁻¹ := by
  rw [inv, toZMod_pow _ _ (by decide)]
  by_cases h : toZMod a = 0
  · rw [h, zero_pow (by decide), inv_zero]
  · -- `a^(m - 2) * a = a^(m - 1) = 1`, by Fermat's little theorem.
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one h

/-- `p = 3 mod 4`, which gives the square root its closed form. -/
theorem modulus_mod_four : modulus % 4 = 3 := by decide

/-- A root that `sqrt` returns squares to its input. -/
theorem sqrt_mul_self {a c : Fp} (h : a.sqrt = some c) : toZMod c * toZMod c = toZMod a := by
  simp only [sqrt] at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  rw [← map_mul, hc]

/-- `sqrt` returns a root of every square. -/
theorem sqrt_isSome {a : Fp} {b : ZMod modulus} (h : b * b = toZMod a) : ∃ c, a.sqrt = some c := by
  refine ⟨_, ite_eq_left (toZMod.injective ?_)⟩
  -- With `a = b^2`, the candidate `a^((p + 1) / 4)` squares to `b^(p + 1)`, which is `b^2`.
  have h4 := modulus_mod_four
  rw [map_mul, toZMod_pow _ _ (by decide), ← h, ← pow_two, ← pow_mul, ← pow_two, ← pow_mul]
  by_cases hb : b = 0
  · subst hb
    rw [zero_pow (by omega), zero_pow (by omega)]
  · rw [show 2 * ((modulus + 1) / 4 * 2) = (modulus - 1) + 2 by omega, pow_add, ZMod.pow_card_sub_one_eq_one hb,
      one_mul]

/-- `sqrt` fails exactly on the non-squares. -/
theorem sqrt_eq_none_iff {a : Fp} : a.sqrt = none ↔ ∀ b : ZMod modulus, b * b ≠ toZMod a := by
  constructor
  · intro h b hb
    obtain ⟨c, hc⟩ := sqrt_isSome hb
    rw [h] at hc
    cases hc
  · intro h
    cases hs : a.sqrt with
    | none => rfl
    | some c => exact absurd (sqrt_mul_self hs) (h (toZMod c))

/-- In a field, a square has at most two roots, `c` and `-c`. -/
theorem eq_or_eq_neg_of_mul_self {c d : ZMod modulus} (h : d * d = c * c) : d = c ∨ d = -c := by
  have : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end Fp

namespace Fn

set_option maxRecDepth 8000

/-- `4681609` is prime, with witness `23`. -/
private theorem prime_4681609 : Nat.Prime 4681609 :=
  Pratt.prime_of_lucas 4681609 23 256 [(2, 3), (3, 1), (97, 1), (2011, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `107361793816595537` is prime, with witness `3`. -/
private theorem prime_107361793816595537 : Nat.Prime 107361793816595537 :=
  Pratt.prime_of_lucas 107361793816595537 3 256 [(2, 4), (16699, 1), (85831, 1), (4681609, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_4681609)
    (by decide) (by decide)

/-- `44706919` is prime, with witness `6`. -/
private theorem prime_44706919 : Nat.Prime 44706919 :=
  Pratt.prime_of_lucas 44706919 6 256 [(2, 1), (3, 1), (797, 1), (9349, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `174723607534414371449` is prime, with witness `3`. -/
private theorem prime_174723607534414371449 : Nat.Prime 174723607534414371449 :=
  Pratt.prime_of_lucas 174723607534414371449 3 256 [(2, 3), (17, 1), (59, 1), (4051, 1), (120233, 1), (44706919, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_44706919)
    (by decide) (by decide)

/-- `545358713` is prime, with witness `5`. -/
private theorem prime_545358713 : Nat.Prime 545358713 :=
  Pratt.prime_of_lucas 545358713 5 256 [(2, 3), (41, 1), (59, 1), (28181, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1627771` is prime, with witness `3`. -/
private theorem prime_1627771 : Nat.Prime 1627771 :=
  Pratt.prime_of_lucas 1627771 3 256 [(2, 1), (3, 1), (5, 1), (29, 1), (1871, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `297159362677` is prime, with witness `2`. -/
private theorem prime_297159362677 : Nat.Prime 297159362677 :=
  Pratt.prime_of_lucas 297159362677 2 256 [(2, 2), (3, 2), (11, 1), (461, 1), (1627771, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1627771)
    (by decide) (by decide)

/-- `29047611873442575647497758179` is prime, with witness `2`. -/
private theorem prime_29047611873442575647497758179 : Nat.Prime 29047611873442575647497758179 :=
  Pratt.prime_of_lucas 29047611873442575647497758179 2 256 [(2, 1), (293, 1), (305873, 1), (545358713, 1), (297159362677, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_545358713
    · exact prime_297159362677)
    (by decide) (by decide)

/-- `341948486974166000522343609283189` is prime, with witness `2`. -/
private theorem prime_341948486974166000522343609283189 : Nat.Prime 341948486974166000522343609283189 :=
  Pratt.prime_of_lucas 341948486974166000522343609283189 2 256 [(2, 2), (3, 3), (109, 1), (29047611873442575647497758179, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_29047611873442575647497758179)
    (by decide) (by decide)

theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 7 256 [(2, 6), (3, 1), (149, 1), (631, 1), (107361793816595537, 1), (174723607534414371449, 1), (341948486974166000522343609283189, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_107361793816595537
    · exact prime_174723607534414371449
    · exact prime_341948486974166000522343609283189)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fn` is `ZMod modulus` as a ring.

The map is the identity, so it carries every operation over, and the algebra of `ZMod` applies. -/
def toZMod : Fn ≃+* ZMod modulus := RingEquiv.refl _

@[simp] theorem toZMod_zero : toZMod 0 = 0 := rfl

@[simp] theorem toZMod_one : toZMod 1 = 1 := rfl

@[simp] theorem toZMod_neg (a : Fn) : toZMod (-a) = -toZMod a := rfl

@[simp] theorem toZMod_sub (a b : Fn) : toZMod (a - b) = toZMod a - toZMod b := rfl

/-- `pow` computes `a^e`, for an exponent below `2^256`. -/
theorem toZMod_pow (a : Fn) (e : Nat) (he : e < 2 ^ 256) : toZMod (a.pow e) = toZMod a ^ e :=
  Fin.powBits_eq_pow 256 a e he

/-- Fermat's inverse is the field inverse, and both send `0` to `0`. -/
@[simp] theorem toZMod_inv (a : Fn) : toZMod a.inv = (toZMod a)⁻¹ := by
  rw [inv, toZMod_pow _ _ (by decide)]
  by_cases h : toZMod a = 0
  · rw [h, zero_pow (by decide), inv_zero]
  · -- `a^(m - 2) * a = a^(m - 1) = 1`, by Fermat's little theorem.
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one h

end Fn

end EthLib.Cryptography.Secp256k1
