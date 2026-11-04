module

public import EthLib.Cryptography.AltBn128.Curve
public import EthLib.Cryptography.Proofs.Secp256k1.Field
public import EthLib.Cryptography.Proofs.Pratt
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: the fields of alt_bn128

Both moduli are prime, by Pratt certificates that the kernel checks.

`Fp` is `Fin p`, which is `ZMod p` by definition, so a proof states its algebra over `ZMod p`.

Fermat's inverse in `Fp` is the field inverse.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

namespace Fp

-- The certificates compute powers of 256-bit numbers, deeper than the default.
set_option maxRecDepth 8000

/-- `405928799` is prime, with witness `22`. -/
private theorem prime_405928799 : Nat.Prime 405928799 :=
  Pratt.prime_of_lucas 405928799 22 256 [(2, 1), (11, 1), (3691, 1), (4999, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `11465965001` is prime, with witness `3`. -/
private theorem prime_11465965001 : Nat.Prime 11465965001 :=
  Pratt.prime_of_lucas 11465965001 3 256 [(2, 3), (5, 4), (7, 1), (327599, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1853641` is prime, with witness `17`. -/
private theorem prime_1853641 : Nat.Prime 1853641 :=
  Pratt.prime_of_lucas 1853641 17 256 [(2, 3), (3, 2), (5, 1), (19, 1), (271, 1)] (by decide) (by decide)
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

/-- `4562087` is prime, with witness `5`. -/
private theorem prime_4562087 : Nat.Prime 4562087 :=
  Pratt.prime_of_lucas 4562087 5 256 [(2, 1), (17, 1), (109, 1), (1231, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `173171039` is prime, with witness `13`. -/
private theorem prime_173171039 : Nat.Prime 173171039 :=
  Pratt.prime_of_lucas 173171039 13 256 [(2, 1), (73, 1), (89, 1), (13327, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1263766531` is prime, with witness `10`. -/
private theorem prime_1263766531 : Nat.Prime 1263766531 :=
  Pratt.prime_of_lucas 1263766531 10 256 [(2, 1), (3, 1), (5, 1), (13, 1), (911, 1), (3557, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `35385462869` is prime, with witness `2`. -/
private theorem prime_35385462869 : Nat.Prime 35385462869 :=
  Pratt.prime_of_lucas 35385462869 2 256 [(2, 2), (7, 1), (1263766531, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_1263766531)
    (by decide) (by decide)

/-- `2480874801745591` is prime, with witness `6`. -/
private theorem prime_2480874801745591 : Nat.Prime 2480874801745591 :=
  Pratt.prime_of_lucas 2480874801745591 6 256 [(2, 1), (3, 2), (5, 1), (19, 1), (41, 1), (35385462869, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_35385462869)
    (by decide) (by decide)

/-- `13427688667394608761327070753331941386769` is prime, with witness `17`. -/
private theorem prime_13427688667394608761327070753331941386769 : Nat.Prime 13427688667394608761327070753331941386769 :=
  Pratt.prime_of_lucas 13427688667394608761327070753331941386769 17 256 [(2, 4), (3, 1), (7, 1), (11, 1), (1853641, 1), (4562087, 1), (173171039, 1), (2480874801745591, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1853641
    · exact prime_4562087
    · exact prime_173171039
    · exact prime_2480874801745591)
    (by decide) (by decide)

theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 3 256 [(2, 1), (3, 2), (13, 1), (29, 1), (67, 1), (229, 1), (311, 1), (983, 1), (11003, 1), (405928799, 1), (11465965001, 1), (13427688667394608761327070753331941386769, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_405928799
    · exact prime_11465965001
    · exact prime_13427688667394608761327070753331941386769)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fp` is `ZMod p` as a ring.

The map is the identity, so it carries every operation over, and the algebra of `ZMod` applies. -/
def toZMod : Fp ≃+* ZMod modulus := RingEquiv.refl _

@[simp] theorem toZMod_zero : toZMod 0 = 0 := rfl

@[simp] theorem toZMod_one : toZMod 1 = 1 := rfl

@[simp] theorem toZMod_neg (a : Fp) : toZMod (-a) = -toZMod a := rfl

@[simp] theorem toZMod_sub (a b : Fp) : toZMod (a - b) = toZMod a - toZMod b := rfl

/-- Square and multiply computes `a^e`, for an exponent below `2^256`. -/
theorem toZMod_powBits (a : Fp) (e : Nat) (he : e < 2 ^ 256) :
    toZMod (Secp256k1.Fin.powBits 256 a e) = toZMod a ^ e :=
  Secp256k1.Fin.powBits_eq_pow 256 a e he

/-- Fermat's inverse is the field inverse, and both send `0` to `0`. -/
@[simp] theorem toZMod_inv (a : Fp) : toZMod a.inv = (toZMod a)⁻¹ := by
  rw [inv, toZMod_powBits _ _ (by decide)]
  by_cases h : toZMod a = 0
  · rw [h, zero_pow (by decide), inv_zero]
  · -- `a^(p - 2) * a = a^(p - 1) = 1`, by Fermat's little theorem.
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one h

/-- In a field, a square has at most two roots, `c` and `-c`. -/
theorem eq_or_eq_neg_of_mul_self {c d : ZMod modulus} (h : d * d = c * c) : d = c ∨ d = -c := by
  have : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end Fp

namespace Fr

set_option maxRecDepth 8000

/-- `405928799` is prime, with witness `22`. -/
private theorem prime_405928799 : Nat.Prime 405928799 :=
  Pratt.prime_of_lucas 405928799 22 256 [(2, 1), (11, 1), (3691, 1), (4999, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `12048837557` is prime, with witness `2`. -/
private theorem prime_12048837557 : Nat.Prime 12048837557 :=
  Pratt.prime_of_lucas 12048837557 2 256 [(2, 2), (7, 2), (661, 1), (93001, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `5156902474397` is prime, with witness `2`. -/
private theorem prime_5156902474397 : Nat.Prime 5156902474397 :=
  Pratt.prime_of_lucas 5156902474397 2 256 [(2, 2), (107, 1), (12048837557, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_12048837557)
    (by decide) (by decide)

/-- `1670836401704629` is prime, with witness `2`. -/
private theorem prime_1670836401704629 : Nat.Prime 1670836401704629 :=
  Pratt.prime_of_lucas 1670836401704629 2 256 [(2, 2), (3, 4), (5156902474397, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_5156902474397)
    (by decide) (by decide)

/-- `1593227` is prime, with witness `2`. -/
private theorem prime_1593227 : Nat.Prime 1593227 :=
  Pratt.prime_of_lucas 1593227 2 256 [(2, 1), (19, 1), (41927, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `639533339` is prime, with witness `2`. -/
private theorem prime_639533339 : Nat.Prime 639533339 :=
  Pratt.prime_of_lucas 639533339 2 256 [(2, 1), (229, 1), (853, 1), (1637, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `65865678001877903` is prime, with witness `5`. -/
private theorem prime_65865678001877903 : Nat.Prime 65865678001877903 :=
  Pratt.prime_of_lucas 65865678001877903 5 256 [(2, 1), (83, 1), (379, 1), (1637, 1), (639533339, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_639533339)
    (by decide) (by decide)

/-- `13818364434197438864469338081` is prime, with witness `3`. -/
private theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 :=
  Pratt.prime_of_lucas 13818364434197438864469338081 3 256 [(2, 5), (5, 1), (823, 1), (1593227, 1), (65865678001877903, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1593227
    · exact prime_65865678001877903)
    (by decide) (by decide)

theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 5 256 [(2, 28), (3, 2), (13, 1), (29, 1), (983, 1), (11003, 1), (237073, 1), (405928799, 1), (1670836401704629, 1), (13818364434197438864469338081, 1)] (by decide) (by decide)
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
    · exact prime_405928799
    · exact prime_1670836401704629
    · exact prime_13818364434197438864469338081)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

end Fr

end EthLib.Cryptography.AltBn128
