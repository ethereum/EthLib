module

public import EthLib.Cryptography.Proofs.X25519.Ladder
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: X25519 key agreement

Two parties that exchange X25519 public keys derive the same secret, [RFC 7748 §6.1][rfc6].

The public key of a scalar `a` is the u-coordinate of `[a] B`, for the base point `B` with `u = 9`.

The shared secret of `a` with the public key of `b` is then the u-coordinate of `[a] [b] B`.

Scalar multiplication commutes, so both parties compute the u-coordinate of `[a b] B`.

The ladder theorem needs an input point whose u-coordinate is not `0`, for each of the two runs.

`B` has the prime order `ℓ` of [RFC 7748 §4.1][rfc4].

A clamped scalar `k` is a multiple of `8` with `2^254 ≤ k < 2^255 < 8 ℓ`, so `ℓ` does not divide it.

Since `ℓ` is odd, `ℓ` does not divide `2 k` either.

So `[b] B` is neither the point at infinity nor the point `(0, 0)` of order 2.

[rfc4]: https://www.rfc-editor.org/rfc/rfc7748#section-4.1
[rfc6]: https://www.rfc-editor.org/rfc/rfc7748#section-6.1
-/

@[expose] public section

namespace EthLib.Cryptography.X25519

open MontgomeryCurve

/-- The v-coordinate of the base point, RFC 7748 §4.1. -/
def baseV : ZMod modulus :=
  14781619447589544791020593568409986887264606134616475288964881837755586237401

/-- The coordinates of the base point satisfy the curve equation, by evaluation. -/
private theorem baseV_mul_baseV :
    baseV * baseV = (9 : ZMod modulus) * 9 * 9 + 486662 * 9 * 9 + 9 := by
  decide

/-- The discriminant of Curve25519 is not `0`, by evaluation. -/
private theorem discriminant_ne_zero : (16 : ZMod modulus) * (486662 ^ 2 - 4) ≠ 0 := by
  decide

/-- The base point lies on the curve. -/
theorem nonsingular_basePoint : curve25519.Nonsingular 9 baseV :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (by rw [discriminant_eq]; exact discriminant_ne_zero)).mp
    ((equation_iff _ _ _).mpr baseV_mul_baseV)

/-- The base point `(9, v)` of RFC 7748 §4.1. -/
def basePoint : curve25519.Point := .some 9 baseV nonsingular_basePoint

/-- The order of the base point, `2^252 + 0x14def9dea2f79cd65812631a5cf5d3ed`, RFC 7748 §4.1. -/
def order : Nat := 2 ^ 252 + 0x14def9dea2f79cd65812631a5cf5d3ed

-- The certificates compute powers mod 253-bit numbers, deeper than the default.
set_option maxRecDepth 8000

/-- `409477` is prime, with witness `2`. -/
private theorem prime_409477 : Nat.Prime 409477 :=
  Pratt.prime_of_lucas 409477 2 256 [(2, 2), (3, 1), (34123, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `14741173` is prime, with witness `2`. -/
private theorem prime_14741173 : Nat.Prime 14741173 :=
  Pratt.prime_of_lucas 14741173 2 256 [(2, 2), (3, 2), (409477, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_409477)
    (by decide) (by decide)

/-- `58964693` is prime, with witness `2`. -/
private theorem prime_58964693 : Nat.Prime 58964693 :=
  Pratt.prime_of_lucas 58964693 2 256 [(2, 2), (14741173, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · norm_num
    · exact prime_14741173)
    (by decide) (by decide)

/-- `132667` is prime, with witness `5`. -/
private theorem prime_132667 : Nat.Prime 132667 :=
  Pratt.prime_of_lucas 132667 5 256 [(2, 1), (3, 1), (22111, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `137849` is prime, with witness `3`. -/
private theorem prime_137849 : Nat.Prime 137849 :=
  Pratt.prime_of_lucas 137849 3 256 [(2, 3), (17231, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `3044861653679985063343` is prime, with witness `5`. -/
private theorem prime_3044861653679985063343 : Nat.Prime 3044861653679985063343 :=
  Pratt.prime_of_lucas 3044861653679985063343 5 256
    [(2, 1), (3, 1), (11, 1), (30703, 1), (82163, 1), (132667, 1), (137849, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_132667
    · exact prime_137849)
    (by decide) (by decide)

/-- `198211423230930754013084525763697` is prime, with witness `5`. -/
private theorem prime_198211423230930754013084525763697 :
    Nat.Prime 198211423230930754013084525763697 :=
  Pratt.prime_of_lucas 198211423230930754013084525763697 5 256
    [(2, 4), (3, 1), (23, 1), (58964693, 1), (3044861653679985063343, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_58964693
    · exact prime_3044861653679985063343)
    (by decide) (by decide)

/-- `292386187` is prime, with witness `2`. -/
private theorem prime_292386187 : Nat.Prime 292386187 :=
  Pratt.prime_of_lucas 292386187 2 256 [(2, 1), (3, 4), (307, 1), (5879, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `213441916511` is prime, with witness `13`. -/
private theorem prime_213441916511 : Nat.Prime 213441916511 :=
  Pratt.prime_of_lucas 213441916511 13 256
    [(2, 1), (5, 1), (73, 1), (292386187, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_292386187)
    (by decide) (by decide)

/-- `531581` is prime, with witness `2`. -/
private theorem prime_531581 : Nat.Prime 531581 :=
  Pratt.prime_of_lucas 531581 2 256 [(2, 2), (5, 1), (7, 1), (3797, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1224481` is prime, with witness `13`. -/
private theorem prime_1224481 : Nat.Prime 1224481 :=
  Pratt.prime_of_lucas 1224481 13 256 [(2, 5), (3, 1), (5, 1), (2551, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1257559732178653` is prime, with witness `2`. -/
private theorem prime_1257559732178653 : Nat.Prime 1257559732178653 :=
  Pratt.prime_of_lucas 1257559732178653 2 256
    [(2, 2), (3, 1), (7, 1), (23, 1), (531581, 1), (1224481, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_531581
    · exact prime_1224481)
    (by decide) (by decide)

/-- `4434155615661930479` is prime, with witness `17`. -/
private theorem prime_4434155615661930479 : Nat.Prime 4434155615661930479 :=
  Pratt.prime_of_lucas 4434155615661930479 17 256
    [(2, 1), (41, 1), (43, 1), (1257559732178653, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1257559732178653)
    (by decide) (by decide)

/-- `172054593956031949258510691` is prime, with witness `2`. -/
private theorem prime_172054593956031949258510691 : Nat.Prime 172054593956031949258510691 :=
  Pratt.prime_of_lucas 172054593956031949258510691 2 256
    [(2, 1), (5, 1), (1361, 1), (2851, 1), (4434155615661930479, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_4434155615661930479)
    (by decide) (by decide)

/-- `19757330305831588566944191468367130476339` is prime, with witness `2`. -/
private theorem prime_19757330305831588566944191468367130476339 :
    Nat.Prime 19757330305831588566944191468367130476339 :=
  Pratt.prime_of_lucas 19757330305831588566944191468367130476339 2 256
    [(2, 1), (269, 1), (213441916511, 1), (172054593956031949258510691, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_213441916511
    · exact prime_172054593956031949258510691)
    (by decide) (by decide)

/-- `276602624281642239937218680557139826668747` is prime, with witness `2`. -/
private theorem prime_276602624281642239937218680557139826668747 :
    Nat.Prime 276602624281642239937218680557139826668747 :=
  Pratt.prime_of_lucas 276602624281642239937218680557139826668747 2 256
    [(2, 1), (7, 1), (19757330305831588566944191468367130476339, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_19757330305831588566944191468367130476339)
    (by decide) (by decide)

/-- `ℓ` is prime, by Lucas' test with witness `2` on a factored `ℓ - 1`. -/
theorem order_prime : Nat.Prime order :=
  Pratt.prime_of_lucas order 2 256
    [(2, 2), (3, 1), (11, 1), (198211423230930754013084525763697, 1),
     (276602624281642239937218680557139826668747, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_198211423230930754013084525763697
    · exact prime_276602624281642239937218680557139826668747)
    (by decide) (by decide)

/-- The u-coordinate of the base point is not `0`. -/
private theorem uCoord_basePoint_ne_zero : uCoord basePoint ≠ 0 := by
  decide

/-- The base point enters the ladder as the field element `9`. -/
private theorem toZMod_symm_uCoord_basePoint : toZMod.symm (uCoord basePoint) = 9 :=
  rfl

/-- The ladder for `ℓ` on the u-coordinate `9` ends with the projective denominator `0`. -/
private theorem ladder_order_z2 :
    (conditionalSwap (ladder order 9).swap (ladder order 9)).z2 = 0 := by
  decide

/-- `[ℓ] B` is the point at infinity.

The ladder theorem reduces this to one run of the ladder, which the kernel evaluates. -/
theorem order_smul_basePoint : order • basePoint = 0 := by
  have h := (ladder_represents order (by decide) basePoint uCoord_basePoint_ne_zero).1
  rw [toZMod_symm_uCoord_basePoint, ladder_order_z2] at h
  obtain ⟨t, ht, -, hz⟩ := h
  generalize order • basePoint = Q at hz
  cases Q with
  | zero => rfl
  | some u v hv =>
    rw [WeierstrassCurve.Affine.Point.xRep_some] at hz
    simp at hz
    exact absurd hz.symm ht

/-- The base point has order `ℓ`. -/
theorem addOrderOf_basePoint : addOrderOf basePoint = order := by
  have := Fact.mk order_prime
  exact addOrderOf_eq_prime order_smul_basePoint (by rintro ⟨⟩)

/-- The public key encodes the u-coordinate of `[k] B`, for the clamped scalar `k`. -/
theorem publicKey_eq (key : Key) :
    publicKey key = encodeUCoordinate (toZMod.symm (uCoord (decodeScalar key • basePoint))) := by
  rw [← x25519_encodeUCoordinate key basePoint uCoord_basePoint_ne_zero,
    toZMod_symm_uCoord_basePoint]
  rfl

/-- `ℓ` is odd. -/
private theorem coprime_order_two : Nat.Coprime order 2 := by
  decide

/-- `ℓ` is coprime to `8`. -/
private theorem coprime_eight_order : Nat.Coprime 8 order := by
  decide

/-- For a clamped scalar `k`, the u-coordinate of `[k] B` is not `0`.

So `[k] B` is neither the point at infinity nor the point `(0, 0)`. -/
theorem uCoord_decodeScalar_smul_ne_zero (key : Key) :
    uCoord (decodeScalar key • basePoint) ≠ 0 := by
  intro h0
  have h2 : (2 * decodeScalar key) • basePoint = 0 := by
    rw [mul_smul]
    generalize decodeScalar key • basePoint = Q at h0
    cases Q with
    | zero => exact nsmul_zero 2
    | some u v hv =>
      simp only [uCoord] at h0
      subst h0
      have hv0 : v = 0 := by
        have := (equation_iff _ _ _).mp hv.1
        simpa using this
      subst hv0
      rw [two_smul]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
        (by simp [WeierstrassCurve.Affine.negY, curve])
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h2
  rw [addOrderOf_basePoint] at hdvd
  have hk : order ∣ decodeScalar key :=
    Nat.Coprime.dvd_of_dvd_mul_left coprime_order_two hdvd
  have h8 : 8 * order ∣ decodeScalar key :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd coprime_eight_order
      (Nat.dvd_of_mod_eq_zero (decodeScalar_mod_eight key)) hk
  have hlt := decodeScalar_lt key
  have hle := le_decodeScalar key
  have := Nat.le_of_dvd (by omega) h8
  have : 2 ^ 255 < 8 * order := by decide
  omega

/-- The shared secret of `a` with the public key of `b` encodes the u-coordinate of `[a b] B`.

Here `a` and `b` stand for the clamped scalars. -/
theorem x25519_publicKey (a b : Key) :
    x25519 a (publicKey b) =
      encodeUCoordinate (toZMod.symm (uCoord ((decodeScalar a * decodeScalar b) • basePoint))) := by
  rw [publicKey_eq, x25519_encodeUCoordinate a _ (uCoord_decodeScalar_smul_ne_zero b), mul_smul]

/-- X25519 key agreement: both parties derive the same shared secret, RFC 7748 §6.1. -/
theorem x25519_agree (a b : Key) : x25519 a (publicKey b) = x25519 b (publicKey a) := by
  rw [x25519_publicKey, x25519_publicKey, Nat.mul_comm]

end EthLib.Cryptography.X25519
