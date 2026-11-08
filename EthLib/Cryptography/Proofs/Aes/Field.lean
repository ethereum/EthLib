module

public import EthLib.Cryptography.Proofs.Aes.GaloisField
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Proofs: the ring of GCM blocks is a field

SP 800-38D §6.3 calls the ring of block residues the field of `2^128` elements.

The ring is GF(2)[u] modulo `1 + u + u^2 + u^7 + u^128`.

It is a field because this modulus is irreducible over GF(2).

## A test of irreducibility

Let `f` be monic over GF(2), of degree `2^(k+1)`.

Then `f` is irreducible when two conditions hold.

- `f` divides `u^(2^(2^(k+1))) - u`.
- `f` is coprime to `u^(2^(2^k)) - u`.

If `f` is reducible, it has an irreducible factor of degree `d` at most `2^k`.

That factor divides `u^(2^d) - u`.

The first condition makes `d` divide `2^(k+1)`, so `d` divides `2^k`.

The factor then divides `u^(2^(2^k)) - u`, against the second condition.

A degree with one prime factor, here 2, needs only these two conditions.

## The certificate

The kernel checks both conditions for the modulus with the multiplication of Algorithm 1.

The module before this one proves that this multiplication is the product of residues.

- 128 squarings take the block of `u` back to itself, so `u^(2^128) = u` in the ring.
- 64 squarings give the block of `u^(2^64)`, and a block below inverts `u^(2^64) - u`.
- So the modulus is coprime to `u^(2^64) - u`.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

open Polynomial

/-! ## A test of irreducibility -/

/-- A monic polynomial of degree `2^(k+1)` over GF(2) is irreducible under two conditions.

It divides `u^(2^(2^(k+1))) - u`, and it is coprime to `u^(2^(2^k)) - u`. -/
theorem irreducible_of_dvd_of_isCoprime {f : (ZMod 2)[X]} {k : ℕ} (hmonic : f.Monic)
    (hdeg : f.natDegree = 2 ^ (k + 1)) (hdvd : f ∣ X ^ 2 ^ 2 ^ (k + 1) - X)
    (hcop : IsCoprime f (X ^ 2 ^ 2 ^ k - X)) : Irreducible f := by
  have hcard : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rw [hmonic.irreducible_iff_natDegree']
  refine ⟨fun h1 => ?_, fun a g _ hg hag hmem => ?_⟩
  · rw [h1, natDegree_one] at hdeg
    exact absurd hdeg.symm (by positivity)
  · rw [Finset.mem_Ioc, hdeg, pow_succ, Nat.mul_div_cancel _ two_pos] at hmem
    -- A factor `g` of degree at most `2^k` has an irreducible factor `q`.
    have hg0 : g ≠ 0 := hg.ne_zero
    have hgu : ¬ IsUnit g := fun hu => by
      rw [natDegree_eq_zero_of_isUnit hu] at hmem
      omega
    obtain ⟨q, hq, hqg⟩ := WfDvdMonoid.exists_irreducible_factor hgu hg0
    have hqf : q ∣ f := hqg.trans (Dvd.intro_left a hag)
    -- The first condition makes the degree of `q` divide `2^(k+1)`.
    have hqd : q.natDegree ∣ 2 ^ (k + 1) :=
      hq.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (by rw [hcard]; exact hqf.trans hdvd)
    have hqle : q.natDegree ≤ 2 ^ k := (natDegree_le_of_dvd hqg hg0).trans hmem.2
    -- A power of two at most `2^k` divides `2^k`.
    have hqk : q.natDegree ∣ 2 ^ k := by
      obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hqd
      rw [he] at hqle ⊢
      exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hqle)
    -- So `q` divides `u^(2^(2^k)) - u` and `f`, against the second condition.
    have hqx := hq.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hqk
    rw [hcard] at hqx
    exact hq.not_isUnit (hcop.isUnit_of_dvd' hqf hqx)

/-! ## The certificate -/

/-- The block of `u`: bit `x_1` is set, so it is bit 126 of its integer. -/
def uBlock : Block := blockOfNat (2 ^ 126)

/-- The block of `1`: bit `x_0` is set, so it is bit 127 of its integer. -/
def oneBlock : Block := blockOfNat (2 ^ 127)

/-- The square of a block by Algorithm 1. -/
def square (A : Block) : Block := mul A A

/-- The block of the inverse of `u^(2^64) - u` in the ring.

An outside computation found it, and the kernel checks it below. -/
def inverseWitness : Block := blockOfNat 31972403664298480875478317702777361017

/-- 128 squarings take the block of `u` back to itself. -/
theorem square_iterate_uBlock : square^[128] uBlock = uBlock := by
  decide +kernel

/-- The witness inverts the block of `u^(2^64) - u`. -/
theorem mul_inverseWitness :
    mul (xorBlock (square^[64] uBlock) uBlock) inverseWitness = oneBlock := by
  decide +kernel

/-! ## The modulus is irreducible -/

/-- The residue of the block of `u` is the root `u`. -/
theorem residue_uBlock : residue uBlock = AdjoinRoot.root modulus := by
  have hX : polyOfNat (2 ^ 126) = X := by
    ext k
    rw [coeff_polyOfNat, coeff_X, Nat.testBit_two_pow]
    split_ifs <;> simp_all <;> omega
  rw [residue, uBlock, blockToNat_blockOfNat (by norm_num), hX, AdjoinRoot.mk_X]

/-- The residue of the block of `1` is 1. -/
theorem residue_oneBlock : residue oneBlock = 1 := by
  have h1 : polyOfNat (2 ^ 127) = 1 := by
    ext k
    rw [coeff_polyOfNat, coeff_one, Nat.testBit_two_pow]
    split_ifs <;> simp_all
    omega
  rw [residue, oneBlock, blockToNat_blockOfNat (by norm_num), h1, map_one]

/-- `n` squarings raise the residue to the power `2^n`. -/
theorem residue_square_iterate (n : ℕ) (A : Block) :
    residue (square^[n] A) = residue A ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', square, residue_mul, ih, ← sq, ← pow_mul, ← pow_succ]

/-- The modulus is monic. -/
theorem monic_modulus : modulus.Monic := by
  unfold modulus
  monicity!

/-- The modulus has degree 128. -/
theorem natDegree_modulus : modulus.natDegree = 128 :=
  natDegree_eq_of_degree_eq_some degree_modulus

/-- The modulus divides `u^(2^128) - u`. -/
theorem modulus_dvd : modulus ∣ X ^ 2 ^ 2 ^ 7 - X := by
  have h := residue_square_iterate 128 uBlock
  rw [square_iterate_uBlock, residue_uBlock, show (2 : ℕ) ^ 128 = 2 ^ 2 ^ 7 by norm_num] at h
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← h, sub_self]

/-- In the ring, the residue of the witness inverts `u^(2^64) + u`, which is `u^(2^64) - u`. -/
theorem residue_inverseWitness :
    (AdjoinRoot.root modulus ^ 2 ^ 2 ^ 6 + AdjoinRoot.root modulus) * residue inverseWitness
      = 1 := by
  have h := congrArg residue mul_inverseWitness
  rwa [residue_mul, residue_xorBlock, residue_square_iterate, residue_uBlock,
    residue_oneBlock] at h

/-- If `u^n + u` has an inverse in the ring, then the modulus is coprime to `u^n - u`.

Over GF(2), `u^n + u` is `u^n - u`.

The exponent stays a variable, so that no step expands the power `u^n`. -/
theorem isCoprime_X_pow_sub_X {n : ℕ} {r : AdjoinRoot modulus}
    (h : (AdjoinRoot.root modulus ^ n + AdjoinRoot.root modulus) * r = 1) :
    IsCoprime modulus (X ^ n - X) := by
  obtain ⟨b, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_add, ← map_mul, ← map_one (AdjoinRoot.mk modulus),
    AdjoinRoot.mk_eq_mk] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨-c, b, ?_⟩
  rw [CharTwo.sub_eq_add]
  linear_combination hc

/-- The modulus is coprime to `u^(2^64) - u`. -/
theorem isCoprime_modulus : IsCoprime modulus (X ^ 2 ^ 2 ^ 6 - X) :=
  isCoprime_X_pow_sub_X residue_inverseWitness

/-- The modulus `1 + u + u^2 + u^7 + u^128` is irreducible over GF(2). -/
theorem irreducible_modulus : Irreducible modulus :=
  -- The exponent `6 + 1` becomes `7` by a rewrite, not by unfolding the power.
  irreducible_of_dvd_of_isCoprime (k := 6) monic_modulus natDegree_modulus
    (by rw [show (6 : ℕ) + 1 = 7 from rfl]; exact modulus_dvd) isCoprime_modulus

/-- The modulus is irreducible, so the ring of residues is a field, as SP 800-38D §6.3 states. -/
instance : Fact (Irreducible modulus) := ⟨irreducible_modulus⟩

/-- The ring of residues has `2^128` elements, as SP 800-38D §6.3 states. -/
theorem card_adjoinRoot_modulus : Nat.card (AdjoinRoot modulus) = 2 ^ 128 := by
  have : Module.Finite (ZMod 2) (AdjoinRoot modulus) :=
    (AdjoinRoot.powerBasis monic_modulus.ne_zero).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    (AdjoinRoot.powerBasis monic_modulus.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_modulus]

end EthLib.Cryptography.Aes.Gcm
