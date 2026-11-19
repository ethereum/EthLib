module

public import EthLib.Cryptography.Proofs.Aes.GaloisField
public import EthLib.Cryptography.Proofs.BinaryField.Irreducible
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Proofs: the ring of GCM blocks is a field

SP 800-38D §6.3 calls the ring of block residues the field of `2^128` elements.

The ring is GF(2)[u] modulo `1 + u + u^2 + u^7 + u^128`.

It is a field because this modulus is irreducible over GF(2).

## A test of irreducibility

The binary field proofs hold a test for a monic polynomial over GF(2) of degree `2^(k+1)`.

The modulus has degree `2^7`, so the test needs two conditions.

- The modulus divides `u^(2^128) - u`.
- The modulus is coprime to `u^(2^64) - u`.

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
  BinaryField.irreducible_of_dvd_of_isCoprime (k := 6) monic_modulus natDegree_modulus
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
