module

public import EthLib.Cryptography.Proofs.Kzg.Domain
public import EthLib.Cryptography.Proofs.PowMod

/-!
# Proofs: the roots and scalars of the three rounds, as naturals

The inverse transform of the setup uses `ζ = ω⁻¹`, where `ω` is the root of the blob domain.

The three rounds use the root `u = ζ^256` of order 16, the scalar `c = 4096⁻¹`, and powers of `ζ`.

The kernel checks of the rounds read these values as naturals below `r`.

Here each natural is computed by square and multiply mod `r`.

Each one is the value of its element of `Fr`, by a proof on variables.

Three constants are written out, and a computation on naturals checks each of them once.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr
open EthLib.Cryptography.PowMod (powModAux powModAux_eq)
open EthLib.Cryptography.Kzg.Constants

/-- The inverse `ζ` of the root of the blob domain. -/
def zeta : Fr := (domainRoot FIELD_ELEMENTS_PER_BLOB)⁻¹

/-- The value of `ζ`. -/
def zetaNat : Nat :=
  25829815649260311651249373569448671287036547786131478959351418120540316250978

/-- The value of `u = ζ^256`. -/
def rootNat : Nat :=
  26753076894533791554649012143113393549300550745003194222677083919072199473480

/-- The value of `4096⁻¹`. -/
def scaleNat : Nat :=
  52423073447788513186850219087163459498374710080483563692275874603576291491841

/-- The value of `u^i`, for `i < 16`. -/
def rootPowNat (i : Nat) : Nat := powModAux 4 Fr.modulus rootNat i

/-- The value of `ζ^e`, for `e < 4096`. -/
def zetaPowNat (e : Nat) : Nat := powModAux 12 Fr.modulus zetaNat e

/-- The value of `4096⁻¹ ζ^(16 j2 k1)`, the scalar of the second round. -/
def scalarB (k1 j2 : Nat) : Nat := scaleNat * zetaPowNat (16 * j2 * k1) % Fr.modulus

/-- The value of `ζ^(j3 (k1 + 16 k2))`, the scalar of the third round. -/
def scalarC (k1 k2 j3 : Nat) : Nat := zetaPowNat (j3 * (k1 + 16 * k2))

/-! ## The constants -/

private theorem natCast_mod (n : Nat) : ((n % Fr.modulus : Nat) : Fr) = n := by
  conv_rhs => rw [← Nat.mod_add_div n Fr.modulus]
  rw [Nat.cast_add, Nat.cast_mul, (Fr.natCast_eq_zero_iff Fr.modulus).mpr dvd_rfl, zero_mul,
    add_zero]

/-- The value of a square and multiply mod `r` is the power in `Fr`. -/
theorem ofNat_powModAux {fuel e : Nat} (b : Nat) (he : e < 2 ^ fuel) :
    powModAux fuel Fr.modulus b e < Fr.modulus ∧
      Fr.ofNat (powModAux fuel Fr.modulus b e) = (b : Fr) ^ e := by
  rw [powModAux_eq fuel _ b e he, Fr.ofNat_eq_natCast, natCast_mod, Nat.cast_pow]
  exact ⟨Nat.mod_lt _ Fr.modulus_pos, rfl⟩

private theorem zetaNat_eq_powModAux :
    zetaNat = powModAux 256 Fr.modulus 7 ((Fr.modulus - 1) / 4096 * 4095) := by
  decide +kernel

private theorem rootNat_eq_powModAux : rootNat = powModAux 9 Fr.modulus zetaNat 256 := by
  decide +kernel

private theorem scaleNat_mul : scaleNat * 4096 % Fr.modulus = 1 := by decide +kernel

theorem isPrimitiveRoot_zeta : IsPrimitiveRoot zeta FIELD_ELEMENTS_PER_BLOB :=
  (isPrimitiveRoot_domainRoot field_elements_per_blob_dvd_modulus_sub_one).inv

theorem zetaNat_eq : (zetaNat : Fr) = zeta := by
  have hw := isPrimitiveRoot_domainRoot field_elements_per_blob_dvd_modulus_sub_one
  have he : (Fr.modulus - 1) / 4096 * 4095 < 2 ^ 256 := by decide +kernel
  have hd : domainRoot FIELD_ELEMENTS_PER_BLOB = ((7 : Nat) : Fr) ^ ((Fr.modulus - 1) / 4096) := by
    rw [domainRoot, Fr.hpow_ofNat_eq_pow _ (by decide +kernel), Fr.ofNat_eq_natCast]
    rfl
  rw [← Fr.ofNat_eq_natCast, zetaNat_eq_powModAux, (ofNat_powModAux 7 he).2, pow_mul, ← hd, zeta,
    eq_comm]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ']
  exact hw.pow_eq_one

theorem rootNat_eq : (rootNat : Fr) = zeta ^ 256 := by
  rw [← Fr.ofNat_eq_natCast, rootNat_eq_powModAux, (ofNat_powModAux zetaNat (by decide)).2,
    zetaNat_eq]

theorem scaleNat_eq : (scaleNat : Fr) = (4096 : Fr)⁻¹ := by
  have h : ((scaleNat * 4096 % Fr.modulus : Nat) : Fr) = 1 := by rw [scaleNat_mul, Nat.cast_one]
  rw [natCast_mod, Nat.cast_mul] at h
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [mul_comm]
  exact_mod_cast h

theorem isPrimitiveRoot_root : IsPrimitiveRoot (zeta ^ 256) 16 :=
  isPrimitiveRoot_zeta.pow (by decide) (by decide)

/-! ## The values -/

theorem rootPowNat_spec {i : Nat} (hi : i < 16) :
    rootPowNat i < Fr.modulus ∧ Fr.ofNat (rootPowNat i) = (zeta ^ 256) ^ i := by
  obtain ⟨hlt, heq⟩ := ofNat_powModAux (fuel := 4) rootNat hi
  exact ⟨hlt, heq.trans (by rw [rootNat_eq])⟩

theorem zetaPowNat_spec {e : Nat} (he : e < 4096) :
    zetaPowNat e < Fr.modulus ∧ Fr.ofNat (zetaPowNat e) = zeta ^ e := by
  obtain ⟨hlt, heq⟩ := ofNat_powModAux (fuel := 12) zetaNat he
  exact ⟨hlt, heq.trans (by rw [zetaNat_eq])⟩

theorem scalarB_spec {k1 j2 : Nat} (hk1 : k1 < 16) (hj2 : j2 < 16) :
    scalarB k1 j2 < Fr.modulus ∧
      Fr.ofNat (scalarB k1 j2) = (4096 : Fr)⁻¹ * zeta ^ (16 * j2 * k1) := by
  have he : 16 * j2 * k1 < 4096 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 16 (Nat.le_of_lt_succ hj2))
      (Nat.le_of_lt_succ hk1)
    omega
  refine ⟨Nat.mod_lt _ Fr.modulus_pos, ?_⟩
  rw [scalarB, Fr.ofNat_eq_natCast, natCast_mod, Nat.cast_mul, scaleNat_eq,
    ← Fr.ofNat_eq_natCast, (zetaPowNat_spec he).2]

theorem scalarC_spec {k1 k2 j3 : Nat} (hk1 : k1 < 16) (hk2 : k2 < 16) (hj3 : j3 < 16) :
    scalarC k1 k2 j3 < Fr.modulus ∧ Fr.ofNat (scalarC k1 k2 j3) = zeta ^ (j3 * (k1 + 16 * k2)) := by
  have he : j3 * (k1 + 16 * k2) < 4096 := by
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hj3) (show k1 + 16 * k2 ≤ 255 by omega)
    omega
  exact zetaPowNat_spec he

end EthLib.Cryptography.Kzg.SetupLagrange
