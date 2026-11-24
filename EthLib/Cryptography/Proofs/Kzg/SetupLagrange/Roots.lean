module

public import EthLib.Cryptography.Proofs.Kzg.Domain

/-!
# Proofs: the roots and scalars of the three rounds, as naturals

The inverse transform of the setup uses `ζ = ω⁻¹`, where `ω` is the root of the blob domain.

The three rounds use the root `u = ζ^256` of order 16, the scalar `c = 4096⁻¹`, and powers of `ζ`.

The kernel checks of the rounds read these values as naturals below `r`.

Here each natural is computed by square and multiply mod `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr
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

/-- The value of `u^i`; the rounds read it for `i < 16`. -/
def rootPowNat (i : Nat) : Nat := Nat.powMod rootNat i Fr.modulus

/-- The value of `ζ^e`; the rounds read it for `e < 4096`. -/
def zetaPowNat (e : Nat) : Nat := Nat.powMod zetaNat e Fr.modulus

/-- The value of `4096⁻¹ ζ^(16 j2 k1)`, the scalar of the second round. -/
def scalarB (k1 j2 : Nat) : Nat := scaleNat * zetaPowNat (16 * j2 * k1) % Fr.modulus

/-- The value of `ζ^(j3 (k1 + 16 k2))`, the scalar of the third round. -/
def scalarC (k1 k2 j3 : Nat) : Nat := zetaPowNat (j3 * (k1 + 16 * k2))

/-! ## The constants

Three constants are written out, and a computation on naturals checks each of them once.
-/

private theorem natCast_mod (n : Nat) : ((n % Fr.modulus : Nat) : Fr) = n := by
  conv_rhs => rw [← Nat.mod_add_div n Fr.modulus]
  rw [Nat.cast_add, Nat.cast_mul, (Fr.natCast_eq_zero_iff Fr.modulus).mpr dvd_rfl, zero_mul,
    add_zero]

/-- The modular power mod `r` is below `r`, and it is the power in `Fr`. -/
theorem ofNat_powMod (b e : Nat) :
    Nat.powMod b e Fr.modulus < Fr.modulus ∧
      Fr.ofNat (Nat.powMod b e Fr.modulus) = (b : Fr) ^ e := by
  rw [Nat.powMod_def, Fr.ofNat_eq_natCast, natCast_mod, Nat.cast_pow]
  exact ⟨Nat.mod_lt _ Fr.modulus_pos, rfl⟩

private theorem zetaNat_eq_powMod :
    zetaNat = Nat.powMod 7 ((Fr.modulus - 1) / 4096 * 4095) Fr.modulus := by
  decide +kernel

private theorem rootNat_eq_powMod : rootNat = Nat.powMod zetaNat 256 Fr.modulus := by
  decide +kernel

private theorem scaleNat_mul : scaleNat * 4096 % Fr.modulus = 1 := by decide +kernel

theorem isPrimitiveRoot_zeta : IsPrimitiveRoot zeta FIELD_ELEMENTS_PER_BLOB :=
  (isPrimitiveRoot_domainRoot field_elements_per_blob_dvd_modulus_sub_one).inv

theorem zetaNat_eq : (zetaNat : Fr) = zeta := by
  have hw := isPrimitiveRoot_domainRoot field_elements_per_blob_dvd_modulus_sub_one
  have hd : domainRoot FIELD_ELEMENTS_PER_BLOB = ((7 : Nat) : Fr) ^ ((Fr.modulus - 1) / 4096) := by
    rw [domainRoot, Fr.hpow_ofNat_eq_pow _ (by decide +kernel), Fr.ofNat_eq_natCast]
    rfl
  rw [← Fr.ofNat_eq_natCast, zetaNat_eq_powMod, (ofNat_powMod 7 _).2, pow_mul, ← hd, zeta,
    eq_comm]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ']
  exact hw.pow_eq_one

theorem rootNat_eq : (rootNat : Fr) = zeta ^ 256 := by
  rw [← Fr.ofNat_eq_natCast, rootNat_eq_powMod, (ofNat_powMod zetaNat 256).2,
    zetaNat_eq]

theorem scaleNat_eq : (scaleNat : Fr) = (4096 : Fr)⁻¹ := by
  have h : ((scaleNat * 4096 % Fr.modulus : Nat) : Fr) = 1 := by rw [scaleNat_mul, Nat.cast_one]
  rw [natCast_mod, Nat.cast_mul] at h
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [mul_comm]
  exact_mod_cast h

theorem isPrimitiveRoot_root : IsPrimitiveRoot (zeta ^ 256) 16 :=
  isPrimitiveRoot_zeta.pow (by decide) (by decide)

/-! ## The values

Each natural is the value of its element of `Fr`, by a proof on variables.
-/

theorem rootPowNat_spec (i : Nat) :
    rootPowNat i < Fr.modulus ∧ Fr.ofNat (rootPowNat i) = (zeta ^ 256) ^ i := by
  obtain ⟨hlt, heq⟩ := ofNat_powMod rootNat i
  exact ⟨hlt, heq.trans (by rw [rootNat_eq])⟩

theorem zetaPowNat_spec (e : Nat) :
    zetaPowNat e < Fr.modulus ∧ Fr.ofNat (zetaPowNat e) = zeta ^ e := by
  obtain ⟨hlt, heq⟩ := ofNat_powMod zetaNat e
  exact ⟨hlt, heq.trans (by rw [zetaNat_eq])⟩

theorem scalarB_spec (k1 j2 : Nat) :
    scalarB k1 j2 < Fr.modulus ∧
      Fr.ofNat (scalarB k1 j2) = (4096 : Fr)⁻¹ * zeta ^ (16 * j2 * k1) := by
  refine ⟨Nat.mod_lt _ Fr.modulus_pos, ?_⟩
  rw [scalarB, Fr.ofNat_eq_natCast, natCast_mod, Nat.cast_mul, scaleNat_eq,
    ← Fr.ofNat_eq_natCast, (zetaPowNat_spec _).2]

theorem scalarC_spec (k1 k2 j3 : Nat) :
    scalarC k1 k2 j3 < Fr.modulus ∧ Fr.ofNat (scalarC k1 k2 j3) = zeta ^ (j3 * (k1 + 16 * k2)) :=
  zetaPowNat_spec _

end EthLib.Cryptography.Kzg.SetupLagrange
