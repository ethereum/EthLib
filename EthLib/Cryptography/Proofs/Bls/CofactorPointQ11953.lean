module

public import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers

/-!
# Proofs: `11953`-torsion witness on the BLS12-381 twist
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

def q11953 : G2 := ⟨⟨Fp.ofNat 3326039129978847390790895384478687990261604743660595966617629581407403980239182135876795661655021205373622298170592, Fp.ofNat 46869467146548478527694938494365300357293527333765386730280567959420038413149881837924443320450215905785660061369⟩, ⟨Fp.ofNat 1132298756428184765003661052478247226395618160691419912279189534963795943103439813278630167376312089258869064647885, Fp.ofNat 2270702702637852964440832104507229096623166001003608211729388228622052313321327540920170329339284344643394921561805⟩, Fp2.one⟩

theorem q11953_valid : G2.Valid q11953 := G2.valid_of_affine_equation (by decide +kernel)

theorem q11953_nonzero : G2.toPoint q11953 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q11953_valid).mpr hz
  exact Bool.noConfusion h

theorem q11953_annihilator : 11953 • G2.toPoint q11953 = 0 :=
  nsmul_zero_cert q11953 q11953_valid 11953 15 (by decide +kernel) (by decide +kernel)

theorem q11953_clear_zero : (clearAux q11953).isInfinity = true := by decide +kernel

end EthLib.Cryptography.Bls.CofactorCertificate
