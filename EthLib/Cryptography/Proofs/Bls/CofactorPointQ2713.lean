module

public import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers

/-!
# Proofs: `2713`-torsion witness on the BLS12-381 twist
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

def q2713 : G2 := ⟨⟨Fp.ofNat 2080236299627846373313113152824626203828184878063747179226546086444465609661079682578791473829990551645806380696196, Fp.ofNat 3052341607489697950751387535491288379717343093870489916200010831014739062904699435842761599142350073607242643439346⟩, ⟨Fp.ofNat 138786684136621197043348134664970982874021436480982065149993747241869262426861989119475052140103788150961461939542, Fp.ofNat 259935730919452527837578491626280728785308707164694630602396646913616192390693965039250352290890968067282376421371⟩, Fp2.one⟩

theorem q2713_valid : G2.Valid q2713 := G2.valid_of_affine_equation (by decide +kernel)

theorem q2713_nonzero : G2.toPoint q2713 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q2713_valid).mpr hz
  exact Bool.noConfusion h

theorem q2713_annihilator : 2713 • G2.toPoint q2713 = 0 :=
  nsmul_zero_cert q2713 q2713_valid 2713 13 (by decide +kernel) (by decide +kernel)

theorem q2713_clear_zero : (clearAux q2713).isInfinity = true := by decide +kernel

end EthLib.Cryptography.Bls.CofactorCertificate
