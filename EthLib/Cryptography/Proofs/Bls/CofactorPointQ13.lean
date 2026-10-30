module

public import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers

/-!
# Proofs: First `13`-torsion witness on the BLS12-381 twist
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

def q13 : G2 := ⟨⟨Fp.ofNat 1516098791699854445898040942928908183909589580246243101257906827426941180554051446550909392579893885218899574105342, Fp.ofNat 3238348490633667398671220956466993747193162347072298219945119514673806511256992531672936690515562397981251002873140⟩, ⟨Fp.ofNat 1335703926339566895459396325186780453917867606042000656714301712043796819408375335349836437088055061353604837545944, Fp.ofNat 2109266869945624999895480995372359165588627724687444010520175867072438469009929776678291010240416096404626491488021⟩, Fp2.one⟩

theorem q13_valid : G2.Valid q13 := G2.valid_of_affine_equation (by decide +kernel)

theorem q13_nonzero : G2.toPoint q13 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q13_valid).mpr hz
  exact Bool.noConfusion h

theorem q13_annihilator : 13 • G2.toPoint q13 = 0 :=
  nsmul_zero_cert q13 q13_valid 13 5 (by decide +kernel) (by decide +kernel)

theorem q13_clear_zero : (clearAux q13).isInfinity = true := by decide +kernel

end EthLib.Cryptography.Bls.CofactorCertificate
