module

public import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers

/-!
# Proofs: First `23`-torsion witness on the BLS12-381 twist
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

def q23 : G2 := ⟨⟨Fp.ofNat 2739514132123941011419517956760862005679983982245647736180827416338821616902655461283968649770562245565651778429134, Fp.ofNat 2808334985466809599109983998418602290148679938845248472406492739371341701874467784583103417930025166484777514627271⟩, ⟨Fp.ofNat 823838782298367016162934668769581913696070428562677941071263521524279588658526909716995604446071443076365015951250, Fp.ofNat 2031906053439228426992397463759315426993470729766381570058783639267049648019329365797683926182988977613511984373688⟩, Fp2.one⟩

theorem q23_valid : G2.Valid q23 := G2.valid_of_affine_equation (by decide +kernel)

theorem q23_nonzero : G2.toPoint q23 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q23_valid).mpr hz
  exact Bool.noConfusion h

theorem q23_annihilator : 23 • G2.toPoint q23 = 0 :=
  nsmul_zero_cert q23 q23_valid 23 6 (by decide +kernel) (by decide +kernel)

theorem q23_clear_zero : (clearAux q23).isInfinity = true := by decide +kernel

end EthLib.Cryptography.Bls.CofactorCertificate
