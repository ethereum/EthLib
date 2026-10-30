module

public import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers

/-!
# Proofs: Second independent `13`-torsion witness on the BLS12-381 twist
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

def independent13 : G2 := ⟨⟨Fp.ofNat 3785287291595963449363006157517216238553350702866930745119159863557026318432990055432590987617994111761605730590096, Fp.ofNat 184693031912202050728408694521708133615870844071267710200043165266197174504058993766601268896503937827921675108037⟩, ⟨Fp.ofNat 2195351338994857125885432308745262298009915734180443935023142416529216833251357026902328260293191354579154915458365, Fp.ofNat 1169630515586987845958993562785169716010090905281211931821796767787587650059725646863962186262369911948032443419257⟩, Fp2.one⟩

theorem independent13_valid : G2.Valid independent13 := G2.valid_of_affine_equation (by decide +kernel)

theorem independent13_nonzero : G2.toPoint independent13 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero independent13_valid).mpr hz
  exact Bool.noConfusion h

theorem independent13_annihilator : 13 • G2.toPoint independent13 = 0 :=
  nsmul_zero_cert independent13 independent13_valid 13 5 (by decide +kernel) (by decide +kernel)

theorem independent13_clear_zero : (clearAux independent13).isInfinity = true := by decide +kernel

end EthLib.Cryptography.Bls.CofactorCertificate
