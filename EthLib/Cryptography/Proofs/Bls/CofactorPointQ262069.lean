module

public import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers

/-!
# Proofs: `262069`-torsion witness on the BLS12-381 twist
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

def q262069 : G2 := ⟨⟨Fp.ofNat 445689349790021496226481610041960119670818562344445314198349534378437798461866468235427851300387466736185843810614, Fp.ofNat 642130957506457077337037835884583121750509984993480752870042996214680726133991353560451529535834214250305831471661⟩, ⟨Fp.ofNat 3689501235694109950530354610934256590544644337586092604586486870082856386990140772018231157092461477750358316929703, Fp.ofNat 3689569798356755572404451911002206581319892419086545502402118524503951312562101915464666252217297686865197893821263⟩, Fp2.one⟩

theorem q262069_valid : G2.Valid q262069 := G2.valid_of_affine_equation (by decide +kernel)

theorem q262069_nonzero : G2.toPoint q262069 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q262069_valid).mpr hz
  exact Bool.noConfusion h

theorem q262069_annihilator : 262069 • G2.toPoint q262069 = 0 :=
  nsmul_zero_cert q262069 q262069_valid 262069 19 (by decide +kernel) (by decide +kernel)

theorem q262069_clear_zero : (clearAux q262069).isInfinity = true := by decide +kernel

end EthLib.Cryptography.Bls.CofactorCertificate
