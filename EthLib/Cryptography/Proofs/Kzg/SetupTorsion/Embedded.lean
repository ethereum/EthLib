module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial00
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial01
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial02
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial03
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial04
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial05
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial06
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial07
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial08
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial09
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial10
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial11
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial12
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial13
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial14
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Monomial15
public import EthLib.Cryptography.Proofs.Kzg.Fk20Proofs

/-!
# Proofs: the monomial points of the embedded setup have order dividing `r`

The FK20 theorems need each monomial point of `G1` in the setup to have order dividing `r`.

The decoder checks only that a point is on the curve, so a decoded point need not have that order.

For the embedded setup, the kernel checks each of the 4096 monomial points of `G1`.

So if the embedded setup decodes, each of these points has order dividing `r`.

Then the FK20 theorems hold for the embedded setup with no hypothesis on its points.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 Fr)
open EthLib.Cryptography.Kzg.Constants
open SetupTorsion
open EthLib.Base (array_mapM_ok_mem)

/-- Every monomial point of `G1` in the embedded data passes the kernel check. -/
theorem SetupTorsion.g1MonomialHex_check :
    (TrustedSetupData.g1MonomialHex.toList.map codes).all checkCodes = true :=
  all_of_chunks checkCodes 16 256 _ (by rw [List.length_map]; decide +kernel)
    (checks_of% g1Monomial_chunk 256)

/-- Each byte string that the hexadecimal decoder returns decodes from one of the strings. -/
theorem TrustedSetup.hexListToBytes_mem {hex : Array String} {bytes : Array ByteArray}
    (h : TrustedSetup.hexListToBytes hex = .ok bytes) :
    ∀ b ∈ bytes, ∃ str ∈ hex, Base.hexBytes? str.toList = some b := by
  intro b hb
  obtain ⟨str, hmem, hstr⟩ := array_mapM_ok_mem h b hb
  refine ⟨str, hmem, ?_⟩
  split at hstr
  · rename_i b' hb'
    cases hstr
    exact hb'
  · cases hstr

/-- If the embedded setup decodes, each of its monomial points of `G1` has order dividing `r`. -/
theorem TrustedSetup.ofHex_torsion {s : TrustedSetup} (h : TrustedSetup.ofHex = .ok s)
    {t : Nat} (ht : t < FIELD_ELEMENTS_PER_BLOB) :
    Fr.modulus • G1.toPoint s.g1Monomial.toArray[t]! = 0 := by
  unfold TrustedSetup.ofHex at h
  -- The three lists stay abstract, so no step evaluates the decoding.
  generalize TrustedSetup.hexListToBytes TrustedSetupData.g1LagrangeHex = a at h
  generalize hb : TrustedSetup.hexListToBytes TrustedSetupData.g1MonomialHex = b at h
  generalize TrustedSetup.hexListToBytes TrustedSetupData.g2MonomialHex = c at h
  cases a with
  | error e => cases h
  | ok x =>
  cases b with
  | error e => cases h
  | ok y =>
  cases c with
  | error e => cases h
  | ok z =>
  obtain ⟨bytes, hmem, hu⟩ := TrustedSetup.ofBytes_g1Monomial_mem h ⟨t, ht⟩
  obtain ⟨str, hstr, hhex⟩ := TrustedSetup.hexListToBytes_mem hb bytes hmem
  have hc := List.all_eq_true.mp g1MonomialHex_check (codes str)
    (List.mem_map_of_mem (Array.mem_toList_iff.mpr hstr))
  rw [getElem!_pos s.g1Monomial.toArray t (by simpa using ht)]
  exact SetupTorsion.modulus_smul_eq_zero hc hhex hu

/-! ## FK20 for the embedded setup -/

/-- The agreement of FK20 with the direct method, for a decoded blob and the embedded setup. -/
theorem computeCellsAndKzgProofs_blob_spec_ofHex
    {setup : TrustedSetup} {blob : Blob} {poly : Polynomial}
    {cellIndex : CellIndex} {coset : Coset}
    (hsetup : TrustedSetup.ofHex = .ok setup)
    (hblob : blobToPolynomial blob = .ok poly)
    (hcoset : cosetForCell cellIndex = .ok coset) :
    let polynomialCoeff := polynomialEvalToCoeff poly
    ∃ vanishing quotient,
      vanishingPolynomialcoeff coset = .ok vanishing ∧
      dividePolynomialcoeff polynomialCoeff vanishing = .ok quotient ∧
      g1LincombPoints (setup.g1Monomial.toArray.extract 0 quotient.size) quotient =
        pure (Bls.G1.msm (setup.g1Monomial.toArray.extract 0 quotient.size) quotient) ∧
      (fk20CellsAndProofs setup polynomialCoeff).1[cellIndex]! =
        cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff)) ∧
      (fk20CellsAndProofs setup polynomialCoeff).2[cellIndex]! =
        compressG1 (Bls.G1.msm (setup.g1Monomial.toArray.extract 0 quotient.size) quotient) :=
  computeCellsAndKzgProofs_blob_spec hblob (TrustedSetup.ofHex_valid hsetup)
    (fun _ ht => TrustedSetup.ofHex_torsion hsetup (Nat.lt_of_lt_of_le ht (Nat.sub_le _ _))) hcoset

/-- Recovery of cells and proofs, end to end, with the embedded setup. -/
theorem recoverCellsAndKzgProofs_spec_ofHex
    {setup : TrustedSetup} {p : PolynomialCoeff}
    {cellIndices : Array CellIndex} {cells : Array Cell} {cosetsEvals : Array CosetEvals}
    {cellIndex : CellIndex} {coset : Coset}
    (hsetup : TrustedSetup.ofHex = .ok setup)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hlen : cells.size = cellIndices.size)
    (hmin : CELLS_PER_EXT_BLOB / 2 ≤ cellIndices.size)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hasc : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = false)
    (hdec : cells.mapM cellToCosetEvals = .ok cosetsEvals)
    (hmatch : RecoverySamplesMatch p cellIndices cosetsEvals)
    (hcoset : cosetForCell cellIndex = .ok coset) :
    recoverCellsAndKzgProofs setup cellIndices cells = .ok (fk20CellsAndProofs setup p) ∧
    ∃ vanishing quotient,
      vanishingPolynomialcoeff coset = .ok vanishing ∧
      dividePolynomialcoeff p vanishing = .ok quotient ∧
      g1LincombPoints (setup.g1Monomial.toArray.extract 0 quotient.size) quotient =
        pure (Bls.G1.msm (setup.g1Monomial.toArray.extract 0 quotient.size) quotient) ∧
      (fk20CellsAndProofs setup p).1[cellIndex]! =
        cosetEvalsToCell (coset.map (evaluatePolynomialcoeff p)) ∧
      (fk20CellsAndProofs setup p).2[cellIndex]! =
        compressG1 (Bls.G1.msm (setup.g1Monomial.toArray.extract 0 quotient.size) quotient) :=
  recoverCellsAndKzgProofs_spec hp hlen hmin hbound hasc hdec hmatch
    (TrustedSetup.ofHex_valid hsetup)
    (fun _ ht => TrustedSetup.ofHex_torsion hsetup (Nat.lt_of_lt_of_le ht (Nat.sub_le _ _))) hcoset

end EthLib.Cryptography.Kzg
