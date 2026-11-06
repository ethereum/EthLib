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
    (TrustedSetupData.g1MonomialHex.toList.map codes).all checkCodes = true := by
  refine all_of_chunks checkCodes 16 256 _ (by rw [List.length_map]; decide +kernel)
    fun k hk => ?_
  match k, hk with
  | 0, _ => exact g1Monomial_chunk_0
  | 1, _ => exact g1Monomial_chunk_1
  | 2, _ => exact g1Monomial_chunk_2
  | 3, _ => exact g1Monomial_chunk_3
  | 4, _ => exact g1Monomial_chunk_4
  | 5, _ => exact g1Monomial_chunk_5
  | 6, _ => exact g1Monomial_chunk_6
  | 7, _ => exact g1Monomial_chunk_7
  | 8, _ => exact g1Monomial_chunk_8
  | 9, _ => exact g1Monomial_chunk_9
  | 10, _ => exact g1Monomial_chunk_10
  | 11, _ => exact g1Monomial_chunk_11
  | 12, _ => exact g1Monomial_chunk_12
  | 13, _ => exact g1Monomial_chunk_13
  | 14, _ => exact g1Monomial_chunk_14
  | 15, _ => exact g1Monomial_chunk_15
  | 16, _ => exact g1Monomial_chunk_16
  | 17, _ => exact g1Monomial_chunk_17
  | 18, _ => exact g1Monomial_chunk_18
  | 19, _ => exact g1Monomial_chunk_19
  | 20, _ => exact g1Monomial_chunk_20
  | 21, _ => exact g1Monomial_chunk_21
  | 22, _ => exact g1Monomial_chunk_22
  | 23, _ => exact g1Monomial_chunk_23
  | 24, _ => exact g1Monomial_chunk_24
  | 25, _ => exact g1Monomial_chunk_25
  | 26, _ => exact g1Monomial_chunk_26
  | 27, _ => exact g1Monomial_chunk_27
  | 28, _ => exact g1Monomial_chunk_28
  | 29, _ => exact g1Monomial_chunk_29
  | 30, _ => exact g1Monomial_chunk_30
  | 31, _ => exact g1Monomial_chunk_31
  | 32, _ => exact g1Monomial_chunk_32
  | 33, _ => exact g1Monomial_chunk_33
  | 34, _ => exact g1Monomial_chunk_34
  | 35, _ => exact g1Monomial_chunk_35
  | 36, _ => exact g1Monomial_chunk_36
  | 37, _ => exact g1Monomial_chunk_37
  | 38, _ => exact g1Monomial_chunk_38
  | 39, _ => exact g1Monomial_chunk_39
  | 40, _ => exact g1Monomial_chunk_40
  | 41, _ => exact g1Monomial_chunk_41
  | 42, _ => exact g1Monomial_chunk_42
  | 43, _ => exact g1Monomial_chunk_43
  | 44, _ => exact g1Monomial_chunk_44
  | 45, _ => exact g1Monomial_chunk_45
  | 46, _ => exact g1Monomial_chunk_46
  | 47, _ => exact g1Monomial_chunk_47
  | 48, _ => exact g1Monomial_chunk_48
  | 49, _ => exact g1Monomial_chunk_49
  | 50, _ => exact g1Monomial_chunk_50
  | 51, _ => exact g1Monomial_chunk_51
  | 52, _ => exact g1Monomial_chunk_52
  | 53, _ => exact g1Monomial_chunk_53
  | 54, _ => exact g1Monomial_chunk_54
  | 55, _ => exact g1Monomial_chunk_55
  | 56, _ => exact g1Monomial_chunk_56
  | 57, _ => exact g1Monomial_chunk_57
  | 58, _ => exact g1Monomial_chunk_58
  | 59, _ => exact g1Monomial_chunk_59
  | 60, _ => exact g1Monomial_chunk_60
  | 61, _ => exact g1Monomial_chunk_61
  | 62, _ => exact g1Monomial_chunk_62
  | 63, _ => exact g1Monomial_chunk_63
  | 64, _ => exact g1Monomial_chunk_64
  | 65, _ => exact g1Monomial_chunk_65
  | 66, _ => exact g1Monomial_chunk_66
  | 67, _ => exact g1Monomial_chunk_67
  | 68, _ => exact g1Monomial_chunk_68
  | 69, _ => exact g1Monomial_chunk_69
  | 70, _ => exact g1Monomial_chunk_70
  | 71, _ => exact g1Monomial_chunk_71
  | 72, _ => exact g1Monomial_chunk_72
  | 73, _ => exact g1Monomial_chunk_73
  | 74, _ => exact g1Monomial_chunk_74
  | 75, _ => exact g1Monomial_chunk_75
  | 76, _ => exact g1Monomial_chunk_76
  | 77, _ => exact g1Monomial_chunk_77
  | 78, _ => exact g1Monomial_chunk_78
  | 79, _ => exact g1Monomial_chunk_79
  | 80, _ => exact g1Monomial_chunk_80
  | 81, _ => exact g1Monomial_chunk_81
  | 82, _ => exact g1Monomial_chunk_82
  | 83, _ => exact g1Monomial_chunk_83
  | 84, _ => exact g1Monomial_chunk_84
  | 85, _ => exact g1Monomial_chunk_85
  | 86, _ => exact g1Monomial_chunk_86
  | 87, _ => exact g1Monomial_chunk_87
  | 88, _ => exact g1Monomial_chunk_88
  | 89, _ => exact g1Monomial_chunk_89
  | 90, _ => exact g1Monomial_chunk_90
  | 91, _ => exact g1Monomial_chunk_91
  | 92, _ => exact g1Monomial_chunk_92
  | 93, _ => exact g1Monomial_chunk_93
  | 94, _ => exact g1Monomial_chunk_94
  | 95, _ => exact g1Monomial_chunk_95
  | 96, _ => exact g1Monomial_chunk_96
  | 97, _ => exact g1Monomial_chunk_97
  | 98, _ => exact g1Monomial_chunk_98
  | 99, _ => exact g1Monomial_chunk_99
  | 100, _ => exact g1Monomial_chunk_100
  | 101, _ => exact g1Monomial_chunk_101
  | 102, _ => exact g1Monomial_chunk_102
  | 103, _ => exact g1Monomial_chunk_103
  | 104, _ => exact g1Monomial_chunk_104
  | 105, _ => exact g1Monomial_chunk_105
  | 106, _ => exact g1Monomial_chunk_106
  | 107, _ => exact g1Monomial_chunk_107
  | 108, _ => exact g1Monomial_chunk_108
  | 109, _ => exact g1Monomial_chunk_109
  | 110, _ => exact g1Monomial_chunk_110
  | 111, _ => exact g1Monomial_chunk_111
  | 112, _ => exact g1Monomial_chunk_112
  | 113, _ => exact g1Monomial_chunk_113
  | 114, _ => exact g1Monomial_chunk_114
  | 115, _ => exact g1Monomial_chunk_115
  | 116, _ => exact g1Monomial_chunk_116
  | 117, _ => exact g1Monomial_chunk_117
  | 118, _ => exact g1Monomial_chunk_118
  | 119, _ => exact g1Monomial_chunk_119
  | 120, _ => exact g1Monomial_chunk_120
  | 121, _ => exact g1Monomial_chunk_121
  | 122, _ => exact g1Monomial_chunk_122
  | 123, _ => exact g1Monomial_chunk_123
  | 124, _ => exact g1Monomial_chunk_124
  | 125, _ => exact g1Monomial_chunk_125
  | 126, _ => exact g1Monomial_chunk_126
  | 127, _ => exact g1Monomial_chunk_127
  | 128, _ => exact g1Monomial_chunk_128
  | 129, _ => exact g1Monomial_chunk_129
  | 130, _ => exact g1Monomial_chunk_130
  | 131, _ => exact g1Monomial_chunk_131
  | 132, _ => exact g1Monomial_chunk_132
  | 133, _ => exact g1Monomial_chunk_133
  | 134, _ => exact g1Monomial_chunk_134
  | 135, _ => exact g1Monomial_chunk_135
  | 136, _ => exact g1Monomial_chunk_136
  | 137, _ => exact g1Monomial_chunk_137
  | 138, _ => exact g1Monomial_chunk_138
  | 139, _ => exact g1Monomial_chunk_139
  | 140, _ => exact g1Monomial_chunk_140
  | 141, _ => exact g1Monomial_chunk_141
  | 142, _ => exact g1Monomial_chunk_142
  | 143, _ => exact g1Monomial_chunk_143
  | 144, _ => exact g1Monomial_chunk_144
  | 145, _ => exact g1Monomial_chunk_145
  | 146, _ => exact g1Monomial_chunk_146
  | 147, _ => exact g1Monomial_chunk_147
  | 148, _ => exact g1Monomial_chunk_148
  | 149, _ => exact g1Monomial_chunk_149
  | 150, _ => exact g1Monomial_chunk_150
  | 151, _ => exact g1Monomial_chunk_151
  | 152, _ => exact g1Monomial_chunk_152
  | 153, _ => exact g1Monomial_chunk_153
  | 154, _ => exact g1Monomial_chunk_154
  | 155, _ => exact g1Monomial_chunk_155
  | 156, _ => exact g1Monomial_chunk_156
  | 157, _ => exact g1Monomial_chunk_157
  | 158, _ => exact g1Monomial_chunk_158
  | 159, _ => exact g1Monomial_chunk_159
  | 160, _ => exact g1Monomial_chunk_160
  | 161, _ => exact g1Monomial_chunk_161
  | 162, _ => exact g1Monomial_chunk_162
  | 163, _ => exact g1Monomial_chunk_163
  | 164, _ => exact g1Monomial_chunk_164
  | 165, _ => exact g1Monomial_chunk_165
  | 166, _ => exact g1Monomial_chunk_166
  | 167, _ => exact g1Monomial_chunk_167
  | 168, _ => exact g1Monomial_chunk_168
  | 169, _ => exact g1Monomial_chunk_169
  | 170, _ => exact g1Monomial_chunk_170
  | 171, _ => exact g1Monomial_chunk_171
  | 172, _ => exact g1Monomial_chunk_172
  | 173, _ => exact g1Monomial_chunk_173
  | 174, _ => exact g1Monomial_chunk_174
  | 175, _ => exact g1Monomial_chunk_175
  | 176, _ => exact g1Monomial_chunk_176
  | 177, _ => exact g1Monomial_chunk_177
  | 178, _ => exact g1Monomial_chunk_178
  | 179, _ => exact g1Monomial_chunk_179
  | 180, _ => exact g1Monomial_chunk_180
  | 181, _ => exact g1Monomial_chunk_181
  | 182, _ => exact g1Monomial_chunk_182
  | 183, _ => exact g1Monomial_chunk_183
  | 184, _ => exact g1Monomial_chunk_184
  | 185, _ => exact g1Monomial_chunk_185
  | 186, _ => exact g1Monomial_chunk_186
  | 187, _ => exact g1Monomial_chunk_187
  | 188, _ => exact g1Monomial_chunk_188
  | 189, _ => exact g1Monomial_chunk_189
  | 190, _ => exact g1Monomial_chunk_190
  | 191, _ => exact g1Monomial_chunk_191
  | 192, _ => exact g1Monomial_chunk_192
  | 193, _ => exact g1Monomial_chunk_193
  | 194, _ => exact g1Monomial_chunk_194
  | 195, _ => exact g1Monomial_chunk_195
  | 196, _ => exact g1Monomial_chunk_196
  | 197, _ => exact g1Monomial_chunk_197
  | 198, _ => exact g1Monomial_chunk_198
  | 199, _ => exact g1Monomial_chunk_199
  | 200, _ => exact g1Monomial_chunk_200
  | 201, _ => exact g1Monomial_chunk_201
  | 202, _ => exact g1Monomial_chunk_202
  | 203, _ => exact g1Monomial_chunk_203
  | 204, _ => exact g1Monomial_chunk_204
  | 205, _ => exact g1Monomial_chunk_205
  | 206, _ => exact g1Monomial_chunk_206
  | 207, _ => exact g1Monomial_chunk_207
  | 208, _ => exact g1Monomial_chunk_208
  | 209, _ => exact g1Monomial_chunk_209
  | 210, _ => exact g1Monomial_chunk_210
  | 211, _ => exact g1Monomial_chunk_211
  | 212, _ => exact g1Monomial_chunk_212
  | 213, _ => exact g1Monomial_chunk_213
  | 214, _ => exact g1Monomial_chunk_214
  | 215, _ => exact g1Monomial_chunk_215
  | 216, _ => exact g1Monomial_chunk_216
  | 217, _ => exact g1Monomial_chunk_217
  | 218, _ => exact g1Monomial_chunk_218
  | 219, _ => exact g1Monomial_chunk_219
  | 220, _ => exact g1Monomial_chunk_220
  | 221, _ => exact g1Monomial_chunk_221
  | 222, _ => exact g1Monomial_chunk_222
  | 223, _ => exact g1Monomial_chunk_223
  | 224, _ => exact g1Monomial_chunk_224
  | 225, _ => exact g1Monomial_chunk_225
  | 226, _ => exact g1Monomial_chunk_226
  | 227, _ => exact g1Monomial_chunk_227
  | 228, _ => exact g1Monomial_chunk_228
  | 229, _ => exact g1Monomial_chunk_229
  | 230, _ => exact g1Monomial_chunk_230
  | 231, _ => exact g1Monomial_chunk_231
  | 232, _ => exact g1Monomial_chunk_232
  | 233, _ => exact g1Monomial_chunk_233
  | 234, _ => exact g1Monomial_chunk_234
  | 235, _ => exact g1Monomial_chunk_235
  | 236, _ => exact g1Monomial_chunk_236
  | 237, _ => exact g1Monomial_chunk_237
  | 238, _ => exact g1Monomial_chunk_238
  | 239, _ => exact g1Monomial_chunk_239
  | 240, _ => exact g1Monomial_chunk_240
  | 241, _ => exact g1Monomial_chunk_241
  | 242, _ => exact g1Monomial_chunk_242
  | 243, _ => exact g1Monomial_chunk_243
  | 244, _ => exact g1Monomial_chunk_244
  | 245, _ => exact g1Monomial_chunk_245
  | 246, _ => exact g1Monomial_chunk_246
  | 247, _ => exact g1Monomial_chunk_247
  | 248, _ => exact g1Monomial_chunk_248
  | 249, _ => exact g1Monomial_chunk_249
  | 250, _ => exact g1Monomial_chunk_250
  | 251, _ => exact g1Monomial_chunk_251
  | 252, _ => exact g1Monomial_chunk_252
  | 253, _ => exact g1Monomial_chunk_253
  | 254, _ => exact g1Monomial_chunk_254
  | 255, _ => exact g1Monomial_chunk_255
  | _ + 256, hk => omega

/-- Each byte string that the hexadecimal decoder returns decodes from one of the strings. -/
theorem TrustedSetup.hexListToBytes_mem {hex : Array String} {bytes : Array ByteArray}
    (h : TrustedSetup.hexListToBytes hex = .ok bytes) :
    ∀ b ∈ bytes, ∃ str ∈ hex, TrustedSetup.hexToBytes? str = some b := by
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
