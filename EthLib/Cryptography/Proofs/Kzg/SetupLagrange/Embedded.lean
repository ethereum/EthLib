module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange0
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange1
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange2
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange3
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial0
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial1
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial2
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial3
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA00
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA01
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA02
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA03
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA04
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA05
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA06
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA07
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA08
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA09
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA10
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA11
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA12
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA13
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA14
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA15
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB00
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB01
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB02
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB03
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB04
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB05
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB06
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB07
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB08
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB09
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB10
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB11
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB12
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB13
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB14
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB15
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC00
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC01
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC02
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC03
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC04
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC05
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC06
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC07
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC08
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC09
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC10
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC11
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC12
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC13
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC14
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC15

/-!
# Proofs: the Lagrange points of the embedded setup come from its monomial points

The embedded setup holds 4096 monomial points and 4096 Lagrange points of `G1`.

The kernel checks that the Lagrange points are the inverse transform of the monomial points.

The check tests that each string encodes its table point, and runs 768 transforms of size 16.

So if the embedded setup decodes, each Lagrange point is a sum of the monomial points.

The factors are the coefficients of its basis polynomial.

Then the setup is well formed at `τ` as soon as its monomial points represent the powers of `τ`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open SetupLagrange

/-- If the embedded setup decodes, each Lagrange point is a sum of the monomial points.

The factors are the coefficients of its basis polynomial. -/
theorem TrustedSetup.ofHex_lagrangeOfMonomial {s : TrustedSetup}
    (h : TrustedSetup.ofHex = .ok s) : s.LagrangeOfMonomial := by
  refine lagrangeOfMonomial_of_checks (tM := tableM) (tA := tableA) (tB := tableB)
    (tL := tableL) h
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    match c, hc with
    | 0, _ => exact decodeM_0
    | 1, _ => exact decodeM_1
    | 2, _ => exact decodeM_2
    | 3, _ => exact decodeM_3
    | 4, _ => exact decodeM_4
    | 5, _ => exact decodeM_5
    | 6, _ => exact decodeM_6
    | 7, _ => exact decodeM_7
    | 8, _ => exact decodeM_8
    | 9, _ => exact decodeM_9
    | 10, _ => exact decodeM_10
    | 11, _ => exact decodeM_11
    | 12, _ => exact decodeM_12
    | 13, _ => exact decodeM_13
    | 14, _ => exact decodeM_14
    | 15, _ => exact decodeM_15
    | 16, _ => exact decodeM_16
    | 17, _ => exact decodeM_17
    | 18, _ => exact decodeM_18
    | 19, _ => exact decodeM_19
    | 20, _ => exact decodeM_20
    | 21, _ => exact decodeM_21
    | 22, _ => exact decodeM_22
    | 23, _ => exact decodeM_23
    | 24, _ => exact decodeM_24
    | 25, _ => exact decodeM_25
    | 26, _ => exact decodeM_26
    | 27, _ => exact decodeM_27
    | 28, _ => exact decodeM_28
    | 29, _ => exact decodeM_29
    | 30, _ => exact decodeM_30
    | 31, _ => exact decodeM_31
    | 32, _ => exact decodeM_32
    | 33, _ => exact decodeM_33
    | 34, _ => exact decodeM_34
    | 35, _ => exact decodeM_35
    | 36, _ => exact decodeM_36
    | 37, _ => exact decodeM_37
    | 38, _ => exact decodeM_38
    | 39, _ => exact decodeM_39
    | 40, _ => exact decodeM_40
    | 41, _ => exact decodeM_41
    | 42, _ => exact decodeM_42
    | 43, _ => exact decodeM_43
    | 44, _ => exact decodeM_44
    | 45, _ => exact decodeM_45
    | 46, _ => exact decodeM_46
    | 47, _ => exact decodeM_47
    | 48, _ => exact decodeM_48
    | 49, _ => exact decodeM_49
    | 50, _ => exact decodeM_50
    | 51, _ => exact decodeM_51
    | 52, _ => exact decodeM_52
    | 53, _ => exact decodeM_53
    | 54, _ => exact decodeM_54
    | 55, _ => exact decodeM_55
    | 56, _ => exact decodeM_56
    | 57, _ => exact decodeM_57
    | 58, _ => exact decodeM_58
    | 59, _ => exact decodeM_59
    | 60, _ => exact decodeM_60
    | 61, _ => exact decodeM_61
    | 62, _ => exact decodeM_62
    | 63, _ => exact decodeM_63
    | 64, _ => exact decodeM_64
    | 65, _ => exact decodeM_65
    | 66, _ => exact decodeM_66
    | 67, _ => exact decodeM_67
    | 68, _ => exact decodeM_68
    | 69, _ => exact decodeM_69
    | 70, _ => exact decodeM_70
    | 71, _ => exact decodeM_71
    | 72, _ => exact decodeM_72
    | 73, _ => exact decodeM_73
    | 74, _ => exact decodeM_74
    | 75, _ => exact decodeM_75
    | 76, _ => exact decodeM_76
    | 77, _ => exact decodeM_77
    | 78, _ => exact decodeM_78
    | 79, _ => exact decodeM_79
    | 80, _ => exact decodeM_80
    | 81, _ => exact decodeM_81
    | 82, _ => exact decodeM_82
    | 83, _ => exact decodeM_83
    | 84, _ => exact decodeM_84
    | 85, _ => exact decodeM_85
    | 86, _ => exact decodeM_86
    | 87, _ => exact decodeM_87
    | 88, _ => exact decodeM_88
    | 89, _ => exact decodeM_89
    | 90, _ => exact decodeM_90
    | 91, _ => exact decodeM_91
    | 92, _ => exact decodeM_92
    | 93, _ => exact decodeM_93
    | 94, _ => exact decodeM_94
    | 95, _ => exact decodeM_95
    | 96, _ => exact decodeM_96
    | 97, _ => exact decodeM_97
    | 98, _ => exact decodeM_98
    | 99, _ => exact decodeM_99
    | 100, _ => exact decodeM_100
    | 101, _ => exact decodeM_101
    | 102, _ => exact decodeM_102
    | 103, _ => exact decodeM_103
    | 104, _ => exact decodeM_104
    | 105, _ => exact decodeM_105
    | 106, _ => exact decodeM_106
    | 107, _ => exact decodeM_107
    | 108, _ => exact decodeM_108
    | 109, _ => exact decodeM_109
    | 110, _ => exact decodeM_110
    | 111, _ => exact decodeM_111
    | 112, _ => exact decodeM_112
    | 113, _ => exact decodeM_113
    | 114, _ => exact decodeM_114
    | 115, _ => exact decodeM_115
    | 116, _ => exact decodeM_116
    | 117, _ => exact decodeM_117
    | 118, _ => exact decodeM_118
    | 119, _ => exact decodeM_119
    | 120, _ => exact decodeM_120
    | 121, _ => exact decodeM_121
    | 122, _ => exact decodeM_122
    | 123, _ => exact decodeM_123
    | 124, _ => exact decodeM_124
    | 125, _ => exact decodeM_125
    | 126, _ => exact decodeM_126
    | 127, _ => exact decodeM_127
    | 128, _ => exact decodeM_128
    | 129, _ => exact decodeM_129
    | 130, _ => exact decodeM_130
    | 131, _ => exact decodeM_131
    | 132, _ => exact decodeM_132
    | 133, _ => exact decodeM_133
    | 134, _ => exact decodeM_134
    | 135, _ => exact decodeM_135
    | 136, _ => exact decodeM_136
    | 137, _ => exact decodeM_137
    | 138, _ => exact decodeM_138
    | 139, _ => exact decodeM_139
    | 140, _ => exact decodeM_140
    | 141, _ => exact decodeM_141
    | 142, _ => exact decodeM_142
    | 143, _ => exact decodeM_143
    | 144, _ => exact decodeM_144
    | 145, _ => exact decodeM_145
    | 146, _ => exact decodeM_146
    | 147, _ => exact decodeM_147
    | 148, _ => exact decodeM_148
    | 149, _ => exact decodeM_149
    | 150, _ => exact decodeM_150
    | 151, _ => exact decodeM_151
    | 152, _ => exact decodeM_152
    | 153, _ => exact decodeM_153
    | 154, _ => exact decodeM_154
    | 155, _ => exact decodeM_155
    | 156, _ => exact decodeM_156
    | 157, _ => exact decodeM_157
    | 158, _ => exact decodeM_158
    | 159, _ => exact decodeM_159
    | 160, _ => exact decodeM_160
    | 161, _ => exact decodeM_161
    | 162, _ => exact decodeM_162
    | 163, _ => exact decodeM_163
    | 164, _ => exact decodeM_164
    | 165, _ => exact decodeM_165
    | 166, _ => exact decodeM_166
    | 167, _ => exact decodeM_167
    | 168, _ => exact decodeM_168
    | 169, _ => exact decodeM_169
    | 170, _ => exact decodeM_170
    | 171, _ => exact decodeM_171
    | 172, _ => exact decodeM_172
    | 173, _ => exact decodeM_173
    | 174, _ => exact decodeM_174
    | 175, _ => exact decodeM_175
    | 176, _ => exact decodeM_176
    | 177, _ => exact decodeM_177
    | 178, _ => exact decodeM_178
    | 179, _ => exact decodeM_179
    | 180, _ => exact decodeM_180
    | 181, _ => exact decodeM_181
    | 182, _ => exact decodeM_182
    | 183, _ => exact decodeM_183
    | 184, _ => exact decodeM_184
    | 185, _ => exact decodeM_185
    | 186, _ => exact decodeM_186
    | 187, _ => exact decodeM_187
    | 188, _ => exact decodeM_188
    | 189, _ => exact decodeM_189
    | 190, _ => exact decodeM_190
    | 191, _ => exact decodeM_191
    | 192, _ => exact decodeM_192
    | 193, _ => exact decodeM_193
    | 194, _ => exact decodeM_194
    | 195, _ => exact decodeM_195
    | 196, _ => exact decodeM_196
    | 197, _ => exact decodeM_197
    | 198, _ => exact decodeM_198
    | 199, _ => exact decodeM_199
    | 200, _ => exact decodeM_200
    | 201, _ => exact decodeM_201
    | 202, _ => exact decodeM_202
    | 203, _ => exact decodeM_203
    | 204, _ => exact decodeM_204
    | 205, _ => exact decodeM_205
    | 206, _ => exact decodeM_206
    | 207, _ => exact decodeM_207
    | 208, _ => exact decodeM_208
    | 209, _ => exact decodeM_209
    | 210, _ => exact decodeM_210
    | 211, _ => exact decodeM_211
    | 212, _ => exact decodeM_212
    | 213, _ => exact decodeM_213
    | 214, _ => exact decodeM_214
    | 215, _ => exact decodeM_215
    | 216, _ => exact decodeM_216
    | 217, _ => exact decodeM_217
    | 218, _ => exact decodeM_218
    | 219, _ => exact decodeM_219
    | 220, _ => exact decodeM_220
    | 221, _ => exact decodeM_221
    | 222, _ => exact decodeM_222
    | 223, _ => exact decodeM_223
    | 224, _ => exact decodeM_224
    | 225, _ => exact decodeM_225
    | 226, _ => exact decodeM_226
    | 227, _ => exact decodeM_227
    | 228, _ => exact decodeM_228
    | 229, _ => exact decodeM_229
    | 230, _ => exact decodeM_230
    | 231, _ => exact decodeM_231
    | 232, _ => exact decodeM_232
    | 233, _ => exact decodeM_233
    | 234, _ => exact decodeM_234
    | 235, _ => exact decodeM_235
    | 236, _ => exact decodeM_236
    | 237, _ => exact decodeM_237
    | 238, _ => exact decodeM_238
    | 239, _ => exact decodeM_239
    | 240, _ => exact decodeM_240
    | 241, _ => exact decodeM_241
    | 242, _ => exact decodeM_242
    | 243, _ => exact decodeM_243
    | 244, _ => exact decodeM_244
    | 245, _ => exact decodeM_245
    | 246, _ => exact decodeM_246
    | 247, _ => exact decodeM_247
    | 248, _ => exact decodeM_248
    | 249, _ => exact decodeM_249
    | 250, _ => exact decodeM_250
    | 251, _ => exact decodeM_251
    | 252, _ => exact decodeM_252
    | 253, _ => exact decodeM_253
    | 254, _ => exact decodeM_254
    | 255, _ => exact decodeM_255
    | _ + 256, hc => omega
  · intro c hc
    match c, hc with
    | 0, _ => exact decodeL_0
    | 1, _ => exact decodeL_1
    | 2, _ => exact decodeL_2
    | 3, _ => exact decodeL_3
    | 4, _ => exact decodeL_4
    | 5, _ => exact decodeL_5
    | 6, _ => exact decodeL_6
    | 7, _ => exact decodeL_7
    | 8, _ => exact decodeL_8
    | 9, _ => exact decodeL_9
    | 10, _ => exact decodeL_10
    | 11, _ => exact decodeL_11
    | 12, _ => exact decodeL_12
    | 13, _ => exact decodeL_13
    | 14, _ => exact decodeL_14
    | 15, _ => exact decodeL_15
    | 16, _ => exact decodeL_16
    | 17, _ => exact decodeL_17
    | 18, _ => exact decodeL_18
    | 19, _ => exact decodeL_19
    | 20, _ => exact decodeL_20
    | 21, _ => exact decodeL_21
    | 22, _ => exact decodeL_22
    | 23, _ => exact decodeL_23
    | 24, _ => exact decodeL_24
    | 25, _ => exact decodeL_25
    | 26, _ => exact decodeL_26
    | 27, _ => exact decodeL_27
    | 28, _ => exact decodeL_28
    | 29, _ => exact decodeL_29
    | 30, _ => exact decodeL_30
    | 31, _ => exact decodeL_31
    | 32, _ => exact decodeL_32
    | 33, _ => exact decodeL_33
    | 34, _ => exact decodeL_34
    | 35, _ => exact decodeL_35
    | 36, _ => exact decodeL_36
    | 37, _ => exact decodeL_37
    | 38, _ => exact decodeL_38
    | 39, _ => exact decodeL_39
    | 40, _ => exact decodeL_40
    | 41, _ => exact decodeL_41
    | 42, _ => exact decodeL_42
    | 43, _ => exact decodeL_43
    | 44, _ => exact decodeL_44
    | 45, _ => exact decodeL_45
    | 46, _ => exact decodeL_46
    | 47, _ => exact decodeL_47
    | 48, _ => exact decodeL_48
    | 49, _ => exact decodeL_49
    | 50, _ => exact decodeL_50
    | 51, _ => exact decodeL_51
    | 52, _ => exact decodeL_52
    | 53, _ => exact decodeL_53
    | 54, _ => exact decodeL_54
    | 55, _ => exact decodeL_55
    | 56, _ => exact decodeL_56
    | 57, _ => exact decodeL_57
    | 58, _ => exact decodeL_58
    | 59, _ => exact decodeL_59
    | 60, _ => exact decodeL_60
    | 61, _ => exact decodeL_61
    | 62, _ => exact decodeL_62
    | 63, _ => exact decodeL_63
    | 64, _ => exact decodeL_64
    | 65, _ => exact decodeL_65
    | 66, _ => exact decodeL_66
    | 67, _ => exact decodeL_67
    | 68, _ => exact decodeL_68
    | 69, _ => exact decodeL_69
    | 70, _ => exact decodeL_70
    | 71, _ => exact decodeL_71
    | 72, _ => exact decodeL_72
    | 73, _ => exact decodeL_73
    | 74, _ => exact decodeL_74
    | 75, _ => exact decodeL_75
    | 76, _ => exact decodeL_76
    | 77, _ => exact decodeL_77
    | 78, _ => exact decodeL_78
    | 79, _ => exact decodeL_79
    | 80, _ => exact decodeL_80
    | 81, _ => exact decodeL_81
    | 82, _ => exact decodeL_82
    | 83, _ => exact decodeL_83
    | 84, _ => exact decodeL_84
    | 85, _ => exact decodeL_85
    | 86, _ => exact decodeL_86
    | 87, _ => exact decodeL_87
    | 88, _ => exact decodeL_88
    | 89, _ => exact decodeL_89
    | 90, _ => exact decodeL_90
    | 91, _ => exact decodeL_91
    | 92, _ => exact decodeL_92
    | 93, _ => exact decodeL_93
    | 94, _ => exact decodeL_94
    | 95, _ => exact decodeL_95
    | 96, _ => exact decodeL_96
    | 97, _ => exact decodeL_97
    | 98, _ => exact decodeL_98
    | 99, _ => exact decodeL_99
    | 100, _ => exact decodeL_100
    | 101, _ => exact decodeL_101
    | 102, _ => exact decodeL_102
    | 103, _ => exact decodeL_103
    | 104, _ => exact decodeL_104
    | 105, _ => exact decodeL_105
    | 106, _ => exact decodeL_106
    | 107, _ => exact decodeL_107
    | 108, _ => exact decodeL_108
    | 109, _ => exact decodeL_109
    | 110, _ => exact decodeL_110
    | 111, _ => exact decodeL_111
    | 112, _ => exact decodeL_112
    | 113, _ => exact decodeL_113
    | 114, _ => exact decodeL_114
    | 115, _ => exact decodeL_115
    | 116, _ => exact decodeL_116
    | 117, _ => exact decodeL_117
    | 118, _ => exact decodeL_118
    | 119, _ => exact decodeL_119
    | 120, _ => exact decodeL_120
    | 121, _ => exact decodeL_121
    | 122, _ => exact decodeL_122
    | 123, _ => exact decodeL_123
    | 124, _ => exact decodeL_124
    | 125, _ => exact decodeL_125
    | 126, _ => exact decodeL_126
    | 127, _ => exact decodeL_127
    | 128, _ => exact decodeL_128
    | 129, _ => exact decodeL_129
    | 130, _ => exact decodeL_130
    | 131, _ => exact decodeL_131
    | 132, _ => exact decodeL_132
    | 133, _ => exact decodeL_133
    | 134, _ => exact decodeL_134
    | 135, _ => exact decodeL_135
    | 136, _ => exact decodeL_136
    | 137, _ => exact decodeL_137
    | 138, _ => exact decodeL_138
    | 139, _ => exact decodeL_139
    | 140, _ => exact decodeL_140
    | 141, _ => exact decodeL_141
    | 142, _ => exact decodeL_142
    | 143, _ => exact decodeL_143
    | 144, _ => exact decodeL_144
    | 145, _ => exact decodeL_145
    | 146, _ => exact decodeL_146
    | 147, _ => exact decodeL_147
    | 148, _ => exact decodeL_148
    | 149, _ => exact decodeL_149
    | 150, _ => exact decodeL_150
    | 151, _ => exact decodeL_151
    | 152, _ => exact decodeL_152
    | 153, _ => exact decodeL_153
    | 154, _ => exact decodeL_154
    | 155, _ => exact decodeL_155
    | 156, _ => exact decodeL_156
    | 157, _ => exact decodeL_157
    | 158, _ => exact decodeL_158
    | 159, _ => exact decodeL_159
    | 160, _ => exact decodeL_160
    | 161, _ => exact decodeL_161
    | 162, _ => exact decodeL_162
    | 163, _ => exact decodeL_163
    | 164, _ => exact decodeL_164
    | 165, _ => exact decodeL_165
    | 166, _ => exact decodeL_166
    | 167, _ => exact decodeL_167
    | 168, _ => exact decodeL_168
    | 169, _ => exact decodeL_169
    | 170, _ => exact decodeL_170
    | 171, _ => exact decodeL_171
    | 172, _ => exact decodeL_172
    | 173, _ => exact decodeL_173
    | 174, _ => exact decodeL_174
    | 175, _ => exact decodeL_175
    | 176, _ => exact decodeL_176
    | 177, _ => exact decodeL_177
    | 178, _ => exact decodeL_178
    | 179, _ => exact decodeL_179
    | 180, _ => exact decodeL_180
    | 181, _ => exact decodeL_181
    | 182, _ => exact decodeL_182
    | 183, _ => exact decodeL_183
    | 184, _ => exact decodeL_184
    | 185, _ => exact decodeL_185
    | 186, _ => exact decodeL_186
    | 187, _ => exact decodeL_187
    | 188, _ => exact decodeL_188
    | 189, _ => exact decodeL_189
    | 190, _ => exact decodeL_190
    | 191, _ => exact decodeL_191
    | 192, _ => exact decodeL_192
    | 193, _ => exact decodeL_193
    | 194, _ => exact decodeL_194
    | 195, _ => exact decodeL_195
    | 196, _ => exact decodeL_196
    | 197, _ => exact decodeL_197
    | 198, _ => exact decodeL_198
    | 199, _ => exact decodeL_199
    | 200, _ => exact decodeL_200
    | 201, _ => exact decodeL_201
    | 202, _ => exact decodeL_202
    | 203, _ => exact decodeL_203
    | 204, _ => exact decodeL_204
    | 205, _ => exact decodeL_205
    | 206, _ => exact decodeL_206
    | 207, _ => exact decodeL_207
    | 208, _ => exact decodeL_208
    | 209, _ => exact decodeL_209
    | 210, _ => exact decodeL_210
    | 211, _ => exact decodeL_211
    | 212, _ => exact decodeL_212
    | 213, _ => exact decodeL_213
    | 214, _ => exact decodeL_214
    | 215, _ => exact decodeL_215
    | 216, _ => exact decodeL_216
    | 217, _ => exact decodeL_217
    | 218, _ => exact decodeL_218
    | 219, _ => exact decodeL_219
    | 220, _ => exact decodeL_220
    | 221, _ => exact decodeL_221
    | 222, _ => exact decodeL_222
    | 223, _ => exact decodeL_223
    | 224, _ => exact decodeL_224
    | 225, _ => exact decodeL_225
    | 226, _ => exact decodeL_226
    | 227, _ => exact decodeL_227
    | 228, _ => exact decodeL_228
    | 229, _ => exact decodeL_229
    | 230, _ => exact decodeL_230
    | 231, _ => exact decodeL_231
    | 232, _ => exact decodeL_232
    | 233, _ => exact decodeL_233
    | 234, _ => exact decodeL_234
    | 235, _ => exact decodeL_235
    | 236, _ => exact decodeL_236
    | 237, _ => exact decodeL_237
    | 238, _ => exact decodeL_238
    | 239, _ => exact decodeL_239
    | 240, _ => exact decodeL_240
    | 241, _ => exact decodeL_241
    | 242, _ => exact decodeL_242
    | 243, _ => exact decodeL_243
    | 244, _ => exact decodeL_244
    | 245, _ => exact decodeL_245
    | 246, _ => exact decodeL_246
    | 247, _ => exact decodeL_247
    | 248, _ => exact decodeL_248
    | 249, _ => exact decodeL_249
    | 250, _ => exact decodeL_250
    | 251, _ => exact decodeL_251
    | 252, _ => exact decodeL_252
    | 253, _ => exact decodeL_253
    | 254, _ => exact decodeL_254
    | 255, _ => exact decodeL_255
    | _ + 256, hc => omega
  · intro j2 hj2 j3 hj3
    match j2, hj2 with
    | 0, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_0_0
      | 1, _ => exact checkA_0_1
      | 2, _ => exact checkA_0_2
      | 3, _ => exact checkA_0_3
      | 4, _ => exact checkA_0_4
      | 5, _ => exact checkA_0_5
      | 6, _ => exact checkA_0_6
      | 7, _ => exact checkA_0_7
      | 8, _ => exact checkA_0_8
      | 9, _ => exact checkA_0_9
      | 10, _ => exact checkA_0_10
      | 11, _ => exact checkA_0_11
      | 12, _ => exact checkA_0_12
      | 13, _ => exact checkA_0_13
      | 14, _ => exact checkA_0_14
      | 15, _ => exact checkA_0_15
      | _ + 16, h => omega
    | 1, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_1_0
      | 1, _ => exact checkA_1_1
      | 2, _ => exact checkA_1_2
      | 3, _ => exact checkA_1_3
      | 4, _ => exact checkA_1_4
      | 5, _ => exact checkA_1_5
      | 6, _ => exact checkA_1_6
      | 7, _ => exact checkA_1_7
      | 8, _ => exact checkA_1_8
      | 9, _ => exact checkA_1_9
      | 10, _ => exact checkA_1_10
      | 11, _ => exact checkA_1_11
      | 12, _ => exact checkA_1_12
      | 13, _ => exact checkA_1_13
      | 14, _ => exact checkA_1_14
      | 15, _ => exact checkA_1_15
      | _ + 16, h => omega
    | 2, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_2_0
      | 1, _ => exact checkA_2_1
      | 2, _ => exact checkA_2_2
      | 3, _ => exact checkA_2_3
      | 4, _ => exact checkA_2_4
      | 5, _ => exact checkA_2_5
      | 6, _ => exact checkA_2_6
      | 7, _ => exact checkA_2_7
      | 8, _ => exact checkA_2_8
      | 9, _ => exact checkA_2_9
      | 10, _ => exact checkA_2_10
      | 11, _ => exact checkA_2_11
      | 12, _ => exact checkA_2_12
      | 13, _ => exact checkA_2_13
      | 14, _ => exact checkA_2_14
      | 15, _ => exact checkA_2_15
      | _ + 16, h => omega
    | 3, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_3_0
      | 1, _ => exact checkA_3_1
      | 2, _ => exact checkA_3_2
      | 3, _ => exact checkA_3_3
      | 4, _ => exact checkA_3_4
      | 5, _ => exact checkA_3_5
      | 6, _ => exact checkA_3_6
      | 7, _ => exact checkA_3_7
      | 8, _ => exact checkA_3_8
      | 9, _ => exact checkA_3_9
      | 10, _ => exact checkA_3_10
      | 11, _ => exact checkA_3_11
      | 12, _ => exact checkA_3_12
      | 13, _ => exact checkA_3_13
      | 14, _ => exact checkA_3_14
      | 15, _ => exact checkA_3_15
      | _ + 16, h => omega
    | 4, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_4_0
      | 1, _ => exact checkA_4_1
      | 2, _ => exact checkA_4_2
      | 3, _ => exact checkA_4_3
      | 4, _ => exact checkA_4_4
      | 5, _ => exact checkA_4_5
      | 6, _ => exact checkA_4_6
      | 7, _ => exact checkA_4_7
      | 8, _ => exact checkA_4_8
      | 9, _ => exact checkA_4_9
      | 10, _ => exact checkA_4_10
      | 11, _ => exact checkA_4_11
      | 12, _ => exact checkA_4_12
      | 13, _ => exact checkA_4_13
      | 14, _ => exact checkA_4_14
      | 15, _ => exact checkA_4_15
      | _ + 16, h => omega
    | 5, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_5_0
      | 1, _ => exact checkA_5_1
      | 2, _ => exact checkA_5_2
      | 3, _ => exact checkA_5_3
      | 4, _ => exact checkA_5_4
      | 5, _ => exact checkA_5_5
      | 6, _ => exact checkA_5_6
      | 7, _ => exact checkA_5_7
      | 8, _ => exact checkA_5_8
      | 9, _ => exact checkA_5_9
      | 10, _ => exact checkA_5_10
      | 11, _ => exact checkA_5_11
      | 12, _ => exact checkA_5_12
      | 13, _ => exact checkA_5_13
      | 14, _ => exact checkA_5_14
      | 15, _ => exact checkA_5_15
      | _ + 16, h => omega
    | 6, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_6_0
      | 1, _ => exact checkA_6_1
      | 2, _ => exact checkA_6_2
      | 3, _ => exact checkA_6_3
      | 4, _ => exact checkA_6_4
      | 5, _ => exact checkA_6_5
      | 6, _ => exact checkA_6_6
      | 7, _ => exact checkA_6_7
      | 8, _ => exact checkA_6_8
      | 9, _ => exact checkA_6_9
      | 10, _ => exact checkA_6_10
      | 11, _ => exact checkA_6_11
      | 12, _ => exact checkA_6_12
      | 13, _ => exact checkA_6_13
      | 14, _ => exact checkA_6_14
      | 15, _ => exact checkA_6_15
      | _ + 16, h => omega
    | 7, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_7_0
      | 1, _ => exact checkA_7_1
      | 2, _ => exact checkA_7_2
      | 3, _ => exact checkA_7_3
      | 4, _ => exact checkA_7_4
      | 5, _ => exact checkA_7_5
      | 6, _ => exact checkA_7_6
      | 7, _ => exact checkA_7_7
      | 8, _ => exact checkA_7_8
      | 9, _ => exact checkA_7_9
      | 10, _ => exact checkA_7_10
      | 11, _ => exact checkA_7_11
      | 12, _ => exact checkA_7_12
      | 13, _ => exact checkA_7_13
      | 14, _ => exact checkA_7_14
      | 15, _ => exact checkA_7_15
      | _ + 16, h => omega
    | 8, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_8_0
      | 1, _ => exact checkA_8_1
      | 2, _ => exact checkA_8_2
      | 3, _ => exact checkA_8_3
      | 4, _ => exact checkA_8_4
      | 5, _ => exact checkA_8_5
      | 6, _ => exact checkA_8_6
      | 7, _ => exact checkA_8_7
      | 8, _ => exact checkA_8_8
      | 9, _ => exact checkA_8_9
      | 10, _ => exact checkA_8_10
      | 11, _ => exact checkA_8_11
      | 12, _ => exact checkA_8_12
      | 13, _ => exact checkA_8_13
      | 14, _ => exact checkA_8_14
      | 15, _ => exact checkA_8_15
      | _ + 16, h => omega
    | 9, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_9_0
      | 1, _ => exact checkA_9_1
      | 2, _ => exact checkA_9_2
      | 3, _ => exact checkA_9_3
      | 4, _ => exact checkA_9_4
      | 5, _ => exact checkA_9_5
      | 6, _ => exact checkA_9_6
      | 7, _ => exact checkA_9_7
      | 8, _ => exact checkA_9_8
      | 9, _ => exact checkA_9_9
      | 10, _ => exact checkA_9_10
      | 11, _ => exact checkA_9_11
      | 12, _ => exact checkA_9_12
      | 13, _ => exact checkA_9_13
      | 14, _ => exact checkA_9_14
      | 15, _ => exact checkA_9_15
      | _ + 16, h => omega
    | 10, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_10_0
      | 1, _ => exact checkA_10_1
      | 2, _ => exact checkA_10_2
      | 3, _ => exact checkA_10_3
      | 4, _ => exact checkA_10_4
      | 5, _ => exact checkA_10_5
      | 6, _ => exact checkA_10_6
      | 7, _ => exact checkA_10_7
      | 8, _ => exact checkA_10_8
      | 9, _ => exact checkA_10_9
      | 10, _ => exact checkA_10_10
      | 11, _ => exact checkA_10_11
      | 12, _ => exact checkA_10_12
      | 13, _ => exact checkA_10_13
      | 14, _ => exact checkA_10_14
      | 15, _ => exact checkA_10_15
      | _ + 16, h => omega
    | 11, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_11_0
      | 1, _ => exact checkA_11_1
      | 2, _ => exact checkA_11_2
      | 3, _ => exact checkA_11_3
      | 4, _ => exact checkA_11_4
      | 5, _ => exact checkA_11_5
      | 6, _ => exact checkA_11_6
      | 7, _ => exact checkA_11_7
      | 8, _ => exact checkA_11_8
      | 9, _ => exact checkA_11_9
      | 10, _ => exact checkA_11_10
      | 11, _ => exact checkA_11_11
      | 12, _ => exact checkA_11_12
      | 13, _ => exact checkA_11_13
      | 14, _ => exact checkA_11_14
      | 15, _ => exact checkA_11_15
      | _ + 16, h => omega
    | 12, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_12_0
      | 1, _ => exact checkA_12_1
      | 2, _ => exact checkA_12_2
      | 3, _ => exact checkA_12_3
      | 4, _ => exact checkA_12_4
      | 5, _ => exact checkA_12_5
      | 6, _ => exact checkA_12_6
      | 7, _ => exact checkA_12_7
      | 8, _ => exact checkA_12_8
      | 9, _ => exact checkA_12_9
      | 10, _ => exact checkA_12_10
      | 11, _ => exact checkA_12_11
      | 12, _ => exact checkA_12_12
      | 13, _ => exact checkA_12_13
      | 14, _ => exact checkA_12_14
      | 15, _ => exact checkA_12_15
      | _ + 16, h => omega
    | 13, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_13_0
      | 1, _ => exact checkA_13_1
      | 2, _ => exact checkA_13_2
      | 3, _ => exact checkA_13_3
      | 4, _ => exact checkA_13_4
      | 5, _ => exact checkA_13_5
      | 6, _ => exact checkA_13_6
      | 7, _ => exact checkA_13_7
      | 8, _ => exact checkA_13_8
      | 9, _ => exact checkA_13_9
      | 10, _ => exact checkA_13_10
      | 11, _ => exact checkA_13_11
      | 12, _ => exact checkA_13_12
      | 13, _ => exact checkA_13_13
      | 14, _ => exact checkA_13_14
      | 15, _ => exact checkA_13_15
      | _ + 16, h => omega
    | 14, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_14_0
      | 1, _ => exact checkA_14_1
      | 2, _ => exact checkA_14_2
      | 3, _ => exact checkA_14_3
      | 4, _ => exact checkA_14_4
      | 5, _ => exact checkA_14_5
      | 6, _ => exact checkA_14_6
      | 7, _ => exact checkA_14_7
      | 8, _ => exact checkA_14_8
      | 9, _ => exact checkA_14_9
      | 10, _ => exact checkA_14_10
      | 11, _ => exact checkA_14_11
      | 12, _ => exact checkA_14_12
      | 13, _ => exact checkA_14_13
      | 14, _ => exact checkA_14_14
      | 15, _ => exact checkA_14_15
      | _ + 16, h => omega
    | 15, _ =>
      match j3, hj3 with
      | 0, _ => exact checkA_15_0
      | 1, _ => exact checkA_15_1
      | 2, _ => exact checkA_15_2
      | 3, _ => exact checkA_15_3
      | 4, _ => exact checkA_15_4
      | 5, _ => exact checkA_15_5
      | 6, _ => exact checkA_15_6
      | 7, _ => exact checkA_15_7
      | 8, _ => exact checkA_15_8
      | 9, _ => exact checkA_15_9
      | 10, _ => exact checkA_15_10
      | 11, _ => exact checkA_15_11
      | 12, _ => exact checkA_15_12
      | 13, _ => exact checkA_15_13
      | 14, _ => exact checkA_15_14
      | 15, _ => exact checkA_15_15
      | _ + 16, h => omega
    | _ + 16, h => omega
  · intro k1 hk1 j3 hj3
    match k1, hk1 with
    | 0, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_0_0
      | 1, _ => exact checkB_0_1
      | 2, _ => exact checkB_0_2
      | 3, _ => exact checkB_0_3
      | 4, _ => exact checkB_0_4
      | 5, _ => exact checkB_0_5
      | 6, _ => exact checkB_0_6
      | 7, _ => exact checkB_0_7
      | 8, _ => exact checkB_0_8
      | 9, _ => exact checkB_0_9
      | 10, _ => exact checkB_0_10
      | 11, _ => exact checkB_0_11
      | 12, _ => exact checkB_0_12
      | 13, _ => exact checkB_0_13
      | 14, _ => exact checkB_0_14
      | 15, _ => exact checkB_0_15
      | _ + 16, h => omega
    | 1, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_1_0
      | 1, _ => exact checkB_1_1
      | 2, _ => exact checkB_1_2
      | 3, _ => exact checkB_1_3
      | 4, _ => exact checkB_1_4
      | 5, _ => exact checkB_1_5
      | 6, _ => exact checkB_1_6
      | 7, _ => exact checkB_1_7
      | 8, _ => exact checkB_1_8
      | 9, _ => exact checkB_1_9
      | 10, _ => exact checkB_1_10
      | 11, _ => exact checkB_1_11
      | 12, _ => exact checkB_1_12
      | 13, _ => exact checkB_1_13
      | 14, _ => exact checkB_1_14
      | 15, _ => exact checkB_1_15
      | _ + 16, h => omega
    | 2, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_2_0
      | 1, _ => exact checkB_2_1
      | 2, _ => exact checkB_2_2
      | 3, _ => exact checkB_2_3
      | 4, _ => exact checkB_2_4
      | 5, _ => exact checkB_2_5
      | 6, _ => exact checkB_2_6
      | 7, _ => exact checkB_2_7
      | 8, _ => exact checkB_2_8
      | 9, _ => exact checkB_2_9
      | 10, _ => exact checkB_2_10
      | 11, _ => exact checkB_2_11
      | 12, _ => exact checkB_2_12
      | 13, _ => exact checkB_2_13
      | 14, _ => exact checkB_2_14
      | 15, _ => exact checkB_2_15
      | _ + 16, h => omega
    | 3, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_3_0
      | 1, _ => exact checkB_3_1
      | 2, _ => exact checkB_3_2
      | 3, _ => exact checkB_3_3
      | 4, _ => exact checkB_3_4
      | 5, _ => exact checkB_3_5
      | 6, _ => exact checkB_3_6
      | 7, _ => exact checkB_3_7
      | 8, _ => exact checkB_3_8
      | 9, _ => exact checkB_3_9
      | 10, _ => exact checkB_3_10
      | 11, _ => exact checkB_3_11
      | 12, _ => exact checkB_3_12
      | 13, _ => exact checkB_3_13
      | 14, _ => exact checkB_3_14
      | 15, _ => exact checkB_3_15
      | _ + 16, h => omega
    | 4, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_4_0
      | 1, _ => exact checkB_4_1
      | 2, _ => exact checkB_4_2
      | 3, _ => exact checkB_4_3
      | 4, _ => exact checkB_4_4
      | 5, _ => exact checkB_4_5
      | 6, _ => exact checkB_4_6
      | 7, _ => exact checkB_4_7
      | 8, _ => exact checkB_4_8
      | 9, _ => exact checkB_4_9
      | 10, _ => exact checkB_4_10
      | 11, _ => exact checkB_4_11
      | 12, _ => exact checkB_4_12
      | 13, _ => exact checkB_4_13
      | 14, _ => exact checkB_4_14
      | 15, _ => exact checkB_4_15
      | _ + 16, h => omega
    | 5, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_5_0
      | 1, _ => exact checkB_5_1
      | 2, _ => exact checkB_5_2
      | 3, _ => exact checkB_5_3
      | 4, _ => exact checkB_5_4
      | 5, _ => exact checkB_5_5
      | 6, _ => exact checkB_5_6
      | 7, _ => exact checkB_5_7
      | 8, _ => exact checkB_5_8
      | 9, _ => exact checkB_5_9
      | 10, _ => exact checkB_5_10
      | 11, _ => exact checkB_5_11
      | 12, _ => exact checkB_5_12
      | 13, _ => exact checkB_5_13
      | 14, _ => exact checkB_5_14
      | 15, _ => exact checkB_5_15
      | _ + 16, h => omega
    | 6, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_6_0
      | 1, _ => exact checkB_6_1
      | 2, _ => exact checkB_6_2
      | 3, _ => exact checkB_6_3
      | 4, _ => exact checkB_6_4
      | 5, _ => exact checkB_6_5
      | 6, _ => exact checkB_6_6
      | 7, _ => exact checkB_6_7
      | 8, _ => exact checkB_6_8
      | 9, _ => exact checkB_6_9
      | 10, _ => exact checkB_6_10
      | 11, _ => exact checkB_6_11
      | 12, _ => exact checkB_6_12
      | 13, _ => exact checkB_6_13
      | 14, _ => exact checkB_6_14
      | 15, _ => exact checkB_6_15
      | _ + 16, h => omega
    | 7, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_7_0
      | 1, _ => exact checkB_7_1
      | 2, _ => exact checkB_7_2
      | 3, _ => exact checkB_7_3
      | 4, _ => exact checkB_7_4
      | 5, _ => exact checkB_7_5
      | 6, _ => exact checkB_7_6
      | 7, _ => exact checkB_7_7
      | 8, _ => exact checkB_7_8
      | 9, _ => exact checkB_7_9
      | 10, _ => exact checkB_7_10
      | 11, _ => exact checkB_7_11
      | 12, _ => exact checkB_7_12
      | 13, _ => exact checkB_7_13
      | 14, _ => exact checkB_7_14
      | 15, _ => exact checkB_7_15
      | _ + 16, h => omega
    | 8, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_8_0
      | 1, _ => exact checkB_8_1
      | 2, _ => exact checkB_8_2
      | 3, _ => exact checkB_8_3
      | 4, _ => exact checkB_8_4
      | 5, _ => exact checkB_8_5
      | 6, _ => exact checkB_8_6
      | 7, _ => exact checkB_8_7
      | 8, _ => exact checkB_8_8
      | 9, _ => exact checkB_8_9
      | 10, _ => exact checkB_8_10
      | 11, _ => exact checkB_8_11
      | 12, _ => exact checkB_8_12
      | 13, _ => exact checkB_8_13
      | 14, _ => exact checkB_8_14
      | 15, _ => exact checkB_8_15
      | _ + 16, h => omega
    | 9, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_9_0
      | 1, _ => exact checkB_9_1
      | 2, _ => exact checkB_9_2
      | 3, _ => exact checkB_9_3
      | 4, _ => exact checkB_9_4
      | 5, _ => exact checkB_9_5
      | 6, _ => exact checkB_9_6
      | 7, _ => exact checkB_9_7
      | 8, _ => exact checkB_9_8
      | 9, _ => exact checkB_9_9
      | 10, _ => exact checkB_9_10
      | 11, _ => exact checkB_9_11
      | 12, _ => exact checkB_9_12
      | 13, _ => exact checkB_9_13
      | 14, _ => exact checkB_9_14
      | 15, _ => exact checkB_9_15
      | _ + 16, h => omega
    | 10, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_10_0
      | 1, _ => exact checkB_10_1
      | 2, _ => exact checkB_10_2
      | 3, _ => exact checkB_10_3
      | 4, _ => exact checkB_10_4
      | 5, _ => exact checkB_10_5
      | 6, _ => exact checkB_10_6
      | 7, _ => exact checkB_10_7
      | 8, _ => exact checkB_10_8
      | 9, _ => exact checkB_10_9
      | 10, _ => exact checkB_10_10
      | 11, _ => exact checkB_10_11
      | 12, _ => exact checkB_10_12
      | 13, _ => exact checkB_10_13
      | 14, _ => exact checkB_10_14
      | 15, _ => exact checkB_10_15
      | _ + 16, h => omega
    | 11, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_11_0
      | 1, _ => exact checkB_11_1
      | 2, _ => exact checkB_11_2
      | 3, _ => exact checkB_11_3
      | 4, _ => exact checkB_11_4
      | 5, _ => exact checkB_11_5
      | 6, _ => exact checkB_11_6
      | 7, _ => exact checkB_11_7
      | 8, _ => exact checkB_11_8
      | 9, _ => exact checkB_11_9
      | 10, _ => exact checkB_11_10
      | 11, _ => exact checkB_11_11
      | 12, _ => exact checkB_11_12
      | 13, _ => exact checkB_11_13
      | 14, _ => exact checkB_11_14
      | 15, _ => exact checkB_11_15
      | _ + 16, h => omega
    | 12, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_12_0
      | 1, _ => exact checkB_12_1
      | 2, _ => exact checkB_12_2
      | 3, _ => exact checkB_12_3
      | 4, _ => exact checkB_12_4
      | 5, _ => exact checkB_12_5
      | 6, _ => exact checkB_12_6
      | 7, _ => exact checkB_12_7
      | 8, _ => exact checkB_12_8
      | 9, _ => exact checkB_12_9
      | 10, _ => exact checkB_12_10
      | 11, _ => exact checkB_12_11
      | 12, _ => exact checkB_12_12
      | 13, _ => exact checkB_12_13
      | 14, _ => exact checkB_12_14
      | 15, _ => exact checkB_12_15
      | _ + 16, h => omega
    | 13, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_13_0
      | 1, _ => exact checkB_13_1
      | 2, _ => exact checkB_13_2
      | 3, _ => exact checkB_13_3
      | 4, _ => exact checkB_13_4
      | 5, _ => exact checkB_13_5
      | 6, _ => exact checkB_13_6
      | 7, _ => exact checkB_13_7
      | 8, _ => exact checkB_13_8
      | 9, _ => exact checkB_13_9
      | 10, _ => exact checkB_13_10
      | 11, _ => exact checkB_13_11
      | 12, _ => exact checkB_13_12
      | 13, _ => exact checkB_13_13
      | 14, _ => exact checkB_13_14
      | 15, _ => exact checkB_13_15
      | _ + 16, h => omega
    | 14, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_14_0
      | 1, _ => exact checkB_14_1
      | 2, _ => exact checkB_14_2
      | 3, _ => exact checkB_14_3
      | 4, _ => exact checkB_14_4
      | 5, _ => exact checkB_14_5
      | 6, _ => exact checkB_14_6
      | 7, _ => exact checkB_14_7
      | 8, _ => exact checkB_14_8
      | 9, _ => exact checkB_14_9
      | 10, _ => exact checkB_14_10
      | 11, _ => exact checkB_14_11
      | 12, _ => exact checkB_14_12
      | 13, _ => exact checkB_14_13
      | 14, _ => exact checkB_14_14
      | 15, _ => exact checkB_14_15
      | _ + 16, h => omega
    | 15, _ =>
      match j3, hj3 with
      | 0, _ => exact checkB_15_0
      | 1, _ => exact checkB_15_1
      | 2, _ => exact checkB_15_2
      | 3, _ => exact checkB_15_3
      | 4, _ => exact checkB_15_4
      | 5, _ => exact checkB_15_5
      | 6, _ => exact checkB_15_6
      | 7, _ => exact checkB_15_7
      | 8, _ => exact checkB_15_8
      | 9, _ => exact checkB_15_9
      | 10, _ => exact checkB_15_10
      | 11, _ => exact checkB_15_11
      | 12, _ => exact checkB_15_12
      | 13, _ => exact checkB_15_13
      | 14, _ => exact checkB_15_14
      | 15, _ => exact checkB_15_15
      | _ + 16, h => omega
    | _ + 16, h => omega
  · intro k1 hk1 k2 hk2
    match k1, hk1 with
    | 0, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_0_0
      | 1, _ => exact checkC_0_1
      | 2, _ => exact checkC_0_2
      | 3, _ => exact checkC_0_3
      | 4, _ => exact checkC_0_4
      | 5, _ => exact checkC_0_5
      | 6, _ => exact checkC_0_6
      | 7, _ => exact checkC_0_7
      | 8, _ => exact checkC_0_8
      | 9, _ => exact checkC_0_9
      | 10, _ => exact checkC_0_10
      | 11, _ => exact checkC_0_11
      | 12, _ => exact checkC_0_12
      | 13, _ => exact checkC_0_13
      | 14, _ => exact checkC_0_14
      | 15, _ => exact checkC_0_15
      | _ + 16, h => omega
    | 1, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_1_0
      | 1, _ => exact checkC_1_1
      | 2, _ => exact checkC_1_2
      | 3, _ => exact checkC_1_3
      | 4, _ => exact checkC_1_4
      | 5, _ => exact checkC_1_5
      | 6, _ => exact checkC_1_6
      | 7, _ => exact checkC_1_7
      | 8, _ => exact checkC_1_8
      | 9, _ => exact checkC_1_9
      | 10, _ => exact checkC_1_10
      | 11, _ => exact checkC_1_11
      | 12, _ => exact checkC_1_12
      | 13, _ => exact checkC_1_13
      | 14, _ => exact checkC_1_14
      | 15, _ => exact checkC_1_15
      | _ + 16, h => omega
    | 2, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_2_0
      | 1, _ => exact checkC_2_1
      | 2, _ => exact checkC_2_2
      | 3, _ => exact checkC_2_3
      | 4, _ => exact checkC_2_4
      | 5, _ => exact checkC_2_5
      | 6, _ => exact checkC_2_6
      | 7, _ => exact checkC_2_7
      | 8, _ => exact checkC_2_8
      | 9, _ => exact checkC_2_9
      | 10, _ => exact checkC_2_10
      | 11, _ => exact checkC_2_11
      | 12, _ => exact checkC_2_12
      | 13, _ => exact checkC_2_13
      | 14, _ => exact checkC_2_14
      | 15, _ => exact checkC_2_15
      | _ + 16, h => omega
    | 3, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_3_0
      | 1, _ => exact checkC_3_1
      | 2, _ => exact checkC_3_2
      | 3, _ => exact checkC_3_3
      | 4, _ => exact checkC_3_4
      | 5, _ => exact checkC_3_5
      | 6, _ => exact checkC_3_6
      | 7, _ => exact checkC_3_7
      | 8, _ => exact checkC_3_8
      | 9, _ => exact checkC_3_9
      | 10, _ => exact checkC_3_10
      | 11, _ => exact checkC_3_11
      | 12, _ => exact checkC_3_12
      | 13, _ => exact checkC_3_13
      | 14, _ => exact checkC_3_14
      | 15, _ => exact checkC_3_15
      | _ + 16, h => omega
    | 4, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_4_0
      | 1, _ => exact checkC_4_1
      | 2, _ => exact checkC_4_2
      | 3, _ => exact checkC_4_3
      | 4, _ => exact checkC_4_4
      | 5, _ => exact checkC_4_5
      | 6, _ => exact checkC_4_6
      | 7, _ => exact checkC_4_7
      | 8, _ => exact checkC_4_8
      | 9, _ => exact checkC_4_9
      | 10, _ => exact checkC_4_10
      | 11, _ => exact checkC_4_11
      | 12, _ => exact checkC_4_12
      | 13, _ => exact checkC_4_13
      | 14, _ => exact checkC_4_14
      | 15, _ => exact checkC_4_15
      | _ + 16, h => omega
    | 5, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_5_0
      | 1, _ => exact checkC_5_1
      | 2, _ => exact checkC_5_2
      | 3, _ => exact checkC_5_3
      | 4, _ => exact checkC_5_4
      | 5, _ => exact checkC_5_5
      | 6, _ => exact checkC_5_6
      | 7, _ => exact checkC_5_7
      | 8, _ => exact checkC_5_8
      | 9, _ => exact checkC_5_9
      | 10, _ => exact checkC_5_10
      | 11, _ => exact checkC_5_11
      | 12, _ => exact checkC_5_12
      | 13, _ => exact checkC_5_13
      | 14, _ => exact checkC_5_14
      | 15, _ => exact checkC_5_15
      | _ + 16, h => omega
    | 6, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_6_0
      | 1, _ => exact checkC_6_1
      | 2, _ => exact checkC_6_2
      | 3, _ => exact checkC_6_3
      | 4, _ => exact checkC_6_4
      | 5, _ => exact checkC_6_5
      | 6, _ => exact checkC_6_6
      | 7, _ => exact checkC_6_7
      | 8, _ => exact checkC_6_8
      | 9, _ => exact checkC_6_9
      | 10, _ => exact checkC_6_10
      | 11, _ => exact checkC_6_11
      | 12, _ => exact checkC_6_12
      | 13, _ => exact checkC_6_13
      | 14, _ => exact checkC_6_14
      | 15, _ => exact checkC_6_15
      | _ + 16, h => omega
    | 7, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_7_0
      | 1, _ => exact checkC_7_1
      | 2, _ => exact checkC_7_2
      | 3, _ => exact checkC_7_3
      | 4, _ => exact checkC_7_4
      | 5, _ => exact checkC_7_5
      | 6, _ => exact checkC_7_6
      | 7, _ => exact checkC_7_7
      | 8, _ => exact checkC_7_8
      | 9, _ => exact checkC_7_9
      | 10, _ => exact checkC_7_10
      | 11, _ => exact checkC_7_11
      | 12, _ => exact checkC_7_12
      | 13, _ => exact checkC_7_13
      | 14, _ => exact checkC_7_14
      | 15, _ => exact checkC_7_15
      | _ + 16, h => omega
    | 8, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_8_0
      | 1, _ => exact checkC_8_1
      | 2, _ => exact checkC_8_2
      | 3, _ => exact checkC_8_3
      | 4, _ => exact checkC_8_4
      | 5, _ => exact checkC_8_5
      | 6, _ => exact checkC_8_6
      | 7, _ => exact checkC_8_7
      | 8, _ => exact checkC_8_8
      | 9, _ => exact checkC_8_9
      | 10, _ => exact checkC_8_10
      | 11, _ => exact checkC_8_11
      | 12, _ => exact checkC_8_12
      | 13, _ => exact checkC_8_13
      | 14, _ => exact checkC_8_14
      | 15, _ => exact checkC_8_15
      | _ + 16, h => omega
    | 9, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_9_0
      | 1, _ => exact checkC_9_1
      | 2, _ => exact checkC_9_2
      | 3, _ => exact checkC_9_3
      | 4, _ => exact checkC_9_4
      | 5, _ => exact checkC_9_5
      | 6, _ => exact checkC_9_6
      | 7, _ => exact checkC_9_7
      | 8, _ => exact checkC_9_8
      | 9, _ => exact checkC_9_9
      | 10, _ => exact checkC_9_10
      | 11, _ => exact checkC_9_11
      | 12, _ => exact checkC_9_12
      | 13, _ => exact checkC_9_13
      | 14, _ => exact checkC_9_14
      | 15, _ => exact checkC_9_15
      | _ + 16, h => omega
    | 10, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_10_0
      | 1, _ => exact checkC_10_1
      | 2, _ => exact checkC_10_2
      | 3, _ => exact checkC_10_3
      | 4, _ => exact checkC_10_4
      | 5, _ => exact checkC_10_5
      | 6, _ => exact checkC_10_6
      | 7, _ => exact checkC_10_7
      | 8, _ => exact checkC_10_8
      | 9, _ => exact checkC_10_9
      | 10, _ => exact checkC_10_10
      | 11, _ => exact checkC_10_11
      | 12, _ => exact checkC_10_12
      | 13, _ => exact checkC_10_13
      | 14, _ => exact checkC_10_14
      | 15, _ => exact checkC_10_15
      | _ + 16, h => omega
    | 11, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_11_0
      | 1, _ => exact checkC_11_1
      | 2, _ => exact checkC_11_2
      | 3, _ => exact checkC_11_3
      | 4, _ => exact checkC_11_4
      | 5, _ => exact checkC_11_5
      | 6, _ => exact checkC_11_6
      | 7, _ => exact checkC_11_7
      | 8, _ => exact checkC_11_8
      | 9, _ => exact checkC_11_9
      | 10, _ => exact checkC_11_10
      | 11, _ => exact checkC_11_11
      | 12, _ => exact checkC_11_12
      | 13, _ => exact checkC_11_13
      | 14, _ => exact checkC_11_14
      | 15, _ => exact checkC_11_15
      | _ + 16, h => omega
    | 12, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_12_0
      | 1, _ => exact checkC_12_1
      | 2, _ => exact checkC_12_2
      | 3, _ => exact checkC_12_3
      | 4, _ => exact checkC_12_4
      | 5, _ => exact checkC_12_5
      | 6, _ => exact checkC_12_6
      | 7, _ => exact checkC_12_7
      | 8, _ => exact checkC_12_8
      | 9, _ => exact checkC_12_9
      | 10, _ => exact checkC_12_10
      | 11, _ => exact checkC_12_11
      | 12, _ => exact checkC_12_12
      | 13, _ => exact checkC_12_13
      | 14, _ => exact checkC_12_14
      | 15, _ => exact checkC_12_15
      | _ + 16, h => omega
    | 13, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_13_0
      | 1, _ => exact checkC_13_1
      | 2, _ => exact checkC_13_2
      | 3, _ => exact checkC_13_3
      | 4, _ => exact checkC_13_4
      | 5, _ => exact checkC_13_5
      | 6, _ => exact checkC_13_6
      | 7, _ => exact checkC_13_7
      | 8, _ => exact checkC_13_8
      | 9, _ => exact checkC_13_9
      | 10, _ => exact checkC_13_10
      | 11, _ => exact checkC_13_11
      | 12, _ => exact checkC_13_12
      | 13, _ => exact checkC_13_13
      | 14, _ => exact checkC_13_14
      | 15, _ => exact checkC_13_15
      | _ + 16, h => omega
    | 14, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_14_0
      | 1, _ => exact checkC_14_1
      | 2, _ => exact checkC_14_2
      | 3, _ => exact checkC_14_3
      | 4, _ => exact checkC_14_4
      | 5, _ => exact checkC_14_5
      | 6, _ => exact checkC_14_6
      | 7, _ => exact checkC_14_7
      | 8, _ => exact checkC_14_8
      | 9, _ => exact checkC_14_9
      | 10, _ => exact checkC_14_10
      | 11, _ => exact checkC_14_11
      | 12, _ => exact checkC_14_12
      | 13, _ => exact checkC_14_13
      | 14, _ => exact checkC_14_14
      | 15, _ => exact checkC_14_15
      | _ + 16, h => omega
    | 15, _ =>
      match k2, hk2 with
      | 0, _ => exact checkC_15_0
      | 1, _ => exact checkC_15_1
      | 2, _ => exact checkC_15_2
      | 3, _ => exact checkC_15_3
      | 4, _ => exact checkC_15_4
      | 5, _ => exact checkC_15_5
      | 6, _ => exact checkC_15_6
      | 7, _ => exact checkC_15_7
      | 8, _ => exact checkC_15_8
      | 9, _ => exact checkC_15_9
      | 10, _ => exact checkC_15_10
      | 11, _ => exact checkC_15_11
      | 12, _ => exact checkC_15_12
      | 13, _ => exact checkC_15_13
      | 14, _ => exact checkC_15_14
      | 15, _ => exact checkC_15_15
      | _ + 16, h => omega
    | _ + 16, h => omega

/-- If the embedded setup decodes, it is well formed at each `τ` that its monomial points fit.

The condition on `τ` is that the monomial points represent its powers. -/
theorem TrustedSetup.ofHex_wellFormed {s : TrustedSetup} {τ : Fr}
    (h : TrustedSetup.ofHex = .ok s)
    (hg1 : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Represents s.g1Monomial[i] (τ ^ i.val))
    (hg2 : ∀ i : Fin KZG_SETUP_G2_LENGTH, G2.Represents s.g2Monomial[i] (τ ^ i.val)) :
    s.WellFormed τ :=
  TrustedSetup.WellFormed.of_lagrangeOfMonomial (TrustedSetup.ofHex_valid h)
    (TrustedSetup.ofHex_lagrangeOfMonomial h) hg1 hg2

end EthLib.Cryptography.Kzg
