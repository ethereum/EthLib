module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded Lagrange points 3072 to 4095 of the embedded setup

Each theorem checks in the kernel that 16 Lagrange strings encode their table entries.

Decompression of such a string gives its entry, so the kernel computes no square root.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeL_192 :
    decodeCheck tableL 3072
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3072).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3072 16]
  decide +kernel

theorem decodeL_193 :
    decodeCheck tableL 3088
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3088).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3088 16]
  decide +kernel

theorem decodeL_194 :
    decodeCheck tableL 3104
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3104).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3104 16]
  decide +kernel

theorem decodeL_195 :
    decodeCheck tableL 3120
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3120).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3120 16]
  decide +kernel

theorem decodeL_196 :
    decodeCheck tableL 3136
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3136).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3136 16]
  decide +kernel

theorem decodeL_197 :
    decodeCheck tableL 3152
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3152).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3152 16]
  decide +kernel

theorem decodeL_198 :
    decodeCheck tableL 3168
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3168).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3168 16]
  decide +kernel

theorem decodeL_199 :
    decodeCheck tableL 3184
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3184).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3184 16]
  decide +kernel

theorem decodeL_200 :
    decodeCheck tableL 3200
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3200).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3200 16]
  decide +kernel

theorem decodeL_201 :
    decodeCheck tableL 3216
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3216).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3216 16]
  decide +kernel

theorem decodeL_202 :
    decodeCheck tableL 3232
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3232).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3232 16]
  decide +kernel

theorem decodeL_203 :
    decodeCheck tableL 3248
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3248).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3248 16]
  decide +kernel

theorem decodeL_204 :
    decodeCheck tableL 3264
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3264).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3264 16]
  decide +kernel

theorem decodeL_205 :
    decodeCheck tableL 3280
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3280).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3280 16]
  decide +kernel

theorem decodeL_206 :
    decodeCheck tableL 3296
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3296).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3296 16]
  decide +kernel

theorem decodeL_207 :
    decodeCheck tableL 3312
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3312).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3312 16]
  decide +kernel

theorem decodeL_208 :
    decodeCheck tableL 3328
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3328).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3328 16]
  decide +kernel

theorem decodeL_209 :
    decodeCheck tableL 3344
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3344).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3344 16]
  decide +kernel

theorem decodeL_210 :
    decodeCheck tableL 3360
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3360).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3360 16]
  decide +kernel

theorem decodeL_211 :
    decodeCheck tableL 3376
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3376).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3376 16]
  decide +kernel

theorem decodeL_212 :
    decodeCheck tableL 3392
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3392).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3392 16]
  decide +kernel

theorem decodeL_213 :
    decodeCheck tableL 3408
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3408).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3408 16]
  decide +kernel

theorem decodeL_214 :
    decodeCheck tableL 3424
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3424).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3424 16]
  decide +kernel

theorem decodeL_215 :
    decodeCheck tableL 3440
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3440).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3440 16]
  decide +kernel

theorem decodeL_216 :
    decodeCheck tableL 3456
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3456).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3456 16]
  decide +kernel

theorem decodeL_217 :
    decodeCheck tableL 3472
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3472).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3472 16]
  decide +kernel

theorem decodeL_218 :
    decodeCheck tableL 3488
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3488).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3488 16]
  decide +kernel

theorem decodeL_219 :
    decodeCheck tableL 3504
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3504).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3504 16]
  decide +kernel

theorem decodeL_220 :
    decodeCheck tableL 3520
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3520).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3520 16]
  decide +kernel

theorem decodeL_221 :
    decodeCheck tableL 3536
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3536).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3536 16]
  decide +kernel

theorem decodeL_222 :
    decodeCheck tableL 3552
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3552).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3552 16]
  decide +kernel

theorem decodeL_223 :
    decodeCheck tableL 3568
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3568).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3568 16]
  decide +kernel

theorem decodeL_224 :
    decodeCheck tableL 3584
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3584).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3584 16]
  decide +kernel

theorem decodeL_225 :
    decodeCheck tableL 3600
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3600).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3600 16]
  decide +kernel

theorem decodeL_226 :
    decodeCheck tableL 3616
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3616).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3616 16]
  decide +kernel

theorem decodeL_227 :
    decodeCheck tableL 3632
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3632).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3632 16]
  decide +kernel

theorem decodeL_228 :
    decodeCheck tableL 3648
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3648).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3648 16]
  decide +kernel

theorem decodeL_229 :
    decodeCheck tableL 3664
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3664).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3664 16]
  decide +kernel

theorem decodeL_230 :
    decodeCheck tableL 3680
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3680).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3680 16]
  decide +kernel

theorem decodeL_231 :
    decodeCheck tableL 3696
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3696).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3696 16]
  decide +kernel

theorem decodeL_232 :
    decodeCheck tableL 3712
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3712).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3712 16]
  decide +kernel

theorem decodeL_233 :
    decodeCheck tableL 3728
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3728).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3728 16]
  decide +kernel

theorem decodeL_234 :
    decodeCheck tableL 3744
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3744).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3744 16]
  decide +kernel

theorem decodeL_235 :
    decodeCheck tableL 3760
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3760).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3760 16]
  decide +kernel

theorem decodeL_236 :
    decodeCheck tableL 3776
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3776).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3776 16]
  decide +kernel

theorem decodeL_237 :
    decodeCheck tableL 3792
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3792).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3792 16]
  decide +kernel

theorem decodeL_238 :
    decodeCheck tableL 3808
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3808).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3808 16]
  decide +kernel

theorem decodeL_239 :
    decodeCheck tableL 3824
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3824).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3824 16]
  decide +kernel

theorem decodeL_240 :
    decodeCheck tableL 3840
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3840).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3840 16]
  decide +kernel

theorem decodeL_241 :
    decodeCheck tableL 3856
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3856).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3856 16]
  decide +kernel

theorem decodeL_242 :
    decodeCheck tableL 3872
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3872).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3872 16]
  decide +kernel

theorem decodeL_243 :
    decodeCheck tableL 3888
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3888).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3888 16]
  decide +kernel

theorem decodeL_244 :
    decodeCheck tableL 3904
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3904).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3904 16]
  decide +kernel

theorem decodeL_245 :
    decodeCheck tableL 3920
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3920).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3920 16]
  decide +kernel

theorem decodeL_246 :
    decodeCheck tableL 3936
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3936).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3936 16]
  decide +kernel

theorem decodeL_247 :
    decodeCheck tableL 3952
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3952).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3952 16]
  decide +kernel

theorem decodeL_248 :
    decodeCheck tableL 3968
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3968).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3968 16]
  decide +kernel

theorem decodeL_249 :
    decodeCheck tableL 3984
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3984).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3984 16]
  decide +kernel

theorem decodeL_250 :
    decodeCheck tableL 4000
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 4000).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 4000 16]
  decide +kernel

theorem decodeL_251 :
    decodeCheck tableL 4016
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 4016).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 4016 16]
  decide +kernel

theorem decodeL_252 :
    decodeCheck tableL 4032
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 4032).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 4032 16]
  decide +kernel

theorem decodeL_253 :
    decodeCheck tableL 4048
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 4048).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 4048 16]
  decide +kernel

theorem decodeL_254 :
    decodeCheck tableL 4064
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 4064).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 4064 16]
  decide +kernel

theorem decodeL_255 :
    decodeCheck tableL 4080
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 4080).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 4080 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
