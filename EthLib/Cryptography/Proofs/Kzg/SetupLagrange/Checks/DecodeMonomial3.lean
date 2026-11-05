module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded monomial points 3072 to 4095 of the embedded setup

Each theorem decodes 16 monomial strings in the kernel.

It compares each decoded point with its table entry.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeM_192 :
    decodeCheck tableM 3072
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3072).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3072 16]
  decide +kernel

theorem decodeM_193 :
    decodeCheck tableM 3088
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3088).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3088 16]
  decide +kernel

theorem decodeM_194 :
    decodeCheck tableM 3104
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3104).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3104 16]
  decide +kernel

theorem decodeM_195 :
    decodeCheck tableM 3120
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3120).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3120 16]
  decide +kernel

theorem decodeM_196 :
    decodeCheck tableM 3136
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3136).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3136 16]
  decide +kernel

theorem decodeM_197 :
    decodeCheck tableM 3152
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3152).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3152 16]
  decide +kernel

theorem decodeM_198 :
    decodeCheck tableM 3168
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3168).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3168 16]
  decide +kernel

theorem decodeM_199 :
    decodeCheck tableM 3184
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3184).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3184 16]
  decide +kernel

theorem decodeM_200 :
    decodeCheck tableM 3200
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3200).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3200 16]
  decide +kernel

theorem decodeM_201 :
    decodeCheck tableM 3216
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3216).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3216 16]
  decide +kernel

theorem decodeM_202 :
    decodeCheck tableM 3232
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3232).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3232 16]
  decide +kernel

theorem decodeM_203 :
    decodeCheck tableM 3248
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3248).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3248 16]
  decide +kernel

theorem decodeM_204 :
    decodeCheck tableM 3264
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3264).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3264 16]
  decide +kernel

theorem decodeM_205 :
    decodeCheck tableM 3280
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3280).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3280 16]
  decide +kernel

theorem decodeM_206 :
    decodeCheck tableM 3296
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3296).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3296 16]
  decide +kernel

theorem decodeM_207 :
    decodeCheck tableM 3312
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3312).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3312 16]
  decide +kernel

theorem decodeM_208 :
    decodeCheck tableM 3328
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3328).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3328 16]
  decide +kernel

theorem decodeM_209 :
    decodeCheck tableM 3344
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3344).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3344 16]
  decide +kernel

theorem decodeM_210 :
    decodeCheck tableM 3360
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3360).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3360 16]
  decide +kernel

theorem decodeM_211 :
    decodeCheck tableM 3376
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3376).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3376 16]
  decide +kernel

theorem decodeM_212 :
    decodeCheck tableM 3392
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3392).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3392 16]
  decide +kernel

theorem decodeM_213 :
    decodeCheck tableM 3408
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3408).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3408 16]
  decide +kernel

theorem decodeM_214 :
    decodeCheck tableM 3424
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3424).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3424 16]
  decide +kernel

theorem decodeM_215 :
    decodeCheck tableM 3440
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3440).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3440 16]
  decide +kernel

theorem decodeM_216 :
    decodeCheck tableM 3456
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3456).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3456 16]
  decide +kernel

theorem decodeM_217 :
    decodeCheck tableM 3472
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3472).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3472 16]
  decide +kernel

theorem decodeM_218 :
    decodeCheck tableM 3488
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3488).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3488 16]
  decide +kernel

theorem decodeM_219 :
    decodeCheck tableM 3504
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3504).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3504 16]
  decide +kernel

theorem decodeM_220 :
    decodeCheck tableM 3520
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3520).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3520 16]
  decide +kernel

theorem decodeM_221 :
    decodeCheck tableM 3536
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3536).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3536 16]
  decide +kernel

theorem decodeM_222 :
    decodeCheck tableM 3552
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3552).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3552 16]
  decide +kernel

theorem decodeM_223 :
    decodeCheck tableM 3568
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3568).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3568 16]
  decide +kernel

theorem decodeM_224 :
    decodeCheck tableM 3584
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3584).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3584 16]
  decide +kernel

theorem decodeM_225 :
    decodeCheck tableM 3600
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3600).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3600 16]
  decide +kernel

theorem decodeM_226 :
    decodeCheck tableM 3616
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3616).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3616 16]
  decide +kernel

theorem decodeM_227 :
    decodeCheck tableM 3632
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3632).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3632 16]
  decide +kernel

theorem decodeM_228 :
    decodeCheck tableM 3648
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3648).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3648 16]
  decide +kernel

theorem decodeM_229 :
    decodeCheck tableM 3664
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3664).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3664 16]
  decide +kernel

theorem decodeM_230 :
    decodeCheck tableM 3680
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3680).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3680 16]
  decide +kernel

theorem decodeM_231 :
    decodeCheck tableM 3696
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3696).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3696 16]
  decide +kernel

theorem decodeM_232 :
    decodeCheck tableM 3712
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3712).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3712 16]
  decide +kernel

theorem decodeM_233 :
    decodeCheck tableM 3728
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3728).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3728 16]
  decide +kernel

theorem decodeM_234 :
    decodeCheck tableM 3744
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3744).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3744 16]
  decide +kernel

theorem decodeM_235 :
    decodeCheck tableM 3760
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3760).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3760 16]
  decide +kernel

theorem decodeM_236 :
    decodeCheck tableM 3776
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3776).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3776 16]
  decide +kernel

theorem decodeM_237 :
    decodeCheck tableM 3792
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3792).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3792 16]
  decide +kernel

theorem decodeM_238 :
    decodeCheck tableM 3808
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3808).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3808 16]
  decide +kernel

theorem decodeM_239 :
    decodeCheck tableM 3824
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3824).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3824 16]
  decide +kernel

theorem decodeM_240 :
    decodeCheck tableM 3840
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3840).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3840 16]
  decide +kernel

theorem decodeM_241 :
    decodeCheck tableM 3856
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3856).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3856 16]
  decide +kernel

theorem decodeM_242 :
    decodeCheck tableM 3872
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3872).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3872 16]
  decide +kernel

theorem decodeM_243 :
    decodeCheck tableM 3888
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3888).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3888 16]
  decide +kernel

theorem decodeM_244 :
    decodeCheck tableM 3904
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3904).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3904 16]
  decide +kernel

theorem decodeM_245 :
    decodeCheck tableM 3920
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3920).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3920 16]
  decide +kernel

theorem decodeM_246 :
    decodeCheck tableM 3936
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3936).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3936 16]
  decide +kernel

theorem decodeM_247 :
    decodeCheck tableM 3952
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3952).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3952 16]
  decide +kernel

theorem decodeM_248 :
    decodeCheck tableM 3968
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3968).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3968 16]
  decide +kernel

theorem decodeM_249 :
    decodeCheck tableM 3984
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3984).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3984 16]
  decide +kernel

theorem decodeM_250 :
    decodeCheck tableM 4000
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4000).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4000 16]
  decide +kernel

theorem decodeM_251 :
    decodeCheck tableM 4016
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4016).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4016 16]
  decide +kernel

theorem decodeM_252 :
    decodeCheck tableM 4032
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4032).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4032 16]
  decide +kernel

theorem decodeM_253 :
    decodeCheck tableM 4048
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4048).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4048 16]
  decide +kernel

theorem decodeM_254 :
    decodeCheck tableM 4064
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4064).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4064 16]
  decide +kernel

theorem decodeM_255 :
    decodeCheck tableM 4080
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4080).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4080 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
