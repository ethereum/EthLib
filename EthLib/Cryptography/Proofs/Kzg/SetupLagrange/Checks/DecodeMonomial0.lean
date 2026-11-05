module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded monomial points 0 to 1023 of the embedded setup

Each theorem decodes 16 monomial strings in the kernel.

It compares each decoded point with its table entry.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeM_0 :
    decodeCheck tableM 0
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 0).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 0 16]
  decide +kernel

theorem decodeM_1 :
    decodeCheck tableM 16
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 16).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 16 16]
  decide +kernel

theorem decodeM_2 :
    decodeCheck tableM 32
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 32).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 32 16]
  decide +kernel

theorem decodeM_3 :
    decodeCheck tableM 48
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 48).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 48 16]
  decide +kernel

theorem decodeM_4 :
    decodeCheck tableM 64
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 64).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 64 16]
  decide +kernel

theorem decodeM_5 :
    decodeCheck tableM 80
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 80).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 80 16]
  decide +kernel

theorem decodeM_6 :
    decodeCheck tableM 96
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 96).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 96 16]
  decide +kernel

theorem decodeM_7 :
    decodeCheck tableM 112
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 112).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 112 16]
  decide +kernel

theorem decodeM_8 :
    decodeCheck tableM 128
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 128).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 128 16]
  decide +kernel

theorem decodeM_9 :
    decodeCheck tableM 144
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 144).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 144 16]
  decide +kernel

theorem decodeM_10 :
    decodeCheck tableM 160
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 160).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 160 16]
  decide +kernel

theorem decodeM_11 :
    decodeCheck tableM 176
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 176).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 176 16]
  decide +kernel

theorem decodeM_12 :
    decodeCheck tableM 192
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 192).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 192 16]
  decide +kernel

theorem decodeM_13 :
    decodeCheck tableM 208
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 208).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 208 16]
  decide +kernel

theorem decodeM_14 :
    decodeCheck tableM 224
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 224).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 224 16]
  decide +kernel

theorem decodeM_15 :
    decodeCheck tableM 240
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 240).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 240 16]
  decide +kernel

theorem decodeM_16 :
    decodeCheck tableM 256
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 256).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 256 16]
  decide +kernel

theorem decodeM_17 :
    decodeCheck tableM 272
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 272).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 272 16]
  decide +kernel

theorem decodeM_18 :
    decodeCheck tableM 288
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 288).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 288 16]
  decide +kernel

theorem decodeM_19 :
    decodeCheck tableM 304
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 304).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 304 16]
  decide +kernel

theorem decodeM_20 :
    decodeCheck tableM 320
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 320).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 320 16]
  decide +kernel

theorem decodeM_21 :
    decodeCheck tableM 336
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 336).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 336 16]
  decide +kernel

theorem decodeM_22 :
    decodeCheck tableM 352
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 352).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 352 16]
  decide +kernel

theorem decodeM_23 :
    decodeCheck tableM 368
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 368).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 368 16]
  decide +kernel

theorem decodeM_24 :
    decodeCheck tableM 384
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 384).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 384 16]
  decide +kernel

theorem decodeM_25 :
    decodeCheck tableM 400
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 400).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 400 16]
  decide +kernel

theorem decodeM_26 :
    decodeCheck tableM 416
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 416).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 416 16]
  decide +kernel

theorem decodeM_27 :
    decodeCheck tableM 432
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 432).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 432 16]
  decide +kernel

theorem decodeM_28 :
    decodeCheck tableM 448
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 448).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 448 16]
  decide +kernel

theorem decodeM_29 :
    decodeCheck tableM 464
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 464).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 464 16]
  decide +kernel

theorem decodeM_30 :
    decodeCheck tableM 480
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 480).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 480 16]
  decide +kernel

theorem decodeM_31 :
    decodeCheck tableM 496
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 496).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 496 16]
  decide +kernel

theorem decodeM_32 :
    decodeCheck tableM 512
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 512).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 512 16]
  decide +kernel

theorem decodeM_33 :
    decodeCheck tableM 528
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 528).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 528 16]
  decide +kernel

theorem decodeM_34 :
    decodeCheck tableM 544
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 544).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 544 16]
  decide +kernel

theorem decodeM_35 :
    decodeCheck tableM 560
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 560).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 560 16]
  decide +kernel

theorem decodeM_36 :
    decodeCheck tableM 576
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 576).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 576 16]
  decide +kernel

theorem decodeM_37 :
    decodeCheck tableM 592
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 592).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 592 16]
  decide +kernel

theorem decodeM_38 :
    decodeCheck tableM 608
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 608).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 608 16]
  decide +kernel

theorem decodeM_39 :
    decodeCheck tableM 624
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 624).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 624 16]
  decide +kernel

theorem decodeM_40 :
    decodeCheck tableM 640
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 640).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 640 16]
  decide +kernel

theorem decodeM_41 :
    decodeCheck tableM 656
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 656).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 656 16]
  decide +kernel

theorem decodeM_42 :
    decodeCheck tableM 672
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 672).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 672 16]
  decide +kernel

theorem decodeM_43 :
    decodeCheck tableM 688
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 688).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 688 16]
  decide +kernel

theorem decodeM_44 :
    decodeCheck tableM 704
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 704).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 704 16]
  decide +kernel

theorem decodeM_45 :
    decodeCheck tableM 720
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 720).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 720 16]
  decide +kernel

theorem decodeM_46 :
    decodeCheck tableM 736
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 736).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 736 16]
  decide +kernel

theorem decodeM_47 :
    decodeCheck tableM 752
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 752).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 752 16]
  decide +kernel

theorem decodeM_48 :
    decodeCheck tableM 768
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 768).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 768 16]
  decide +kernel

theorem decodeM_49 :
    decodeCheck tableM 784
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 784).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 784 16]
  decide +kernel

theorem decodeM_50 :
    decodeCheck tableM 800
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 800).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 800 16]
  decide +kernel

theorem decodeM_51 :
    decodeCheck tableM 816
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 816).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 816 16]
  decide +kernel

theorem decodeM_52 :
    decodeCheck tableM 832
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 832).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 832 16]
  decide +kernel

theorem decodeM_53 :
    decodeCheck tableM 848
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 848).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 848 16]
  decide +kernel

theorem decodeM_54 :
    decodeCheck tableM 864
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 864).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 864 16]
  decide +kernel

theorem decodeM_55 :
    decodeCheck tableM 880
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 880).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 880 16]
  decide +kernel

theorem decodeM_56 :
    decodeCheck tableM 896
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 896).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 896 16]
  decide +kernel

theorem decodeM_57 :
    decodeCheck tableM 912
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 912).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 912 16]
  decide +kernel

theorem decodeM_58 :
    decodeCheck tableM 928
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 928).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 928 16]
  decide +kernel

theorem decodeM_59 :
    decodeCheck tableM 944
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 944).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 944 16]
  decide +kernel

theorem decodeM_60 :
    decodeCheck tableM 960
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 960).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 960 16]
  decide +kernel

theorem decodeM_61 :
    decodeCheck tableM 976
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 976).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 976 16]
  decide +kernel

theorem decodeM_62 :
    decodeCheck tableM 992
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 992).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 992 16]
  decide +kernel

theorem decodeM_63 :
    decodeCheck tableM 1008
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1008).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1008 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
