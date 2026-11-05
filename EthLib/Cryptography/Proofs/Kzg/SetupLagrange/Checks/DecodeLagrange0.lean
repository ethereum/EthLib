module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded Lagrange points 0 to 1023 of the embedded setup

Each theorem decodes 16 Lagrange strings in the kernel.

It compares each decoded point with its table entry.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeL_0 :
    decodeCheck tableL 0
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 0).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 0 16]
  decide +kernel

theorem decodeL_1 :
    decodeCheck tableL 16
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 16).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 16 16]
  decide +kernel

theorem decodeL_2 :
    decodeCheck tableL 32
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 32).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 32 16]
  decide +kernel

theorem decodeL_3 :
    decodeCheck tableL 48
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 48).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 48 16]
  decide +kernel

theorem decodeL_4 :
    decodeCheck tableL 64
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 64).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 64 16]
  decide +kernel

theorem decodeL_5 :
    decodeCheck tableL 80
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 80).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 80 16]
  decide +kernel

theorem decodeL_6 :
    decodeCheck tableL 96
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 96).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 96 16]
  decide +kernel

theorem decodeL_7 :
    decodeCheck tableL 112
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 112).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 112 16]
  decide +kernel

theorem decodeL_8 :
    decodeCheck tableL 128
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 128).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 128 16]
  decide +kernel

theorem decodeL_9 :
    decodeCheck tableL 144
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 144).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 144 16]
  decide +kernel

theorem decodeL_10 :
    decodeCheck tableL 160
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 160).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 160 16]
  decide +kernel

theorem decodeL_11 :
    decodeCheck tableL 176
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 176).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 176 16]
  decide +kernel

theorem decodeL_12 :
    decodeCheck tableL 192
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 192).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 192 16]
  decide +kernel

theorem decodeL_13 :
    decodeCheck tableL 208
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 208).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 208 16]
  decide +kernel

theorem decodeL_14 :
    decodeCheck tableL 224
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 224).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 224 16]
  decide +kernel

theorem decodeL_15 :
    decodeCheck tableL 240
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 240).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 240 16]
  decide +kernel

theorem decodeL_16 :
    decodeCheck tableL 256
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 256).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 256 16]
  decide +kernel

theorem decodeL_17 :
    decodeCheck tableL 272
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 272).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 272 16]
  decide +kernel

theorem decodeL_18 :
    decodeCheck tableL 288
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 288).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 288 16]
  decide +kernel

theorem decodeL_19 :
    decodeCheck tableL 304
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 304).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 304 16]
  decide +kernel

theorem decodeL_20 :
    decodeCheck tableL 320
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 320).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 320 16]
  decide +kernel

theorem decodeL_21 :
    decodeCheck tableL 336
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 336).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 336 16]
  decide +kernel

theorem decodeL_22 :
    decodeCheck tableL 352
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 352).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 352 16]
  decide +kernel

theorem decodeL_23 :
    decodeCheck tableL 368
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 368).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 368 16]
  decide +kernel

theorem decodeL_24 :
    decodeCheck tableL 384
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 384).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 384 16]
  decide +kernel

theorem decodeL_25 :
    decodeCheck tableL 400
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 400).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 400 16]
  decide +kernel

theorem decodeL_26 :
    decodeCheck tableL 416
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 416).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 416 16]
  decide +kernel

theorem decodeL_27 :
    decodeCheck tableL 432
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 432).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 432 16]
  decide +kernel

theorem decodeL_28 :
    decodeCheck tableL 448
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 448).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 448 16]
  decide +kernel

theorem decodeL_29 :
    decodeCheck tableL 464
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 464).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 464 16]
  decide +kernel

theorem decodeL_30 :
    decodeCheck tableL 480
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 480).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 480 16]
  decide +kernel

theorem decodeL_31 :
    decodeCheck tableL 496
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 496).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 496 16]
  decide +kernel

theorem decodeL_32 :
    decodeCheck tableL 512
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 512).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 512 16]
  decide +kernel

theorem decodeL_33 :
    decodeCheck tableL 528
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 528).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 528 16]
  decide +kernel

theorem decodeL_34 :
    decodeCheck tableL 544
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 544).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 544 16]
  decide +kernel

theorem decodeL_35 :
    decodeCheck tableL 560
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 560).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 560 16]
  decide +kernel

theorem decodeL_36 :
    decodeCheck tableL 576
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 576).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 576 16]
  decide +kernel

theorem decodeL_37 :
    decodeCheck tableL 592
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 592).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 592 16]
  decide +kernel

theorem decodeL_38 :
    decodeCheck tableL 608
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 608).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 608 16]
  decide +kernel

theorem decodeL_39 :
    decodeCheck tableL 624
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 624).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 624 16]
  decide +kernel

theorem decodeL_40 :
    decodeCheck tableL 640
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 640).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 640 16]
  decide +kernel

theorem decodeL_41 :
    decodeCheck tableL 656
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 656).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 656 16]
  decide +kernel

theorem decodeL_42 :
    decodeCheck tableL 672
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 672).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 672 16]
  decide +kernel

theorem decodeL_43 :
    decodeCheck tableL 688
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 688).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 688 16]
  decide +kernel

theorem decodeL_44 :
    decodeCheck tableL 704
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 704).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 704 16]
  decide +kernel

theorem decodeL_45 :
    decodeCheck tableL 720
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 720).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 720 16]
  decide +kernel

theorem decodeL_46 :
    decodeCheck tableL 736
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 736).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 736 16]
  decide +kernel

theorem decodeL_47 :
    decodeCheck tableL 752
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 752).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 752 16]
  decide +kernel

theorem decodeL_48 :
    decodeCheck tableL 768
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 768).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 768 16]
  decide +kernel

theorem decodeL_49 :
    decodeCheck tableL 784
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 784).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 784 16]
  decide +kernel

theorem decodeL_50 :
    decodeCheck tableL 800
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 800).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 800 16]
  decide +kernel

theorem decodeL_51 :
    decodeCheck tableL 816
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 816).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 816 16]
  decide +kernel

theorem decodeL_52 :
    decodeCheck tableL 832
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 832).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 832 16]
  decide +kernel

theorem decodeL_53 :
    decodeCheck tableL 848
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 848).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 848 16]
  decide +kernel

theorem decodeL_54 :
    decodeCheck tableL 864
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 864).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 864 16]
  decide +kernel

theorem decodeL_55 :
    decodeCheck tableL 880
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 880).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 880 16]
  decide +kernel

theorem decodeL_56 :
    decodeCheck tableL 896
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 896).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 896 16]
  decide +kernel

theorem decodeL_57 :
    decodeCheck tableL 912
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 912).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 912 16]
  decide +kernel

theorem decodeL_58 :
    decodeCheck tableL 928
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 928).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 928 16]
  decide +kernel

theorem decodeL_59 :
    decodeCheck tableL 944
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 944).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 944 16]
  decide +kernel

theorem decodeL_60 :
    decodeCheck tableL 960
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 960).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 960 16]
  decide +kernel

theorem decodeL_61 :
    decodeCheck tableL 976
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 976).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 976 16]
  decide +kernel

theorem decodeL_62 :
    decodeCheck tableL 992
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 992).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 992 16]
  decide +kernel

theorem decodeL_63 :
    decodeCheck tableL 1008
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1008).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1008 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
