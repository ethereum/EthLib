module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded monomial points 1024 to 2047 of the embedded setup

Each theorem checks in the kernel that 16 monomial strings encode their table entries.

Decompression of such a string gives its entry, so the kernel computes no square root.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeM_64 :
    decodeCheck tableM 1024
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1024).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1024 16]
  decide +kernel

theorem decodeM_65 :
    decodeCheck tableM 1040
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1040).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1040 16]
  decide +kernel

theorem decodeM_66 :
    decodeCheck tableM 1056
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1056).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1056 16]
  decide +kernel

theorem decodeM_67 :
    decodeCheck tableM 1072
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1072).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1072 16]
  decide +kernel

theorem decodeM_68 :
    decodeCheck tableM 1088
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1088).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1088 16]
  decide +kernel

theorem decodeM_69 :
    decodeCheck tableM 1104
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1104).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1104 16]
  decide +kernel

theorem decodeM_70 :
    decodeCheck tableM 1120
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1120).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1120 16]
  decide +kernel

theorem decodeM_71 :
    decodeCheck tableM 1136
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1136).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1136 16]
  decide +kernel

theorem decodeM_72 :
    decodeCheck tableM 1152
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1152).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1152 16]
  decide +kernel

theorem decodeM_73 :
    decodeCheck tableM 1168
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1168).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1168 16]
  decide +kernel

theorem decodeM_74 :
    decodeCheck tableM 1184
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1184).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1184 16]
  decide +kernel

theorem decodeM_75 :
    decodeCheck tableM 1200
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1200).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1200 16]
  decide +kernel

theorem decodeM_76 :
    decodeCheck tableM 1216
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1216).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1216 16]
  decide +kernel

theorem decodeM_77 :
    decodeCheck tableM 1232
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1232).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1232 16]
  decide +kernel

theorem decodeM_78 :
    decodeCheck tableM 1248
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1248).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1248 16]
  decide +kernel

theorem decodeM_79 :
    decodeCheck tableM 1264
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1264).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1264 16]
  decide +kernel

theorem decodeM_80 :
    decodeCheck tableM 1280
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1280).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1280 16]
  decide +kernel

theorem decodeM_81 :
    decodeCheck tableM 1296
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1296).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1296 16]
  decide +kernel

theorem decodeM_82 :
    decodeCheck tableM 1312
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1312).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1312 16]
  decide +kernel

theorem decodeM_83 :
    decodeCheck tableM 1328
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1328).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1328 16]
  decide +kernel

theorem decodeM_84 :
    decodeCheck tableM 1344
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1344).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1344 16]
  decide +kernel

theorem decodeM_85 :
    decodeCheck tableM 1360
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1360).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1360 16]
  decide +kernel

theorem decodeM_86 :
    decodeCheck tableM 1376
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1376).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1376 16]
  decide +kernel

theorem decodeM_87 :
    decodeCheck tableM 1392
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1392).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1392 16]
  decide +kernel

theorem decodeM_88 :
    decodeCheck tableM 1408
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1408).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1408 16]
  decide +kernel

theorem decodeM_89 :
    decodeCheck tableM 1424
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1424).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1424 16]
  decide +kernel

theorem decodeM_90 :
    decodeCheck tableM 1440
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1440).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1440 16]
  decide +kernel

theorem decodeM_91 :
    decodeCheck tableM 1456
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1456).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1456 16]
  decide +kernel

theorem decodeM_92 :
    decodeCheck tableM 1472
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1472).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1472 16]
  decide +kernel

theorem decodeM_93 :
    decodeCheck tableM 1488
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1488).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1488 16]
  decide +kernel

theorem decodeM_94 :
    decodeCheck tableM 1504
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1504).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1504 16]
  decide +kernel

theorem decodeM_95 :
    decodeCheck tableM 1520
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1520).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1520 16]
  decide +kernel

theorem decodeM_96 :
    decodeCheck tableM 1536
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1536).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1536 16]
  decide +kernel

theorem decodeM_97 :
    decodeCheck tableM 1552
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1552).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1552 16]
  decide +kernel

theorem decodeM_98 :
    decodeCheck tableM 1568
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1568).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1568 16]
  decide +kernel

theorem decodeM_99 :
    decodeCheck tableM 1584
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1584).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1584 16]
  decide +kernel

theorem decodeM_100 :
    decodeCheck tableM 1600
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1600).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1600 16]
  decide +kernel

theorem decodeM_101 :
    decodeCheck tableM 1616
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1616).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1616 16]
  decide +kernel

theorem decodeM_102 :
    decodeCheck tableM 1632
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1632).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1632 16]
  decide +kernel

theorem decodeM_103 :
    decodeCheck tableM 1648
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1648).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1648 16]
  decide +kernel

theorem decodeM_104 :
    decodeCheck tableM 1664
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1664).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1664 16]
  decide +kernel

theorem decodeM_105 :
    decodeCheck tableM 1680
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1680).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1680 16]
  decide +kernel

theorem decodeM_106 :
    decodeCheck tableM 1696
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1696).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1696 16]
  decide +kernel

theorem decodeM_107 :
    decodeCheck tableM 1712
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1712).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1712 16]
  decide +kernel

theorem decodeM_108 :
    decodeCheck tableM 1728
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1728).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1728 16]
  decide +kernel

theorem decodeM_109 :
    decodeCheck tableM 1744
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1744).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1744 16]
  decide +kernel

theorem decodeM_110 :
    decodeCheck tableM 1760
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1760).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1760 16]
  decide +kernel

theorem decodeM_111 :
    decodeCheck tableM 1776
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1776).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1776 16]
  decide +kernel

theorem decodeM_112 :
    decodeCheck tableM 1792
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1792).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1792 16]
  decide +kernel

theorem decodeM_113 :
    decodeCheck tableM 1808
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1808).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1808 16]
  decide +kernel

theorem decodeM_114 :
    decodeCheck tableM 1824
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1824).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1824 16]
  decide +kernel

theorem decodeM_115 :
    decodeCheck tableM 1840
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1840).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1840 16]
  decide +kernel

theorem decodeM_116 :
    decodeCheck tableM 1856
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1856).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1856 16]
  decide +kernel

theorem decodeM_117 :
    decodeCheck tableM 1872
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1872).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1872 16]
  decide +kernel

theorem decodeM_118 :
    decodeCheck tableM 1888
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1888).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1888 16]
  decide +kernel

theorem decodeM_119 :
    decodeCheck tableM 1904
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1904).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1904 16]
  decide +kernel

theorem decodeM_120 :
    decodeCheck tableM 1920
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1920).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1920 16]
  decide +kernel

theorem decodeM_121 :
    decodeCheck tableM 1936
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1936).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1936 16]
  decide +kernel

theorem decodeM_122 :
    decodeCheck tableM 1952
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1952).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1952 16]
  decide +kernel

theorem decodeM_123 :
    decodeCheck tableM 1968
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1968).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1968 16]
  decide +kernel

theorem decodeM_124 :
    decodeCheck tableM 1984
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1984).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1984 16]
  decide +kernel

theorem decodeM_125 :
    decodeCheck tableM 2000
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2000).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2000 16]
  decide +kernel

theorem decodeM_126 :
    decodeCheck tableM 2016
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2016).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2016 16]
  decide +kernel

theorem decodeM_127 :
    decodeCheck tableM 2032
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2032).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2032 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
