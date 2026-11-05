module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded Lagrange points 1024 to 2047 of the embedded setup

Each theorem checks in the kernel that 16 Lagrange strings encode their table entries.

Decompression of such a string gives its entry, so the kernel computes no square root.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeL_64 :
    decodeCheck tableL 1024
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1024).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1024 16]
  decide +kernel

theorem decodeL_65 :
    decodeCheck tableL 1040
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1040).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1040 16]
  decide +kernel

theorem decodeL_66 :
    decodeCheck tableL 1056
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1056).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1056 16]
  decide +kernel

theorem decodeL_67 :
    decodeCheck tableL 1072
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1072).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1072 16]
  decide +kernel

theorem decodeL_68 :
    decodeCheck tableL 1088
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1088).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1088 16]
  decide +kernel

theorem decodeL_69 :
    decodeCheck tableL 1104
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1104).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1104 16]
  decide +kernel

theorem decodeL_70 :
    decodeCheck tableL 1120
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1120).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1120 16]
  decide +kernel

theorem decodeL_71 :
    decodeCheck tableL 1136
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1136).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1136 16]
  decide +kernel

theorem decodeL_72 :
    decodeCheck tableL 1152
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1152).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1152 16]
  decide +kernel

theorem decodeL_73 :
    decodeCheck tableL 1168
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1168).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1168 16]
  decide +kernel

theorem decodeL_74 :
    decodeCheck tableL 1184
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1184).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1184 16]
  decide +kernel

theorem decodeL_75 :
    decodeCheck tableL 1200
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1200).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1200 16]
  decide +kernel

theorem decodeL_76 :
    decodeCheck tableL 1216
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1216).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1216 16]
  decide +kernel

theorem decodeL_77 :
    decodeCheck tableL 1232
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1232).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1232 16]
  decide +kernel

theorem decodeL_78 :
    decodeCheck tableL 1248
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1248).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1248 16]
  decide +kernel

theorem decodeL_79 :
    decodeCheck tableL 1264
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1264).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1264 16]
  decide +kernel

theorem decodeL_80 :
    decodeCheck tableL 1280
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1280).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1280 16]
  decide +kernel

theorem decodeL_81 :
    decodeCheck tableL 1296
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1296).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1296 16]
  decide +kernel

theorem decodeL_82 :
    decodeCheck tableL 1312
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1312).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1312 16]
  decide +kernel

theorem decodeL_83 :
    decodeCheck tableL 1328
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1328).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1328 16]
  decide +kernel

theorem decodeL_84 :
    decodeCheck tableL 1344
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1344).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1344 16]
  decide +kernel

theorem decodeL_85 :
    decodeCheck tableL 1360
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1360).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1360 16]
  decide +kernel

theorem decodeL_86 :
    decodeCheck tableL 1376
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1376).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1376 16]
  decide +kernel

theorem decodeL_87 :
    decodeCheck tableL 1392
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1392).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1392 16]
  decide +kernel

theorem decodeL_88 :
    decodeCheck tableL 1408
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1408).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1408 16]
  decide +kernel

theorem decodeL_89 :
    decodeCheck tableL 1424
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1424).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1424 16]
  decide +kernel

theorem decodeL_90 :
    decodeCheck tableL 1440
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1440).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1440 16]
  decide +kernel

theorem decodeL_91 :
    decodeCheck tableL 1456
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1456).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1456 16]
  decide +kernel

theorem decodeL_92 :
    decodeCheck tableL 1472
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1472).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1472 16]
  decide +kernel

theorem decodeL_93 :
    decodeCheck tableL 1488
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1488).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1488 16]
  decide +kernel

theorem decodeL_94 :
    decodeCheck tableL 1504
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1504).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1504 16]
  decide +kernel

theorem decodeL_95 :
    decodeCheck tableL 1520
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1520).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1520 16]
  decide +kernel

theorem decodeL_96 :
    decodeCheck tableL 1536
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1536).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1536 16]
  decide +kernel

theorem decodeL_97 :
    decodeCheck tableL 1552
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1552).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1552 16]
  decide +kernel

theorem decodeL_98 :
    decodeCheck tableL 1568
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1568).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1568 16]
  decide +kernel

theorem decodeL_99 :
    decodeCheck tableL 1584
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1584).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1584 16]
  decide +kernel

theorem decodeL_100 :
    decodeCheck tableL 1600
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1600).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1600 16]
  decide +kernel

theorem decodeL_101 :
    decodeCheck tableL 1616
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1616).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1616 16]
  decide +kernel

theorem decodeL_102 :
    decodeCheck tableL 1632
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1632).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1632 16]
  decide +kernel

theorem decodeL_103 :
    decodeCheck tableL 1648
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1648).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1648 16]
  decide +kernel

theorem decodeL_104 :
    decodeCheck tableL 1664
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1664).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1664 16]
  decide +kernel

theorem decodeL_105 :
    decodeCheck tableL 1680
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1680).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1680 16]
  decide +kernel

theorem decodeL_106 :
    decodeCheck tableL 1696
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1696).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1696 16]
  decide +kernel

theorem decodeL_107 :
    decodeCheck tableL 1712
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1712).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1712 16]
  decide +kernel

theorem decodeL_108 :
    decodeCheck tableL 1728
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1728).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1728 16]
  decide +kernel

theorem decodeL_109 :
    decodeCheck tableL 1744
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1744).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1744 16]
  decide +kernel

theorem decodeL_110 :
    decodeCheck tableL 1760
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1760).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1760 16]
  decide +kernel

theorem decodeL_111 :
    decodeCheck tableL 1776
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1776).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1776 16]
  decide +kernel

theorem decodeL_112 :
    decodeCheck tableL 1792
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1792).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1792 16]
  decide +kernel

theorem decodeL_113 :
    decodeCheck tableL 1808
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1808).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1808 16]
  decide +kernel

theorem decodeL_114 :
    decodeCheck tableL 1824
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1824).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1824 16]
  decide +kernel

theorem decodeL_115 :
    decodeCheck tableL 1840
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1840).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1840 16]
  decide +kernel

theorem decodeL_116 :
    decodeCheck tableL 1856
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1856).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1856 16]
  decide +kernel

theorem decodeL_117 :
    decodeCheck tableL 1872
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1872).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1872 16]
  decide +kernel

theorem decodeL_118 :
    decodeCheck tableL 1888
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1888).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1888 16]
  decide +kernel

theorem decodeL_119 :
    decodeCheck tableL 1904
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1904).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1904 16]
  decide +kernel

theorem decodeL_120 :
    decodeCheck tableL 1920
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1920).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1920 16]
  decide +kernel

theorem decodeL_121 :
    decodeCheck tableL 1936
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1936).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1936 16]
  decide +kernel

theorem decodeL_122 :
    decodeCheck tableL 1952
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1952).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1952 16]
  decide +kernel

theorem decodeL_123 :
    decodeCheck tableL 1968
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1968).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1968 16]
  decide +kernel

theorem decodeL_124 :
    decodeCheck tableL 1984
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 1984).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 1984 16]
  decide +kernel

theorem decodeL_125 :
    decodeCheck tableL 2000
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2000).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2000 16]
  decide +kernel

theorem decodeL_126 :
    decodeCheck tableL 2016
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2016).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2016 16]
  decide +kernel

theorem decodeL_127 :
    decodeCheck tableL 2032
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2032).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2032 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
