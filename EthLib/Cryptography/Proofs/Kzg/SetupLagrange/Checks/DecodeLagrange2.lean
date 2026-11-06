module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded Lagrange points 2048 to 3071 of the embedded setup

Each theorem checks in the kernel that 16 Lagrange strings encode their table entries.

Decompression of such a string gives its entry, so the kernel computes no square root.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeL_128 :
    decodeCheck tableL 2048
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2048).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2048 16]
  decide +kernel

theorem decodeL_129 :
    decodeCheck tableL 2064
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2064).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2064 16]
  decide +kernel

theorem decodeL_130 :
    decodeCheck tableL 2080
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2080).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2080 16]
  decide +kernel

theorem decodeL_131 :
    decodeCheck tableL 2096
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2096).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2096 16]
  decide +kernel

theorem decodeL_132 :
    decodeCheck tableL 2112
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2112).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2112 16]
  decide +kernel

theorem decodeL_133 :
    decodeCheck tableL 2128
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2128).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2128 16]
  decide +kernel

theorem decodeL_134 :
    decodeCheck tableL 2144
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2144).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2144 16]
  decide +kernel

theorem decodeL_135 :
    decodeCheck tableL 2160
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2160).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2160 16]
  decide +kernel

theorem decodeL_136 :
    decodeCheck tableL 2176
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2176).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2176 16]
  decide +kernel

theorem decodeL_137 :
    decodeCheck tableL 2192
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2192).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2192 16]
  decide +kernel

theorem decodeL_138 :
    decodeCheck tableL 2208
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2208).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2208 16]
  decide +kernel

theorem decodeL_139 :
    decodeCheck tableL 2224
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2224).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2224 16]
  decide +kernel

theorem decodeL_140 :
    decodeCheck tableL 2240
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2240).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2240 16]
  decide +kernel

theorem decodeL_141 :
    decodeCheck tableL 2256
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2256).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2256 16]
  decide +kernel

theorem decodeL_142 :
    decodeCheck tableL 2272
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2272).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2272 16]
  decide +kernel

theorem decodeL_143 :
    decodeCheck tableL 2288
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2288).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2288 16]
  decide +kernel

theorem decodeL_144 :
    decodeCheck tableL 2304
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2304).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2304 16]
  decide +kernel

theorem decodeL_145 :
    decodeCheck tableL 2320
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2320).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2320 16]
  decide +kernel

theorem decodeL_146 :
    decodeCheck tableL 2336
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2336).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2336 16]
  decide +kernel

theorem decodeL_147 :
    decodeCheck tableL 2352
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2352).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2352 16]
  decide +kernel

theorem decodeL_148 :
    decodeCheck tableL 2368
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2368).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2368 16]
  decide +kernel

theorem decodeL_149 :
    decodeCheck tableL 2384
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2384).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2384 16]
  decide +kernel

theorem decodeL_150 :
    decodeCheck tableL 2400
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2400).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2400 16]
  decide +kernel

theorem decodeL_151 :
    decodeCheck tableL 2416
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2416).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2416 16]
  decide +kernel

theorem decodeL_152 :
    decodeCheck tableL 2432
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2432).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2432 16]
  decide +kernel

theorem decodeL_153 :
    decodeCheck tableL 2448
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2448).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2448 16]
  decide +kernel

theorem decodeL_154 :
    decodeCheck tableL 2464
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2464).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2464 16]
  decide +kernel

theorem decodeL_155 :
    decodeCheck tableL 2480
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2480).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2480 16]
  decide +kernel

theorem decodeL_156 :
    decodeCheck tableL 2496
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2496).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2496 16]
  decide +kernel

theorem decodeL_157 :
    decodeCheck tableL 2512
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2512).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2512 16]
  decide +kernel

theorem decodeL_158 :
    decodeCheck tableL 2528
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2528).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2528 16]
  decide +kernel

theorem decodeL_159 :
    decodeCheck tableL 2544
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2544).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2544 16]
  decide +kernel

theorem decodeL_160 :
    decodeCheck tableL 2560
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2560).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2560 16]
  decide +kernel

theorem decodeL_161 :
    decodeCheck tableL 2576
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2576).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2576 16]
  decide +kernel

theorem decodeL_162 :
    decodeCheck tableL 2592
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2592).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2592 16]
  decide +kernel

theorem decodeL_163 :
    decodeCheck tableL 2608
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2608).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2608 16]
  decide +kernel

theorem decodeL_164 :
    decodeCheck tableL 2624
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2624).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2624 16]
  decide +kernel

theorem decodeL_165 :
    decodeCheck tableL 2640
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2640).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2640 16]
  decide +kernel

theorem decodeL_166 :
    decodeCheck tableL 2656
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2656).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2656 16]
  decide +kernel

theorem decodeL_167 :
    decodeCheck tableL 2672
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2672).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2672 16]
  decide +kernel

theorem decodeL_168 :
    decodeCheck tableL 2688
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2688).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2688 16]
  decide +kernel

theorem decodeL_169 :
    decodeCheck tableL 2704
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2704).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2704 16]
  decide +kernel

theorem decodeL_170 :
    decodeCheck tableL 2720
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2720).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2720 16]
  decide +kernel

theorem decodeL_171 :
    decodeCheck tableL 2736
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2736).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2736 16]
  decide +kernel

theorem decodeL_172 :
    decodeCheck tableL 2752
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2752).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2752 16]
  decide +kernel

theorem decodeL_173 :
    decodeCheck tableL 2768
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2768).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2768 16]
  decide +kernel

theorem decodeL_174 :
    decodeCheck tableL 2784
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2784).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2784 16]
  decide +kernel

theorem decodeL_175 :
    decodeCheck tableL 2800
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2800).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2800 16]
  decide +kernel

theorem decodeL_176 :
    decodeCheck tableL 2816
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2816).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2816 16]
  decide +kernel

theorem decodeL_177 :
    decodeCheck tableL 2832
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2832).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2832 16]
  decide +kernel

theorem decodeL_178 :
    decodeCheck tableL 2848
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2848).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2848 16]
  decide +kernel

theorem decodeL_179 :
    decodeCheck tableL 2864
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2864).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2864 16]
  decide +kernel

theorem decodeL_180 :
    decodeCheck tableL 2880
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2880).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2880 16]
  decide +kernel

theorem decodeL_181 :
    decodeCheck tableL 2896
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2896).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2896 16]
  decide +kernel

theorem decodeL_182 :
    decodeCheck tableL 2912
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2912).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2912 16]
  decide +kernel

theorem decodeL_183 :
    decodeCheck tableL 2928
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2928).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2928 16]
  decide +kernel

theorem decodeL_184 :
    decodeCheck tableL 2944
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2944).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2944 16]
  decide +kernel

theorem decodeL_185 :
    decodeCheck tableL 2960
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2960).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2960 16]
  decide +kernel

theorem decodeL_186 :
    decodeCheck tableL 2976
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2976).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2976 16]
  decide +kernel

theorem decodeL_187 :
    decodeCheck tableL 2992
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 2992).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 2992 16]
  decide +kernel

theorem decodeL_188 :
    decodeCheck tableL 3008
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3008).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3008 16]
  decide +kernel

theorem decodeL_189 :
    decodeCheck tableL 3024
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3024).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3024 16]
  decide +kernel

theorem decodeL_190 :
    decodeCheck tableL 3040
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3040).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3040 16]
  decide +kernel

theorem decodeL_191 :
    decodeCheck tableL 3056
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop 3056).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1LagrangeHex 3056 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
