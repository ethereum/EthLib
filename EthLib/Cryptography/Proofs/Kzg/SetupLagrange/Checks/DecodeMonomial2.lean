module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the decoded monomial points 2048 to 3071 of the embedded setup

Each theorem decodes 16 monomial strings in the kernel.

It compares each decoded point with its table entry.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open SetupTorsion (codes)

theorem decodeM_128 :
    decodeCheck tableM 2048
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2048).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2048 16]
  decide +kernel

theorem decodeM_129 :
    decodeCheck tableM 2064
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2064).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2064 16]
  decide +kernel

theorem decodeM_130 :
    decodeCheck tableM 2080
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2080).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2080 16]
  decide +kernel

theorem decodeM_131 :
    decodeCheck tableM 2096
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2096).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2096 16]
  decide +kernel

theorem decodeM_132 :
    decodeCheck tableM 2112
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2112).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2112 16]
  decide +kernel

theorem decodeM_133 :
    decodeCheck tableM 2128
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2128).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2128 16]
  decide +kernel

theorem decodeM_134 :
    decodeCheck tableM 2144
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2144).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2144 16]
  decide +kernel

theorem decodeM_135 :
    decodeCheck tableM 2160
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2160).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2160 16]
  decide +kernel

theorem decodeM_136 :
    decodeCheck tableM 2176
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2176).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2176 16]
  decide +kernel

theorem decodeM_137 :
    decodeCheck tableM 2192
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2192).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2192 16]
  decide +kernel

theorem decodeM_138 :
    decodeCheck tableM 2208
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2208).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2208 16]
  decide +kernel

theorem decodeM_139 :
    decodeCheck tableM 2224
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2224).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2224 16]
  decide +kernel

theorem decodeM_140 :
    decodeCheck tableM 2240
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2240).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2240 16]
  decide +kernel

theorem decodeM_141 :
    decodeCheck tableM 2256
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2256).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2256 16]
  decide +kernel

theorem decodeM_142 :
    decodeCheck tableM 2272
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2272).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2272 16]
  decide +kernel

theorem decodeM_143 :
    decodeCheck tableM 2288
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2288).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2288 16]
  decide +kernel

theorem decodeM_144 :
    decodeCheck tableM 2304
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2304).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2304 16]
  decide +kernel

theorem decodeM_145 :
    decodeCheck tableM 2320
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2320).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2320 16]
  decide +kernel

theorem decodeM_146 :
    decodeCheck tableM 2336
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2336).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2336 16]
  decide +kernel

theorem decodeM_147 :
    decodeCheck tableM 2352
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2352).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2352 16]
  decide +kernel

theorem decodeM_148 :
    decodeCheck tableM 2368
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2368).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2368 16]
  decide +kernel

theorem decodeM_149 :
    decodeCheck tableM 2384
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2384).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2384 16]
  decide +kernel

theorem decodeM_150 :
    decodeCheck tableM 2400
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2400).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2400 16]
  decide +kernel

theorem decodeM_151 :
    decodeCheck tableM 2416
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2416).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2416 16]
  decide +kernel

theorem decodeM_152 :
    decodeCheck tableM 2432
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2432).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2432 16]
  decide +kernel

theorem decodeM_153 :
    decodeCheck tableM 2448
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2448).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2448 16]
  decide +kernel

theorem decodeM_154 :
    decodeCheck tableM 2464
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2464).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2464 16]
  decide +kernel

theorem decodeM_155 :
    decodeCheck tableM 2480
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2480).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2480 16]
  decide +kernel

theorem decodeM_156 :
    decodeCheck tableM 2496
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2496).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2496 16]
  decide +kernel

theorem decodeM_157 :
    decodeCheck tableM 2512
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2512).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2512 16]
  decide +kernel

theorem decodeM_158 :
    decodeCheck tableM 2528
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2528).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2528 16]
  decide +kernel

theorem decodeM_159 :
    decodeCheck tableM 2544
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2544).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2544 16]
  decide +kernel

theorem decodeM_160 :
    decodeCheck tableM 2560
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2560).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2560 16]
  decide +kernel

theorem decodeM_161 :
    decodeCheck tableM 2576
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2576).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2576 16]
  decide +kernel

theorem decodeM_162 :
    decodeCheck tableM 2592
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2592).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2592 16]
  decide +kernel

theorem decodeM_163 :
    decodeCheck tableM 2608
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2608).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2608 16]
  decide +kernel

theorem decodeM_164 :
    decodeCheck tableM 2624
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2624).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2624 16]
  decide +kernel

theorem decodeM_165 :
    decodeCheck tableM 2640
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2640).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2640 16]
  decide +kernel

theorem decodeM_166 :
    decodeCheck tableM 2656
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2656).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2656 16]
  decide +kernel

theorem decodeM_167 :
    decodeCheck tableM 2672
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2672).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2672 16]
  decide +kernel

theorem decodeM_168 :
    decodeCheck tableM 2688
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2688).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2688 16]
  decide +kernel

theorem decodeM_169 :
    decodeCheck tableM 2704
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2704).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2704 16]
  decide +kernel

theorem decodeM_170 :
    decodeCheck tableM 2720
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2720).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2720 16]
  decide +kernel

theorem decodeM_171 :
    decodeCheck tableM 2736
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2736).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2736 16]
  decide +kernel

theorem decodeM_172 :
    decodeCheck tableM 2752
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2752).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2752 16]
  decide +kernel

theorem decodeM_173 :
    decodeCheck tableM 2768
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2768).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2768 16]
  decide +kernel

theorem decodeM_174 :
    decodeCheck tableM 2784
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2784).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2784 16]
  decide +kernel

theorem decodeM_175 :
    decodeCheck tableM 2800
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2800).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2800 16]
  decide +kernel

theorem decodeM_176 :
    decodeCheck tableM 2816
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2816).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2816 16]
  decide +kernel

theorem decodeM_177 :
    decodeCheck tableM 2832
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2832).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2832 16]
  decide +kernel

theorem decodeM_178 :
    decodeCheck tableM 2848
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2848).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2848 16]
  decide +kernel

theorem decodeM_179 :
    decodeCheck tableM 2864
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2864).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2864 16]
  decide +kernel

theorem decodeM_180 :
    decodeCheck tableM 2880
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2880).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2880 16]
  decide +kernel

theorem decodeM_181 :
    decodeCheck tableM 2896
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2896).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2896 16]
  decide +kernel

theorem decodeM_182 :
    decodeCheck tableM 2912
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2912).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2912 16]
  decide +kernel

theorem decodeM_183 :
    decodeCheck tableM 2928
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2928).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2928 16]
  decide +kernel

theorem decodeM_184 :
    decodeCheck tableM 2944
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2944).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2944 16]
  decide +kernel

theorem decodeM_185 :
    decodeCheck tableM 2960
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2960).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2960 16]
  decide +kernel

theorem decodeM_186 :
    decodeCheck tableM 2976
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2976).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2976 16]
  decide +kernel

theorem decodeM_187 :
    decodeCheck tableM 2992
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2992).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2992 16]
  decide +kernel

theorem decodeM_188 :
    decodeCheck tableM 3008
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3008).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3008 16]
  decide +kernel

theorem decodeM_189 :
    decodeCheck tableM 3024
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3024).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3024 16]
  decide +kernel

theorem decodeM_190 :
    decodeCheck tableM 3040
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3040).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3040 16]
  decide +kernel

theorem decodeM_191 :
    decodeCheck tableM 3056
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3056).take 16) = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3056 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
