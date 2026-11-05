module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 8`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_8_0 : checkA tableM tableA 8 0 = true := by
  decide +kernel

theorem checkA_8_1 : checkA tableM tableA 8 1 = true := by
  decide +kernel

theorem checkA_8_2 : checkA tableM tableA 8 2 = true := by
  decide +kernel

theorem checkA_8_3 : checkA tableM tableA 8 3 = true := by
  decide +kernel

theorem checkA_8_4 : checkA tableM tableA 8 4 = true := by
  decide +kernel

theorem checkA_8_5 : checkA tableM tableA 8 5 = true := by
  decide +kernel

theorem checkA_8_6 : checkA tableM tableA 8 6 = true := by
  decide +kernel

theorem checkA_8_7 : checkA tableM tableA 8 7 = true := by
  decide +kernel

theorem checkA_8_8 : checkA tableM tableA 8 8 = true := by
  decide +kernel

theorem checkA_8_9 : checkA tableM tableA 8 9 = true := by
  decide +kernel

theorem checkA_8_10 : checkA tableM tableA 8 10 = true := by
  decide +kernel

theorem checkA_8_11 : checkA tableM tableA 8 11 = true := by
  decide +kernel

theorem checkA_8_12 : checkA tableM tableA 8 12 = true := by
  decide +kernel

theorem checkA_8_13 : checkA tableM tableA 8 13 = true := by
  decide +kernel

theorem checkA_8_14 : checkA tableM tableA 8 14 = true := by
  decide +kernel

theorem checkA_8_15 : checkA tableM tableA 8 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
