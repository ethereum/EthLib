module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 15`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_15_0 : checkA tableM tableA 15 0 = true := by
  decide +kernel

theorem checkA_15_1 : checkA tableM tableA 15 1 = true := by
  decide +kernel

theorem checkA_15_2 : checkA tableM tableA 15 2 = true := by
  decide +kernel

theorem checkA_15_3 : checkA tableM tableA 15 3 = true := by
  decide +kernel

theorem checkA_15_4 : checkA tableM tableA 15 4 = true := by
  decide +kernel

theorem checkA_15_5 : checkA tableM tableA 15 5 = true := by
  decide +kernel

theorem checkA_15_6 : checkA tableM tableA 15 6 = true := by
  decide +kernel

theorem checkA_15_7 : checkA tableM tableA 15 7 = true := by
  decide +kernel

theorem checkA_15_8 : checkA tableM tableA 15 8 = true := by
  decide +kernel

theorem checkA_15_9 : checkA tableM tableA 15 9 = true := by
  decide +kernel

theorem checkA_15_10 : checkA tableM tableA 15 10 = true := by
  decide +kernel

theorem checkA_15_11 : checkA tableM tableA 15 11 = true := by
  decide +kernel

theorem checkA_15_12 : checkA tableM tableA 15 12 = true := by
  decide +kernel

theorem checkA_15_13 : checkA tableM tableA 15 13 = true := by
  decide +kernel

theorem checkA_15_14 : checkA tableM tableA 15 14 = true := by
  decide +kernel

theorem checkA_15_15 : checkA tableM tableA 15 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
