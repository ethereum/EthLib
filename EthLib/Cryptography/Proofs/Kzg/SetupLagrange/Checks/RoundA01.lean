module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 1`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_1_0 : checkA tableM tableA 1 0 = true := by
  decide +kernel

theorem checkA_1_1 : checkA tableM tableA 1 1 = true := by
  decide +kernel

theorem checkA_1_2 : checkA tableM tableA 1 2 = true := by
  decide +kernel

theorem checkA_1_3 : checkA tableM tableA 1 3 = true := by
  decide +kernel

theorem checkA_1_4 : checkA tableM tableA 1 4 = true := by
  decide +kernel

theorem checkA_1_5 : checkA tableM tableA 1 5 = true := by
  decide +kernel

theorem checkA_1_6 : checkA tableM tableA 1 6 = true := by
  decide +kernel

theorem checkA_1_7 : checkA tableM tableA 1 7 = true := by
  decide +kernel

theorem checkA_1_8 : checkA tableM tableA 1 8 = true := by
  decide +kernel

theorem checkA_1_9 : checkA tableM tableA 1 9 = true := by
  decide +kernel

theorem checkA_1_10 : checkA tableM tableA 1 10 = true := by
  decide +kernel

theorem checkA_1_11 : checkA tableM tableA 1 11 = true := by
  decide +kernel

theorem checkA_1_12 : checkA tableM tableA 1 12 = true := by
  decide +kernel

theorem checkA_1_13 : checkA tableM tableA 1 13 = true := by
  decide +kernel

theorem checkA_1_14 : checkA tableM tableA 1 14 = true := by
  decide +kernel

theorem checkA_1_15 : checkA tableM tableA 1 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
