module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 5`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_5_0 : checkA tableM tableA 5 0 = true := by
  decide +kernel

theorem checkA_5_1 : checkA tableM tableA 5 1 = true := by
  decide +kernel

theorem checkA_5_2 : checkA tableM tableA 5 2 = true := by
  decide +kernel

theorem checkA_5_3 : checkA tableM tableA 5 3 = true := by
  decide +kernel

theorem checkA_5_4 : checkA tableM tableA 5 4 = true := by
  decide +kernel

theorem checkA_5_5 : checkA tableM tableA 5 5 = true := by
  decide +kernel

theorem checkA_5_6 : checkA tableM tableA 5 6 = true := by
  decide +kernel

theorem checkA_5_7 : checkA tableM tableA 5 7 = true := by
  decide +kernel

theorem checkA_5_8 : checkA tableM tableA 5 8 = true := by
  decide +kernel

theorem checkA_5_9 : checkA tableM tableA 5 9 = true := by
  decide +kernel

theorem checkA_5_10 : checkA tableM tableA 5 10 = true := by
  decide +kernel

theorem checkA_5_11 : checkA tableM tableA 5 11 = true := by
  decide +kernel

theorem checkA_5_12 : checkA tableM tableA 5 12 = true := by
  decide +kernel

theorem checkA_5_13 : checkA tableM tableA 5 13 = true := by
  decide +kernel

theorem checkA_5_14 : checkA tableM tableA 5 14 = true := by
  decide +kernel

theorem checkA_5_15 : checkA tableM tableA 5 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
