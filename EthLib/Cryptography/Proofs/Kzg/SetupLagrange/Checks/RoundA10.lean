module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 10`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_10_0 : checkA tableM tableA 10 0 = true := by
  decide +kernel

theorem checkA_10_1 : checkA tableM tableA 10 1 = true := by
  decide +kernel

theorem checkA_10_2 : checkA tableM tableA 10 2 = true := by
  decide +kernel

theorem checkA_10_3 : checkA tableM tableA 10 3 = true := by
  decide +kernel

theorem checkA_10_4 : checkA tableM tableA 10 4 = true := by
  decide +kernel

theorem checkA_10_5 : checkA tableM tableA 10 5 = true := by
  decide +kernel

theorem checkA_10_6 : checkA tableM tableA 10 6 = true := by
  decide +kernel

theorem checkA_10_7 : checkA tableM tableA 10 7 = true := by
  decide +kernel

theorem checkA_10_8 : checkA tableM tableA 10 8 = true := by
  decide +kernel

theorem checkA_10_9 : checkA tableM tableA 10 9 = true := by
  decide +kernel

theorem checkA_10_10 : checkA tableM tableA 10 10 = true := by
  decide +kernel

theorem checkA_10_11 : checkA tableM tableA 10 11 = true := by
  decide +kernel

theorem checkA_10_12 : checkA tableM tableA 10 12 = true := by
  decide +kernel

theorem checkA_10_13 : checkA tableM tableA 10 13 = true := by
  decide +kernel

theorem checkA_10_14 : checkA tableM tableA 10 14 = true := by
  decide +kernel

theorem checkA_10_15 : checkA tableM tableA 10 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
