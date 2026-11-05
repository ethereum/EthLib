module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 9`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_9_0 : checkA tableM tableA 9 0 = true := by
  decide +kernel

theorem checkA_9_1 : checkA tableM tableA 9 1 = true := by
  decide +kernel

theorem checkA_9_2 : checkA tableM tableA 9 2 = true := by
  decide +kernel

theorem checkA_9_3 : checkA tableM tableA 9 3 = true := by
  decide +kernel

theorem checkA_9_4 : checkA tableM tableA 9 4 = true := by
  decide +kernel

theorem checkA_9_5 : checkA tableM tableA 9 5 = true := by
  decide +kernel

theorem checkA_9_6 : checkA tableM tableA 9 6 = true := by
  decide +kernel

theorem checkA_9_7 : checkA tableM tableA 9 7 = true := by
  decide +kernel

theorem checkA_9_8 : checkA tableM tableA 9 8 = true := by
  decide +kernel

theorem checkA_9_9 : checkA tableM tableA 9 9 = true := by
  decide +kernel

theorem checkA_9_10 : checkA tableM tableA 9 10 = true := by
  decide +kernel

theorem checkA_9_11 : checkA tableM tableA 9 11 = true := by
  decide +kernel

theorem checkA_9_12 : checkA tableM tableA 9 12 = true := by
  decide +kernel

theorem checkA_9_13 : checkA tableM tableA 9 13 = true := by
  decide +kernel

theorem checkA_9_14 : checkA tableM tableA 9 14 = true := by
  decide +kernel

theorem checkA_9_15 : checkA tableM tableA 9 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
