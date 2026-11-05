module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 14`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_14_0 : checkA tableM tableA 14 0 = true := by
  decide +kernel

theorem checkA_14_1 : checkA tableM tableA 14 1 = true := by
  decide +kernel

theorem checkA_14_2 : checkA tableM tableA 14 2 = true := by
  decide +kernel

theorem checkA_14_3 : checkA tableM tableA 14 3 = true := by
  decide +kernel

theorem checkA_14_4 : checkA tableM tableA 14 4 = true := by
  decide +kernel

theorem checkA_14_5 : checkA tableM tableA 14 5 = true := by
  decide +kernel

theorem checkA_14_6 : checkA tableM tableA 14 6 = true := by
  decide +kernel

theorem checkA_14_7 : checkA tableM tableA 14 7 = true := by
  decide +kernel

theorem checkA_14_8 : checkA tableM tableA 14 8 = true := by
  decide +kernel

theorem checkA_14_9 : checkA tableM tableA 14 9 = true := by
  decide +kernel

theorem checkA_14_10 : checkA tableM tableA 14 10 = true := by
  decide +kernel

theorem checkA_14_11 : checkA tableM tableA 14 11 = true := by
  decide +kernel

theorem checkA_14_12 : checkA tableM tableA 14 12 = true := by
  decide +kernel

theorem checkA_14_13 : checkA tableM tableA 14 13 = true := by
  decide +kernel

theorem checkA_14_14 : checkA tableM tableA 14 14 = true := by
  decide +kernel

theorem checkA_14_15 : checkA tableM tableA 14 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
