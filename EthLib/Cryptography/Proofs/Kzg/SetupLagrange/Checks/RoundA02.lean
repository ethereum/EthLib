module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 2`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_2_0 : checkA tableM tableA 2 0 = true := by
  decide +kernel

theorem checkA_2_1 : checkA tableM tableA 2 1 = true := by
  decide +kernel

theorem checkA_2_2 : checkA tableM tableA 2 2 = true := by
  decide +kernel

theorem checkA_2_3 : checkA tableM tableA 2 3 = true := by
  decide +kernel

theorem checkA_2_4 : checkA tableM tableA 2 4 = true := by
  decide +kernel

theorem checkA_2_5 : checkA tableM tableA 2 5 = true := by
  decide +kernel

theorem checkA_2_6 : checkA tableM tableA 2 6 = true := by
  decide +kernel

theorem checkA_2_7 : checkA tableM tableA 2 7 = true := by
  decide +kernel

theorem checkA_2_8 : checkA tableM tableA 2 8 = true := by
  decide +kernel

theorem checkA_2_9 : checkA tableM tableA 2 9 = true := by
  decide +kernel

theorem checkA_2_10 : checkA tableM tableA 2 10 = true := by
  decide +kernel

theorem checkA_2_11 : checkA tableM tableA 2 11 = true := by
  decide +kernel

theorem checkA_2_12 : checkA tableM tableA 2 12 = true := by
  decide +kernel

theorem checkA_2_13 : checkA tableM tableA 2 13 = true := by
  decide +kernel

theorem checkA_2_14 : checkA tableM tableA 2 14 = true := by
  decide +kernel

theorem checkA_2_15 : checkA tableM tableA 2 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
