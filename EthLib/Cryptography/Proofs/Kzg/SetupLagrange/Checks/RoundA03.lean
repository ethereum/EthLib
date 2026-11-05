module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 3`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_3_0 : checkA tableM tableA 3 0 = true := by
  decide +kernel

theorem checkA_3_1 : checkA tableM tableA 3 1 = true := by
  decide +kernel

theorem checkA_3_2 : checkA tableM tableA 3 2 = true := by
  decide +kernel

theorem checkA_3_3 : checkA tableM tableA 3 3 = true := by
  decide +kernel

theorem checkA_3_4 : checkA tableM tableA 3 4 = true := by
  decide +kernel

theorem checkA_3_5 : checkA tableM tableA 3 5 = true := by
  decide +kernel

theorem checkA_3_6 : checkA tableM tableA 3 6 = true := by
  decide +kernel

theorem checkA_3_7 : checkA tableM tableA 3 7 = true := by
  decide +kernel

theorem checkA_3_8 : checkA tableM tableA 3 8 = true := by
  decide +kernel

theorem checkA_3_9 : checkA tableM tableA 3 9 = true := by
  decide +kernel

theorem checkA_3_10 : checkA tableM tableA 3 10 = true := by
  decide +kernel

theorem checkA_3_11 : checkA tableM tableA 3 11 = true := by
  decide +kernel

theorem checkA_3_12 : checkA tableM tableA 3 12 = true := by
  decide +kernel

theorem checkA_3_13 : checkA tableM tableA 3 13 = true := by
  decide +kernel

theorem checkA_3_14 : checkA tableM tableA 3 14 = true := by
  decide +kernel

theorem checkA_3_15 : checkA tableM tableA 3 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
