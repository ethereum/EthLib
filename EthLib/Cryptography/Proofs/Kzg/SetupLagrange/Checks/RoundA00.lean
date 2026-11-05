module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 0`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_0_0 : checkA tableM tableA 0 0 = true := by
  decide +kernel

theorem checkA_0_1 : checkA tableM tableA 0 1 = true := by
  decide +kernel

theorem checkA_0_2 : checkA tableM tableA 0 2 = true := by
  decide +kernel

theorem checkA_0_3 : checkA tableM tableA 0 3 = true := by
  decide +kernel

theorem checkA_0_4 : checkA tableM tableA 0 4 = true := by
  decide +kernel

theorem checkA_0_5 : checkA tableM tableA 0 5 = true := by
  decide +kernel

theorem checkA_0_6 : checkA tableM tableA 0 6 = true := by
  decide +kernel

theorem checkA_0_7 : checkA tableM tableA 0 7 = true := by
  decide +kernel

theorem checkA_0_8 : checkA tableM tableA 0 8 = true := by
  decide +kernel

theorem checkA_0_9 : checkA tableM tableA 0 9 = true := by
  decide +kernel

theorem checkA_0_10 : checkA tableM tableA 0 10 = true := by
  decide +kernel

theorem checkA_0_11 : checkA tableM tableA 0 11 = true := by
  decide +kernel

theorem checkA_0_12 : checkA tableM tableA 0 12 = true := by
  decide +kernel

theorem checkA_0_13 : checkA tableM tableA 0 13 = true := by
  decide +kernel

theorem checkA_0_14 : checkA tableM tableA 0 14 = true := by
  decide +kernel

theorem checkA_0_15 : checkA tableM tableA 0 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
