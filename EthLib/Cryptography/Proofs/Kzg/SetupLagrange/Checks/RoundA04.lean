module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 4`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_4_0 : checkA tableM tableA 4 0 = true := by
  decide +kernel

theorem checkA_4_1 : checkA tableM tableA 4 1 = true := by
  decide +kernel

theorem checkA_4_2 : checkA tableM tableA 4 2 = true := by
  decide +kernel

theorem checkA_4_3 : checkA tableM tableA 4 3 = true := by
  decide +kernel

theorem checkA_4_4 : checkA tableM tableA 4 4 = true := by
  decide +kernel

theorem checkA_4_5 : checkA tableM tableA 4 5 = true := by
  decide +kernel

theorem checkA_4_6 : checkA tableM tableA 4 6 = true := by
  decide +kernel

theorem checkA_4_7 : checkA tableM tableA 4 7 = true := by
  decide +kernel

theorem checkA_4_8 : checkA tableM tableA 4 8 = true := by
  decide +kernel

theorem checkA_4_9 : checkA tableM tableA 4 9 = true := by
  decide +kernel

theorem checkA_4_10 : checkA tableM tableA 4 10 = true := by
  decide +kernel

theorem checkA_4_11 : checkA tableM tableA 4 11 = true := by
  decide +kernel

theorem checkA_4_12 : checkA tableM tableA 4 12 = true := by
  decide +kernel

theorem checkA_4_13 : checkA tableM tableA 4 13 = true := by
  decide +kernel

theorem checkA_4_14 : checkA tableM tableA 4 14 = true := by
  decide +kernel

theorem checkA_4_15 : checkA tableM tableA 4 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
