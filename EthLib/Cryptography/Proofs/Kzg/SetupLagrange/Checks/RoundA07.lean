module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 7`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_7_0 : checkA tableM tableA 7 0 = true := by
  decide +kernel

theorem checkA_7_1 : checkA tableM tableA 7 1 = true := by
  decide +kernel

theorem checkA_7_2 : checkA tableM tableA 7 2 = true := by
  decide +kernel

theorem checkA_7_3 : checkA tableM tableA 7 3 = true := by
  decide +kernel

theorem checkA_7_4 : checkA tableM tableA 7 4 = true := by
  decide +kernel

theorem checkA_7_5 : checkA tableM tableA 7 5 = true := by
  decide +kernel

theorem checkA_7_6 : checkA tableM tableA 7 6 = true := by
  decide +kernel

theorem checkA_7_7 : checkA tableM tableA 7 7 = true := by
  decide +kernel

theorem checkA_7_8 : checkA tableM tableA 7 8 = true := by
  decide +kernel

theorem checkA_7_9 : checkA tableM tableA 7 9 = true := by
  decide +kernel

theorem checkA_7_10 : checkA tableM tableA 7 10 = true := by
  decide +kernel

theorem checkA_7_11 : checkA tableM tableA 7 11 = true := by
  decide +kernel

theorem checkA_7_12 : checkA tableM tableA 7 12 = true := by
  decide +kernel

theorem checkA_7_13 : checkA tableM tableA 7 13 = true := by
  decide +kernel

theorem checkA_7_14 : checkA tableM tableA 7 14 = true := by
  decide +kernel

theorem checkA_7_15 : checkA tableM tableA 7 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
