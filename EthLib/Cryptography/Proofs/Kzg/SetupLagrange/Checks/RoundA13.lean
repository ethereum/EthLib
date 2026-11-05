module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 13`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_13_0 : checkA tableM tableA 13 0 = true := by
  decide +kernel

theorem checkA_13_1 : checkA tableM tableA 13 1 = true := by
  decide +kernel

theorem checkA_13_2 : checkA tableM tableA 13 2 = true := by
  decide +kernel

theorem checkA_13_3 : checkA tableM tableA 13 3 = true := by
  decide +kernel

theorem checkA_13_4 : checkA tableM tableA 13 4 = true := by
  decide +kernel

theorem checkA_13_5 : checkA tableM tableA 13 5 = true := by
  decide +kernel

theorem checkA_13_6 : checkA tableM tableA 13 6 = true := by
  decide +kernel

theorem checkA_13_7 : checkA tableM tableA 13 7 = true := by
  decide +kernel

theorem checkA_13_8 : checkA tableM tableA 13 8 = true := by
  decide +kernel

theorem checkA_13_9 : checkA tableM tableA 13 9 = true := by
  decide +kernel

theorem checkA_13_10 : checkA tableM tableA 13 10 = true := by
  decide +kernel

theorem checkA_13_11 : checkA tableM tableA 13 11 = true := by
  decide +kernel

theorem checkA_13_12 : checkA tableM tableA 13 12 = true := by
  decide +kernel

theorem checkA_13_13 : checkA tableM tableA 13 13 = true := by
  decide +kernel

theorem checkA_13_14 : checkA tableM tableA 13 14 = true := by
  decide +kernel

theorem checkA_13_15 : checkA tableM tableA 13 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
