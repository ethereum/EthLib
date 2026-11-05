module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 6`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_6_0 : checkA tableM tableA 6 0 = true := by
  decide +kernel

theorem checkA_6_1 : checkA tableM tableA 6 1 = true := by
  decide +kernel

theorem checkA_6_2 : checkA tableM tableA 6 2 = true := by
  decide +kernel

theorem checkA_6_3 : checkA tableM tableA 6 3 = true := by
  decide +kernel

theorem checkA_6_4 : checkA tableM tableA 6 4 = true := by
  decide +kernel

theorem checkA_6_5 : checkA tableM tableA 6 5 = true := by
  decide +kernel

theorem checkA_6_6 : checkA tableM tableA 6 6 = true := by
  decide +kernel

theorem checkA_6_7 : checkA tableM tableA 6 7 = true := by
  decide +kernel

theorem checkA_6_8 : checkA tableM tableA 6 8 = true := by
  decide +kernel

theorem checkA_6_9 : checkA tableM tableA 6 9 = true := by
  decide +kernel

theorem checkA_6_10 : checkA tableM tableA 6 10 = true := by
  decide +kernel

theorem checkA_6_11 : checkA tableM tableA 6 11 = true := by
  decide +kernel

theorem checkA_6_12 : checkA tableM tableA 6 12 = true := by
  decide +kernel

theorem checkA_6_13 : checkA tableM tableA 6 13 = true := by
  decide +kernel

theorem checkA_6_14 : checkA tableM tableA 6 14 = true := by
  decide +kernel

theorem checkA_6_15 : checkA tableM tableA 6 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
