module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 12`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_12_0 : checkA tableM tableA 12 0 = true := by
  decide +kernel

theorem checkA_12_1 : checkA tableM tableA 12 1 = true := by
  decide +kernel

theorem checkA_12_2 : checkA tableM tableA 12 2 = true := by
  decide +kernel

theorem checkA_12_3 : checkA tableM tableA 12 3 = true := by
  decide +kernel

theorem checkA_12_4 : checkA tableM tableA 12 4 = true := by
  decide +kernel

theorem checkA_12_5 : checkA tableM tableA 12 5 = true := by
  decide +kernel

theorem checkA_12_6 : checkA tableM tableA 12 6 = true := by
  decide +kernel

theorem checkA_12_7 : checkA tableM tableA 12 7 = true := by
  decide +kernel

theorem checkA_12_8 : checkA tableM tableA 12 8 = true := by
  decide +kernel

theorem checkA_12_9 : checkA tableM tableA 12 9 = true := by
  decide +kernel

theorem checkA_12_10 : checkA tableM tableA 12 10 = true := by
  decide +kernel

theorem checkA_12_11 : checkA tableM tableA 12 11 = true := by
  decide +kernel

theorem checkA_12_12 : checkA tableM tableA 12 12 = true := by
  decide +kernel

theorem checkA_12_13 : checkA tableM tableA 12 13 = true := by
  decide +kernel

theorem checkA_12_14 : checkA tableM tableA 12 14 = true := by
  decide +kernel

theorem checkA_12_15 : checkA tableM tableA 12 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
