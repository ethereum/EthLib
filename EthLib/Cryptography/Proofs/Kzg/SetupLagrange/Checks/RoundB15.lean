module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 15`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_15_0 : checkB tableA tableB 15 0 = true := by
  decide +kernel

theorem checkB_15_1 : checkB tableA tableB 15 1 = true := by
  decide +kernel

theorem checkB_15_2 : checkB tableA tableB 15 2 = true := by
  decide +kernel

theorem checkB_15_3 : checkB tableA tableB 15 3 = true := by
  decide +kernel

theorem checkB_15_4 : checkB tableA tableB 15 4 = true := by
  decide +kernel

theorem checkB_15_5 : checkB tableA tableB 15 5 = true := by
  decide +kernel

theorem checkB_15_6 : checkB tableA tableB 15 6 = true := by
  decide +kernel

theorem checkB_15_7 : checkB tableA tableB 15 7 = true := by
  decide +kernel

theorem checkB_15_8 : checkB tableA tableB 15 8 = true := by
  decide +kernel

theorem checkB_15_9 : checkB tableA tableB 15 9 = true := by
  decide +kernel

theorem checkB_15_10 : checkB tableA tableB 15 10 = true := by
  decide +kernel

theorem checkB_15_11 : checkB tableA tableB 15 11 = true := by
  decide +kernel

theorem checkB_15_12 : checkB tableA tableB 15 12 = true := by
  decide +kernel

theorem checkB_15_13 : checkB tableA tableB 15 13 = true := by
  decide +kernel

theorem checkB_15_14 : checkB tableA tableB 15 14 = true := by
  decide +kernel

theorem checkB_15_15 : checkB tableA tableB 15 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
