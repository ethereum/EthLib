module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 1`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_1_0 : checkB tableA tableB 1 0 = true := by
  decide +kernel

theorem checkB_1_1 : checkB tableA tableB 1 1 = true := by
  decide +kernel

theorem checkB_1_2 : checkB tableA tableB 1 2 = true := by
  decide +kernel

theorem checkB_1_3 : checkB tableA tableB 1 3 = true := by
  decide +kernel

theorem checkB_1_4 : checkB tableA tableB 1 4 = true := by
  decide +kernel

theorem checkB_1_5 : checkB tableA tableB 1 5 = true := by
  decide +kernel

theorem checkB_1_6 : checkB tableA tableB 1 6 = true := by
  decide +kernel

theorem checkB_1_7 : checkB tableA tableB 1 7 = true := by
  decide +kernel

theorem checkB_1_8 : checkB tableA tableB 1 8 = true := by
  decide +kernel

theorem checkB_1_9 : checkB tableA tableB 1 9 = true := by
  decide +kernel

theorem checkB_1_10 : checkB tableA tableB 1 10 = true := by
  decide +kernel

theorem checkB_1_11 : checkB tableA tableB 1 11 = true := by
  decide +kernel

theorem checkB_1_12 : checkB tableA tableB 1 12 = true := by
  decide +kernel

theorem checkB_1_13 : checkB tableA tableB 1 13 = true := by
  decide +kernel

theorem checkB_1_14 : checkB tableA tableB 1 14 = true := by
  decide +kernel

theorem checkB_1_15 : checkB tableA tableB 1 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
