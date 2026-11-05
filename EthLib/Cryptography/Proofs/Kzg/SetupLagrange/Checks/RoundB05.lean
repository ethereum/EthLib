module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 5`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_5_0 : checkB tableA tableB 5 0 = true := by
  decide +kernel

theorem checkB_5_1 : checkB tableA tableB 5 1 = true := by
  decide +kernel

theorem checkB_5_2 : checkB tableA tableB 5 2 = true := by
  decide +kernel

theorem checkB_5_3 : checkB tableA tableB 5 3 = true := by
  decide +kernel

theorem checkB_5_4 : checkB tableA tableB 5 4 = true := by
  decide +kernel

theorem checkB_5_5 : checkB tableA tableB 5 5 = true := by
  decide +kernel

theorem checkB_5_6 : checkB tableA tableB 5 6 = true := by
  decide +kernel

theorem checkB_5_7 : checkB tableA tableB 5 7 = true := by
  decide +kernel

theorem checkB_5_8 : checkB tableA tableB 5 8 = true := by
  decide +kernel

theorem checkB_5_9 : checkB tableA tableB 5 9 = true := by
  decide +kernel

theorem checkB_5_10 : checkB tableA tableB 5 10 = true := by
  decide +kernel

theorem checkB_5_11 : checkB tableA tableB 5 11 = true := by
  decide +kernel

theorem checkB_5_12 : checkB tableA tableB 5 12 = true := by
  decide +kernel

theorem checkB_5_13 : checkB tableA tableB 5 13 = true := by
  decide +kernel

theorem checkB_5_14 : checkB tableA tableB 5 14 = true := by
  decide +kernel

theorem checkB_5_15 : checkB tableA tableB 5 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
