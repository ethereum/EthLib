module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 9`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_9_0 : checkB tableA tableB 9 0 = true := by
  decide +kernel

theorem checkB_9_1 : checkB tableA tableB 9 1 = true := by
  decide +kernel

theorem checkB_9_2 : checkB tableA tableB 9 2 = true := by
  decide +kernel

theorem checkB_9_3 : checkB tableA tableB 9 3 = true := by
  decide +kernel

theorem checkB_9_4 : checkB tableA tableB 9 4 = true := by
  decide +kernel

theorem checkB_9_5 : checkB tableA tableB 9 5 = true := by
  decide +kernel

theorem checkB_9_6 : checkB tableA tableB 9 6 = true := by
  decide +kernel

theorem checkB_9_7 : checkB tableA tableB 9 7 = true := by
  decide +kernel

theorem checkB_9_8 : checkB tableA tableB 9 8 = true := by
  decide +kernel

theorem checkB_9_9 : checkB tableA tableB 9 9 = true := by
  decide +kernel

theorem checkB_9_10 : checkB tableA tableB 9 10 = true := by
  decide +kernel

theorem checkB_9_11 : checkB tableA tableB 9 11 = true := by
  decide +kernel

theorem checkB_9_12 : checkB tableA tableB 9 12 = true := by
  decide +kernel

theorem checkB_9_13 : checkB tableA tableB 9 13 = true := by
  decide +kernel

theorem checkB_9_14 : checkB tableA tableB 9 14 = true := by
  decide +kernel

theorem checkB_9_15 : checkB tableA tableB 9 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
