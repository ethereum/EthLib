module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 10`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_10_0 : checkB tableA tableB 10 0 = true := by
  decide +kernel

theorem checkB_10_1 : checkB tableA tableB 10 1 = true := by
  decide +kernel

theorem checkB_10_2 : checkB tableA tableB 10 2 = true := by
  decide +kernel

theorem checkB_10_3 : checkB tableA tableB 10 3 = true := by
  decide +kernel

theorem checkB_10_4 : checkB tableA tableB 10 4 = true := by
  decide +kernel

theorem checkB_10_5 : checkB tableA tableB 10 5 = true := by
  decide +kernel

theorem checkB_10_6 : checkB tableA tableB 10 6 = true := by
  decide +kernel

theorem checkB_10_7 : checkB tableA tableB 10 7 = true := by
  decide +kernel

theorem checkB_10_8 : checkB tableA tableB 10 8 = true := by
  decide +kernel

theorem checkB_10_9 : checkB tableA tableB 10 9 = true := by
  decide +kernel

theorem checkB_10_10 : checkB tableA tableB 10 10 = true := by
  decide +kernel

theorem checkB_10_11 : checkB tableA tableB 10 11 = true := by
  decide +kernel

theorem checkB_10_12 : checkB tableA tableB 10 12 = true := by
  decide +kernel

theorem checkB_10_13 : checkB tableA tableB 10 13 = true := by
  decide +kernel

theorem checkB_10_14 : checkB tableA tableB 10 14 = true := by
  decide +kernel

theorem checkB_10_15 : checkB tableA tableB 10 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
