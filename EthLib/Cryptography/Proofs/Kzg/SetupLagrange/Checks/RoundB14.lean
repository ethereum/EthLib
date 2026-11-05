module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 14`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_14_0 : checkB tableA tableB 14 0 = true := by
  decide +kernel

theorem checkB_14_1 : checkB tableA tableB 14 1 = true := by
  decide +kernel

theorem checkB_14_2 : checkB tableA tableB 14 2 = true := by
  decide +kernel

theorem checkB_14_3 : checkB tableA tableB 14 3 = true := by
  decide +kernel

theorem checkB_14_4 : checkB tableA tableB 14 4 = true := by
  decide +kernel

theorem checkB_14_5 : checkB tableA tableB 14 5 = true := by
  decide +kernel

theorem checkB_14_6 : checkB tableA tableB 14 6 = true := by
  decide +kernel

theorem checkB_14_7 : checkB tableA tableB 14 7 = true := by
  decide +kernel

theorem checkB_14_8 : checkB tableA tableB 14 8 = true := by
  decide +kernel

theorem checkB_14_9 : checkB tableA tableB 14 9 = true := by
  decide +kernel

theorem checkB_14_10 : checkB tableA tableB 14 10 = true := by
  decide +kernel

theorem checkB_14_11 : checkB tableA tableB 14 11 = true := by
  decide +kernel

theorem checkB_14_12 : checkB tableA tableB 14 12 = true := by
  decide +kernel

theorem checkB_14_13 : checkB tableA tableB 14 13 = true := by
  decide +kernel

theorem checkB_14_14 : checkB tableA tableB 14 14 = true := by
  decide +kernel

theorem checkB_14_15 : checkB tableA tableB 14 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
