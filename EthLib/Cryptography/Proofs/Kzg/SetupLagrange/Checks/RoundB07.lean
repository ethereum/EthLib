module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 7`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_7_0 : checkB tableA tableB 7 0 = true := by
  decide +kernel

theorem checkB_7_1 : checkB tableA tableB 7 1 = true := by
  decide +kernel

theorem checkB_7_2 : checkB tableA tableB 7 2 = true := by
  decide +kernel

theorem checkB_7_3 : checkB tableA tableB 7 3 = true := by
  decide +kernel

theorem checkB_7_4 : checkB tableA tableB 7 4 = true := by
  decide +kernel

theorem checkB_7_5 : checkB tableA tableB 7 5 = true := by
  decide +kernel

theorem checkB_7_6 : checkB tableA tableB 7 6 = true := by
  decide +kernel

theorem checkB_7_7 : checkB tableA tableB 7 7 = true := by
  decide +kernel

theorem checkB_7_8 : checkB tableA tableB 7 8 = true := by
  decide +kernel

theorem checkB_7_9 : checkB tableA tableB 7 9 = true := by
  decide +kernel

theorem checkB_7_10 : checkB tableA tableB 7 10 = true := by
  decide +kernel

theorem checkB_7_11 : checkB tableA tableB 7 11 = true := by
  decide +kernel

theorem checkB_7_12 : checkB tableA tableB 7 12 = true := by
  decide +kernel

theorem checkB_7_13 : checkB tableA tableB 7 13 = true := by
  decide +kernel

theorem checkB_7_14 : checkB tableA tableB 7 14 = true := by
  decide +kernel

theorem checkB_7_15 : checkB tableA tableB 7 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
