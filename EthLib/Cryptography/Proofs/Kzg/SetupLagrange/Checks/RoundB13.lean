module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 13`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_13_0 : checkB tableA tableB 13 0 = true := by
  decide +kernel

theorem checkB_13_1 : checkB tableA tableB 13 1 = true := by
  decide +kernel

theorem checkB_13_2 : checkB tableA tableB 13 2 = true := by
  decide +kernel

theorem checkB_13_3 : checkB tableA tableB 13 3 = true := by
  decide +kernel

theorem checkB_13_4 : checkB tableA tableB 13 4 = true := by
  decide +kernel

theorem checkB_13_5 : checkB tableA tableB 13 5 = true := by
  decide +kernel

theorem checkB_13_6 : checkB tableA tableB 13 6 = true := by
  decide +kernel

theorem checkB_13_7 : checkB tableA tableB 13 7 = true := by
  decide +kernel

theorem checkB_13_8 : checkB tableA tableB 13 8 = true := by
  decide +kernel

theorem checkB_13_9 : checkB tableA tableB 13 9 = true := by
  decide +kernel

theorem checkB_13_10 : checkB tableA tableB 13 10 = true := by
  decide +kernel

theorem checkB_13_11 : checkB tableA tableB 13 11 = true := by
  decide +kernel

theorem checkB_13_12 : checkB tableA tableB 13 12 = true := by
  decide +kernel

theorem checkB_13_13 : checkB tableA tableB 13 13 = true := by
  decide +kernel

theorem checkB_13_14 : checkB tableA tableB 13 14 = true := by
  decide +kernel

theorem checkB_13_15 : checkB tableA tableB 13 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
