module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 6`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_6_0 : checkB tableA tableB 6 0 = true := by
  decide +kernel

theorem checkB_6_1 : checkB tableA tableB 6 1 = true := by
  decide +kernel

theorem checkB_6_2 : checkB tableA tableB 6 2 = true := by
  decide +kernel

theorem checkB_6_3 : checkB tableA tableB 6 3 = true := by
  decide +kernel

theorem checkB_6_4 : checkB tableA tableB 6 4 = true := by
  decide +kernel

theorem checkB_6_5 : checkB tableA tableB 6 5 = true := by
  decide +kernel

theorem checkB_6_6 : checkB tableA tableB 6 6 = true := by
  decide +kernel

theorem checkB_6_7 : checkB tableA tableB 6 7 = true := by
  decide +kernel

theorem checkB_6_8 : checkB tableA tableB 6 8 = true := by
  decide +kernel

theorem checkB_6_9 : checkB tableA tableB 6 9 = true := by
  decide +kernel

theorem checkB_6_10 : checkB tableA tableB 6 10 = true := by
  decide +kernel

theorem checkB_6_11 : checkB tableA tableB 6 11 = true := by
  decide +kernel

theorem checkB_6_12 : checkB tableA tableB 6 12 = true := by
  decide +kernel

theorem checkB_6_13 : checkB tableA tableB 6 13 = true := by
  decide +kernel

theorem checkB_6_14 : checkB tableA tableB 6 14 = true := by
  decide +kernel

theorem checkB_6_15 : checkB tableA tableB 6 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
