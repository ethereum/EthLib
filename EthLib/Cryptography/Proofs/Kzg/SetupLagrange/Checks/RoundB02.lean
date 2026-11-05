module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 2`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_2_0 : checkB tableA tableB 2 0 = true := by
  decide +kernel

theorem checkB_2_1 : checkB tableA tableB 2 1 = true := by
  decide +kernel

theorem checkB_2_2 : checkB tableA tableB 2 2 = true := by
  decide +kernel

theorem checkB_2_3 : checkB tableA tableB 2 3 = true := by
  decide +kernel

theorem checkB_2_4 : checkB tableA tableB 2 4 = true := by
  decide +kernel

theorem checkB_2_5 : checkB tableA tableB 2 5 = true := by
  decide +kernel

theorem checkB_2_6 : checkB tableA tableB 2 6 = true := by
  decide +kernel

theorem checkB_2_7 : checkB tableA tableB 2 7 = true := by
  decide +kernel

theorem checkB_2_8 : checkB tableA tableB 2 8 = true := by
  decide +kernel

theorem checkB_2_9 : checkB tableA tableB 2 9 = true := by
  decide +kernel

theorem checkB_2_10 : checkB tableA tableB 2 10 = true := by
  decide +kernel

theorem checkB_2_11 : checkB tableA tableB 2 11 = true := by
  decide +kernel

theorem checkB_2_12 : checkB tableA tableB 2 12 = true := by
  decide +kernel

theorem checkB_2_13 : checkB tableA tableB 2 13 = true := by
  decide +kernel

theorem checkB_2_14 : checkB tableA tableB 2 14 = true := by
  decide +kernel

theorem checkB_2_15 : checkB tableA tableB 2 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
