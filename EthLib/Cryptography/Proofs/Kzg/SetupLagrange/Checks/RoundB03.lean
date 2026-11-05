module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 3`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_3_0 : checkB tableA tableB 3 0 = true := by
  decide +kernel

theorem checkB_3_1 : checkB tableA tableB 3 1 = true := by
  decide +kernel

theorem checkB_3_2 : checkB tableA tableB 3 2 = true := by
  decide +kernel

theorem checkB_3_3 : checkB tableA tableB 3 3 = true := by
  decide +kernel

theorem checkB_3_4 : checkB tableA tableB 3 4 = true := by
  decide +kernel

theorem checkB_3_5 : checkB tableA tableB 3 5 = true := by
  decide +kernel

theorem checkB_3_6 : checkB tableA tableB 3 6 = true := by
  decide +kernel

theorem checkB_3_7 : checkB tableA tableB 3 7 = true := by
  decide +kernel

theorem checkB_3_8 : checkB tableA tableB 3 8 = true := by
  decide +kernel

theorem checkB_3_9 : checkB tableA tableB 3 9 = true := by
  decide +kernel

theorem checkB_3_10 : checkB tableA tableB 3 10 = true := by
  decide +kernel

theorem checkB_3_11 : checkB tableA tableB 3 11 = true := by
  decide +kernel

theorem checkB_3_12 : checkB tableA tableB 3 12 = true := by
  decide +kernel

theorem checkB_3_13 : checkB tableA tableB 3 13 = true := by
  decide +kernel

theorem checkB_3_14 : checkB tableA tableB 3 14 = true := by
  decide +kernel

theorem checkB_3_15 : checkB tableA tableB 3 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
