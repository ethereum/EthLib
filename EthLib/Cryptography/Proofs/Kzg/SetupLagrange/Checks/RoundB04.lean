module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 4`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_4_0 : checkB tableA tableB 4 0 = true := by
  decide +kernel

theorem checkB_4_1 : checkB tableA tableB 4 1 = true := by
  decide +kernel

theorem checkB_4_2 : checkB tableA tableB 4 2 = true := by
  decide +kernel

theorem checkB_4_3 : checkB tableA tableB 4 3 = true := by
  decide +kernel

theorem checkB_4_4 : checkB tableA tableB 4 4 = true := by
  decide +kernel

theorem checkB_4_5 : checkB tableA tableB 4 5 = true := by
  decide +kernel

theorem checkB_4_6 : checkB tableA tableB 4 6 = true := by
  decide +kernel

theorem checkB_4_7 : checkB tableA tableB 4 7 = true := by
  decide +kernel

theorem checkB_4_8 : checkB tableA tableB 4 8 = true := by
  decide +kernel

theorem checkB_4_9 : checkB tableA tableB 4 9 = true := by
  decide +kernel

theorem checkB_4_10 : checkB tableA tableB 4 10 = true := by
  decide +kernel

theorem checkB_4_11 : checkB tableA tableB 4 11 = true := by
  decide +kernel

theorem checkB_4_12 : checkB tableA tableB 4 12 = true := by
  decide +kernel

theorem checkB_4_13 : checkB tableA tableB 4 13 = true := by
  decide +kernel

theorem checkB_4_14 : checkB tableA tableB 4 14 = true := by
  decide +kernel

theorem checkB_4_15 : checkB tableA tableB 4 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
