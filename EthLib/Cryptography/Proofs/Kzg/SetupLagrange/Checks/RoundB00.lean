module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 0`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_0_0 : checkB tableA tableB 0 0 = true := by
  decide +kernel

theorem checkB_0_1 : checkB tableA tableB 0 1 = true := by
  decide +kernel

theorem checkB_0_2 : checkB tableA tableB 0 2 = true := by
  decide +kernel

theorem checkB_0_3 : checkB tableA tableB 0 3 = true := by
  decide +kernel

theorem checkB_0_4 : checkB tableA tableB 0 4 = true := by
  decide +kernel

theorem checkB_0_5 : checkB tableA tableB 0 5 = true := by
  decide +kernel

theorem checkB_0_6 : checkB tableA tableB 0 6 = true := by
  decide +kernel

theorem checkB_0_7 : checkB tableA tableB 0 7 = true := by
  decide +kernel

theorem checkB_0_8 : checkB tableA tableB 0 8 = true := by
  decide +kernel

theorem checkB_0_9 : checkB tableA tableB 0 9 = true := by
  decide +kernel

theorem checkB_0_10 : checkB tableA tableB 0 10 = true := by
  decide +kernel

theorem checkB_0_11 : checkB tableA tableB 0 11 = true := by
  decide +kernel

theorem checkB_0_12 : checkB tableA tableB 0 12 = true := by
  decide +kernel

theorem checkB_0_13 : checkB tableA tableB 0 13 = true := by
  decide +kernel

theorem checkB_0_14 : checkB tableA tableB 0 14 = true := by
  decide +kernel

theorem checkB_0_15 : checkB tableA tableB 0 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
