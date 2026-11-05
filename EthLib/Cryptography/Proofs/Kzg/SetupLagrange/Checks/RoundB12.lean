module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 12`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_12_0 : checkB tableA tableB 12 0 = true := by
  decide +kernel

theorem checkB_12_1 : checkB tableA tableB 12 1 = true := by
  decide +kernel

theorem checkB_12_2 : checkB tableA tableB 12 2 = true := by
  decide +kernel

theorem checkB_12_3 : checkB tableA tableB 12 3 = true := by
  decide +kernel

theorem checkB_12_4 : checkB tableA tableB 12 4 = true := by
  decide +kernel

theorem checkB_12_5 : checkB tableA tableB 12 5 = true := by
  decide +kernel

theorem checkB_12_6 : checkB tableA tableB 12 6 = true := by
  decide +kernel

theorem checkB_12_7 : checkB tableA tableB 12 7 = true := by
  decide +kernel

theorem checkB_12_8 : checkB tableA tableB 12 8 = true := by
  decide +kernel

theorem checkB_12_9 : checkB tableA tableB 12 9 = true := by
  decide +kernel

theorem checkB_12_10 : checkB tableA tableB 12 10 = true := by
  decide +kernel

theorem checkB_12_11 : checkB tableA tableB 12 11 = true := by
  decide +kernel

theorem checkB_12_12 : checkB tableA tableB 12 12 = true := by
  decide +kernel

theorem checkB_12_13 : checkB tableA tableB 12 13 = true := by
  decide +kernel

theorem checkB_12_14 : checkB tableA tableB 12 14 = true := by
  decide +kernel

theorem checkB_12_15 : checkB tableA tableB 12 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
