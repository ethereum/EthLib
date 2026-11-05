module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 8`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_8_0 : checkB tableA tableB 8 0 = true := by
  decide +kernel

theorem checkB_8_1 : checkB tableA tableB 8 1 = true := by
  decide +kernel

theorem checkB_8_2 : checkB tableA tableB 8 2 = true := by
  decide +kernel

theorem checkB_8_3 : checkB tableA tableB 8 3 = true := by
  decide +kernel

theorem checkB_8_4 : checkB tableA tableB 8 4 = true := by
  decide +kernel

theorem checkB_8_5 : checkB tableA tableB 8 5 = true := by
  decide +kernel

theorem checkB_8_6 : checkB tableA tableB 8 6 = true := by
  decide +kernel

theorem checkB_8_7 : checkB tableA tableB 8 7 = true := by
  decide +kernel

theorem checkB_8_8 : checkB tableA tableB 8 8 = true := by
  decide +kernel

theorem checkB_8_9 : checkB tableA tableB 8 9 = true := by
  decide +kernel

theorem checkB_8_10 : checkB tableA tableB 8 10 = true := by
  decide +kernel

theorem checkB_8_11 : checkB tableA tableB 8 11 = true := by
  decide +kernel

theorem checkB_8_12 : checkB tableA tableB 8 12 = true := by
  decide +kernel

theorem checkB_8_13 : checkB tableA tableB 8 13 = true := by
  decide +kernel

theorem checkB_8_14 : checkB tableA tableB 8 14 = true := by
  decide +kernel

theorem checkB_8_15 : checkB tableA tableB 8 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
