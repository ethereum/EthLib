module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the second round at `k1 = 11`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkB_11_0 : checkB tableA tableB 11 0 = true := by
  decide +kernel

theorem checkB_11_1 : checkB tableA tableB 11 1 = true := by
  decide +kernel

theorem checkB_11_2 : checkB tableA tableB 11 2 = true := by
  decide +kernel

theorem checkB_11_3 : checkB tableA tableB 11 3 = true := by
  decide +kernel

theorem checkB_11_4 : checkB tableA tableB 11 4 = true := by
  decide +kernel

theorem checkB_11_5 : checkB tableA tableB 11 5 = true := by
  decide +kernel

theorem checkB_11_6 : checkB tableA tableB 11 6 = true := by
  decide +kernel

theorem checkB_11_7 : checkB tableA tableB 11 7 = true := by
  decide +kernel

theorem checkB_11_8 : checkB tableA tableB 11 8 = true := by
  decide +kernel

theorem checkB_11_9 : checkB tableA tableB 11 9 = true := by
  decide +kernel

theorem checkB_11_10 : checkB tableA tableB 11 10 = true := by
  decide +kernel

theorem checkB_11_11 : checkB tableA tableB 11 11 = true := by
  decide +kernel

theorem checkB_11_12 : checkB tableA tableB 11 12 = true := by
  decide +kernel

theorem checkB_11_13 : checkB tableA tableB 11 13 = true := by
  decide +kernel

theorem checkB_11_14 : checkB tableA tableB 11 14 = true := by
  decide +kernel

theorem checkB_11_15 : checkB tableA tableB 11 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
