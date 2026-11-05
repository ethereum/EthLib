module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 5`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_5_0 : checkC tableB tableL 5 0 = true := by
  decide +kernel

theorem checkC_5_1 : checkC tableB tableL 5 1 = true := by
  decide +kernel

theorem checkC_5_2 : checkC tableB tableL 5 2 = true := by
  decide +kernel

theorem checkC_5_3 : checkC tableB tableL 5 3 = true := by
  decide +kernel

theorem checkC_5_4 : checkC tableB tableL 5 4 = true := by
  decide +kernel

theorem checkC_5_5 : checkC tableB tableL 5 5 = true := by
  decide +kernel

theorem checkC_5_6 : checkC tableB tableL 5 6 = true := by
  decide +kernel

theorem checkC_5_7 : checkC tableB tableL 5 7 = true := by
  decide +kernel

theorem checkC_5_8 : checkC tableB tableL 5 8 = true := by
  decide +kernel

theorem checkC_5_9 : checkC tableB tableL 5 9 = true := by
  decide +kernel

theorem checkC_5_10 : checkC tableB tableL 5 10 = true := by
  decide +kernel

theorem checkC_5_11 : checkC tableB tableL 5 11 = true := by
  decide +kernel

theorem checkC_5_12 : checkC tableB tableL 5 12 = true := by
  decide +kernel

theorem checkC_5_13 : checkC tableB tableL 5 13 = true := by
  decide +kernel

theorem checkC_5_14 : checkC tableB tableL 5 14 = true := by
  decide +kernel

theorem checkC_5_15 : checkC tableB tableL 5 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
