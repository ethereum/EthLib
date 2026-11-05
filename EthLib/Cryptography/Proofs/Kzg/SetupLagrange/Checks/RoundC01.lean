module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 1`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_1_0 : checkC tableB tableL 1 0 = true := by
  decide +kernel

theorem checkC_1_1 : checkC tableB tableL 1 1 = true := by
  decide +kernel

theorem checkC_1_2 : checkC tableB tableL 1 2 = true := by
  decide +kernel

theorem checkC_1_3 : checkC tableB tableL 1 3 = true := by
  decide +kernel

theorem checkC_1_4 : checkC tableB tableL 1 4 = true := by
  decide +kernel

theorem checkC_1_5 : checkC tableB tableL 1 5 = true := by
  decide +kernel

theorem checkC_1_6 : checkC tableB tableL 1 6 = true := by
  decide +kernel

theorem checkC_1_7 : checkC tableB tableL 1 7 = true := by
  decide +kernel

theorem checkC_1_8 : checkC tableB tableL 1 8 = true := by
  decide +kernel

theorem checkC_1_9 : checkC tableB tableL 1 9 = true := by
  decide +kernel

theorem checkC_1_10 : checkC tableB tableL 1 10 = true := by
  decide +kernel

theorem checkC_1_11 : checkC tableB tableL 1 11 = true := by
  decide +kernel

theorem checkC_1_12 : checkC tableB tableL 1 12 = true := by
  decide +kernel

theorem checkC_1_13 : checkC tableB tableL 1 13 = true := by
  decide +kernel

theorem checkC_1_14 : checkC tableB tableL 1 14 = true := by
  decide +kernel

theorem checkC_1_15 : checkC tableB tableL 1 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
