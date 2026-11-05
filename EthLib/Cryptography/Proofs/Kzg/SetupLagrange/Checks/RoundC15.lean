module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 15`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_15_0 : checkC tableB tableL 15 0 = true := by
  decide +kernel

theorem checkC_15_1 : checkC tableB tableL 15 1 = true := by
  decide +kernel

theorem checkC_15_2 : checkC tableB tableL 15 2 = true := by
  decide +kernel

theorem checkC_15_3 : checkC tableB tableL 15 3 = true := by
  decide +kernel

theorem checkC_15_4 : checkC tableB tableL 15 4 = true := by
  decide +kernel

theorem checkC_15_5 : checkC tableB tableL 15 5 = true := by
  decide +kernel

theorem checkC_15_6 : checkC tableB tableL 15 6 = true := by
  decide +kernel

theorem checkC_15_7 : checkC tableB tableL 15 7 = true := by
  decide +kernel

theorem checkC_15_8 : checkC tableB tableL 15 8 = true := by
  decide +kernel

theorem checkC_15_9 : checkC tableB tableL 15 9 = true := by
  decide +kernel

theorem checkC_15_10 : checkC tableB tableL 15 10 = true := by
  decide +kernel

theorem checkC_15_11 : checkC tableB tableL 15 11 = true := by
  decide +kernel

theorem checkC_15_12 : checkC tableB tableL 15 12 = true := by
  decide +kernel

theorem checkC_15_13 : checkC tableB tableL 15 13 = true := by
  decide +kernel

theorem checkC_15_14 : checkC tableB tableL 15 14 = true := by
  decide +kernel

theorem checkC_15_15 : checkC tableB tableL 15 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
