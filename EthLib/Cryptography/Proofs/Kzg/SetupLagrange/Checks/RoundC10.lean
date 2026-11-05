module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 10`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_10_0 : checkC tableB tableL 10 0 = true := by
  decide +kernel

theorem checkC_10_1 : checkC tableB tableL 10 1 = true := by
  decide +kernel

theorem checkC_10_2 : checkC tableB tableL 10 2 = true := by
  decide +kernel

theorem checkC_10_3 : checkC tableB tableL 10 3 = true := by
  decide +kernel

theorem checkC_10_4 : checkC tableB tableL 10 4 = true := by
  decide +kernel

theorem checkC_10_5 : checkC tableB tableL 10 5 = true := by
  decide +kernel

theorem checkC_10_6 : checkC tableB tableL 10 6 = true := by
  decide +kernel

theorem checkC_10_7 : checkC tableB tableL 10 7 = true := by
  decide +kernel

theorem checkC_10_8 : checkC tableB tableL 10 8 = true := by
  decide +kernel

theorem checkC_10_9 : checkC tableB tableL 10 9 = true := by
  decide +kernel

theorem checkC_10_10 : checkC tableB tableL 10 10 = true := by
  decide +kernel

theorem checkC_10_11 : checkC tableB tableL 10 11 = true := by
  decide +kernel

theorem checkC_10_12 : checkC tableB tableL 10 12 = true := by
  decide +kernel

theorem checkC_10_13 : checkC tableB tableL 10 13 = true := by
  decide +kernel

theorem checkC_10_14 : checkC tableB tableL 10 14 = true := by
  decide +kernel

theorem checkC_10_15 : checkC tableB tableL 10 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
