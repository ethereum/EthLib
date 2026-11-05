module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 9`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_9_0 : checkC tableB tableL 9 0 = true := by
  decide +kernel

theorem checkC_9_1 : checkC tableB tableL 9 1 = true := by
  decide +kernel

theorem checkC_9_2 : checkC tableB tableL 9 2 = true := by
  decide +kernel

theorem checkC_9_3 : checkC tableB tableL 9 3 = true := by
  decide +kernel

theorem checkC_9_4 : checkC tableB tableL 9 4 = true := by
  decide +kernel

theorem checkC_9_5 : checkC tableB tableL 9 5 = true := by
  decide +kernel

theorem checkC_9_6 : checkC tableB tableL 9 6 = true := by
  decide +kernel

theorem checkC_9_7 : checkC tableB tableL 9 7 = true := by
  decide +kernel

theorem checkC_9_8 : checkC tableB tableL 9 8 = true := by
  decide +kernel

theorem checkC_9_9 : checkC tableB tableL 9 9 = true := by
  decide +kernel

theorem checkC_9_10 : checkC tableB tableL 9 10 = true := by
  decide +kernel

theorem checkC_9_11 : checkC tableB tableL 9 11 = true := by
  decide +kernel

theorem checkC_9_12 : checkC tableB tableL 9 12 = true := by
  decide +kernel

theorem checkC_9_13 : checkC tableB tableL 9 13 = true := by
  decide +kernel

theorem checkC_9_14 : checkC tableB tableL 9 14 = true := by
  decide +kernel

theorem checkC_9_15 : checkC tableB tableL 9 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
