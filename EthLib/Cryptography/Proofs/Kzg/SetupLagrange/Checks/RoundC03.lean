module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 3`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_3_0 : checkC tableB tableL 3 0 = true := by
  decide +kernel

theorem checkC_3_1 : checkC tableB tableL 3 1 = true := by
  decide +kernel

theorem checkC_3_2 : checkC tableB tableL 3 2 = true := by
  decide +kernel

theorem checkC_3_3 : checkC tableB tableL 3 3 = true := by
  decide +kernel

theorem checkC_3_4 : checkC tableB tableL 3 4 = true := by
  decide +kernel

theorem checkC_3_5 : checkC tableB tableL 3 5 = true := by
  decide +kernel

theorem checkC_3_6 : checkC tableB tableL 3 6 = true := by
  decide +kernel

theorem checkC_3_7 : checkC tableB tableL 3 7 = true := by
  decide +kernel

theorem checkC_3_8 : checkC tableB tableL 3 8 = true := by
  decide +kernel

theorem checkC_3_9 : checkC tableB tableL 3 9 = true := by
  decide +kernel

theorem checkC_3_10 : checkC tableB tableL 3 10 = true := by
  decide +kernel

theorem checkC_3_11 : checkC tableB tableL 3 11 = true := by
  decide +kernel

theorem checkC_3_12 : checkC tableB tableL 3 12 = true := by
  decide +kernel

theorem checkC_3_13 : checkC tableB tableL 3 13 = true := by
  decide +kernel

theorem checkC_3_14 : checkC tableB tableL 3 14 = true := by
  decide +kernel

theorem checkC_3_15 : checkC tableB tableL 3 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
