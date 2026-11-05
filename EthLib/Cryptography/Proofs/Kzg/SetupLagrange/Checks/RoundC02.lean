module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 2`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_2_0 : checkC tableB tableL 2 0 = true := by
  decide +kernel

theorem checkC_2_1 : checkC tableB tableL 2 1 = true := by
  decide +kernel

theorem checkC_2_2 : checkC tableB tableL 2 2 = true := by
  decide +kernel

theorem checkC_2_3 : checkC tableB tableL 2 3 = true := by
  decide +kernel

theorem checkC_2_4 : checkC tableB tableL 2 4 = true := by
  decide +kernel

theorem checkC_2_5 : checkC tableB tableL 2 5 = true := by
  decide +kernel

theorem checkC_2_6 : checkC tableB tableL 2 6 = true := by
  decide +kernel

theorem checkC_2_7 : checkC tableB tableL 2 7 = true := by
  decide +kernel

theorem checkC_2_8 : checkC tableB tableL 2 8 = true := by
  decide +kernel

theorem checkC_2_9 : checkC tableB tableL 2 9 = true := by
  decide +kernel

theorem checkC_2_10 : checkC tableB tableL 2 10 = true := by
  decide +kernel

theorem checkC_2_11 : checkC tableB tableL 2 11 = true := by
  decide +kernel

theorem checkC_2_12 : checkC tableB tableL 2 12 = true := by
  decide +kernel

theorem checkC_2_13 : checkC tableB tableL 2 13 = true := by
  decide +kernel

theorem checkC_2_14 : checkC tableB tableL 2 14 = true := by
  decide +kernel

theorem checkC_2_15 : checkC tableB tableL 2 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
