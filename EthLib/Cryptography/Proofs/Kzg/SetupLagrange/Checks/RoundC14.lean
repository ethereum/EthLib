module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 14`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_14_0 : checkC tableB tableL 14 0 = true := by
  decide +kernel

theorem checkC_14_1 : checkC tableB tableL 14 1 = true := by
  decide +kernel

theorem checkC_14_2 : checkC tableB tableL 14 2 = true := by
  decide +kernel

theorem checkC_14_3 : checkC tableB tableL 14 3 = true := by
  decide +kernel

theorem checkC_14_4 : checkC tableB tableL 14 4 = true := by
  decide +kernel

theorem checkC_14_5 : checkC tableB tableL 14 5 = true := by
  decide +kernel

theorem checkC_14_6 : checkC tableB tableL 14 6 = true := by
  decide +kernel

theorem checkC_14_7 : checkC tableB tableL 14 7 = true := by
  decide +kernel

theorem checkC_14_8 : checkC tableB tableL 14 8 = true := by
  decide +kernel

theorem checkC_14_9 : checkC tableB tableL 14 9 = true := by
  decide +kernel

theorem checkC_14_10 : checkC tableB tableL 14 10 = true := by
  decide +kernel

theorem checkC_14_11 : checkC tableB tableL 14 11 = true := by
  decide +kernel

theorem checkC_14_12 : checkC tableB tableL 14 12 = true := by
  decide +kernel

theorem checkC_14_13 : checkC tableB tableL 14 13 = true := by
  decide +kernel

theorem checkC_14_14 : checkC tableB tableL 14 14 = true := by
  decide +kernel

theorem checkC_14_15 : checkC tableB tableL 14 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
