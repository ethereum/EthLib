module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 7`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_7_0 : checkC tableB tableL 7 0 = true := by
  decide +kernel

theorem checkC_7_1 : checkC tableB tableL 7 1 = true := by
  decide +kernel

theorem checkC_7_2 : checkC tableB tableL 7 2 = true := by
  decide +kernel

theorem checkC_7_3 : checkC tableB tableL 7 3 = true := by
  decide +kernel

theorem checkC_7_4 : checkC tableB tableL 7 4 = true := by
  decide +kernel

theorem checkC_7_5 : checkC tableB tableL 7 5 = true := by
  decide +kernel

theorem checkC_7_6 : checkC tableB tableL 7 6 = true := by
  decide +kernel

theorem checkC_7_7 : checkC tableB tableL 7 7 = true := by
  decide +kernel

theorem checkC_7_8 : checkC tableB tableL 7 8 = true := by
  decide +kernel

theorem checkC_7_9 : checkC tableB tableL 7 9 = true := by
  decide +kernel

theorem checkC_7_10 : checkC tableB tableL 7 10 = true := by
  decide +kernel

theorem checkC_7_11 : checkC tableB tableL 7 11 = true := by
  decide +kernel

theorem checkC_7_12 : checkC tableB tableL 7 12 = true := by
  decide +kernel

theorem checkC_7_13 : checkC tableB tableL 7 13 = true := by
  decide +kernel

theorem checkC_7_14 : checkC tableB tableL 7 14 = true := by
  decide +kernel

theorem checkC_7_15 : checkC tableB tableL 7 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
