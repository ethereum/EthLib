module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 8`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_8_0 : checkC tableB tableL 8 0 = true := by
  decide +kernel

theorem checkC_8_1 : checkC tableB tableL 8 1 = true := by
  decide +kernel

theorem checkC_8_2 : checkC tableB tableL 8 2 = true := by
  decide +kernel

theorem checkC_8_3 : checkC tableB tableL 8 3 = true := by
  decide +kernel

theorem checkC_8_4 : checkC tableB tableL 8 4 = true := by
  decide +kernel

theorem checkC_8_5 : checkC tableB tableL 8 5 = true := by
  decide +kernel

theorem checkC_8_6 : checkC tableB tableL 8 6 = true := by
  decide +kernel

theorem checkC_8_7 : checkC tableB tableL 8 7 = true := by
  decide +kernel

theorem checkC_8_8 : checkC tableB tableL 8 8 = true := by
  decide +kernel

theorem checkC_8_9 : checkC tableB tableL 8 9 = true := by
  decide +kernel

theorem checkC_8_10 : checkC tableB tableL 8 10 = true := by
  decide +kernel

theorem checkC_8_11 : checkC tableB tableL 8 11 = true := by
  decide +kernel

theorem checkC_8_12 : checkC tableB tableL 8 12 = true := by
  decide +kernel

theorem checkC_8_13 : checkC tableB tableL 8 13 = true := by
  decide +kernel

theorem checkC_8_14 : checkC tableB tableL 8 14 = true := by
  decide +kernel

theorem checkC_8_15 : checkC tableB tableL 8 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
