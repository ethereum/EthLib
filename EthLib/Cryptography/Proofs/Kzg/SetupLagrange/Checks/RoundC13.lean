module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 13`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_13_0 : checkC tableB tableL 13 0 = true := by
  decide +kernel

theorem checkC_13_1 : checkC tableB tableL 13 1 = true := by
  decide +kernel

theorem checkC_13_2 : checkC tableB tableL 13 2 = true := by
  decide +kernel

theorem checkC_13_3 : checkC tableB tableL 13 3 = true := by
  decide +kernel

theorem checkC_13_4 : checkC tableB tableL 13 4 = true := by
  decide +kernel

theorem checkC_13_5 : checkC tableB tableL 13 5 = true := by
  decide +kernel

theorem checkC_13_6 : checkC tableB tableL 13 6 = true := by
  decide +kernel

theorem checkC_13_7 : checkC tableB tableL 13 7 = true := by
  decide +kernel

theorem checkC_13_8 : checkC tableB tableL 13 8 = true := by
  decide +kernel

theorem checkC_13_9 : checkC tableB tableL 13 9 = true := by
  decide +kernel

theorem checkC_13_10 : checkC tableB tableL 13 10 = true := by
  decide +kernel

theorem checkC_13_11 : checkC tableB tableL 13 11 = true := by
  decide +kernel

theorem checkC_13_12 : checkC tableB tableL 13 12 = true := by
  decide +kernel

theorem checkC_13_13 : checkC tableB tableL 13 13 = true := by
  decide +kernel

theorem checkC_13_14 : checkC tableB tableL 13 14 = true := by
  decide +kernel

theorem checkC_13_15 : checkC tableB tableL 13 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
