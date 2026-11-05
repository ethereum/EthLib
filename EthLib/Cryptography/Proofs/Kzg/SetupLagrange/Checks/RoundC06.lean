module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 6`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_6_0 : checkC tableB tableL 6 0 = true := by
  decide +kernel

theorem checkC_6_1 : checkC tableB tableL 6 1 = true := by
  decide +kernel

theorem checkC_6_2 : checkC tableB tableL 6 2 = true := by
  decide +kernel

theorem checkC_6_3 : checkC tableB tableL 6 3 = true := by
  decide +kernel

theorem checkC_6_4 : checkC tableB tableL 6 4 = true := by
  decide +kernel

theorem checkC_6_5 : checkC tableB tableL 6 5 = true := by
  decide +kernel

theorem checkC_6_6 : checkC tableB tableL 6 6 = true := by
  decide +kernel

theorem checkC_6_7 : checkC tableB tableL 6 7 = true := by
  decide +kernel

theorem checkC_6_8 : checkC tableB tableL 6 8 = true := by
  decide +kernel

theorem checkC_6_9 : checkC tableB tableL 6 9 = true := by
  decide +kernel

theorem checkC_6_10 : checkC tableB tableL 6 10 = true := by
  decide +kernel

theorem checkC_6_11 : checkC tableB tableL 6 11 = true := by
  decide +kernel

theorem checkC_6_12 : checkC tableB tableL 6 12 = true := by
  decide +kernel

theorem checkC_6_13 : checkC tableB tableL 6 13 = true := by
  decide +kernel

theorem checkC_6_14 : checkC tableB tableL 6 14 = true := by
  decide +kernel

theorem checkC_6_15 : checkC tableB tableL 6 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
