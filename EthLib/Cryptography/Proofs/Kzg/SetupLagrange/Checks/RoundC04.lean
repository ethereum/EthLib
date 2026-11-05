module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 4`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_4_0 : checkC tableB tableL 4 0 = true := by
  decide +kernel

theorem checkC_4_1 : checkC tableB tableL 4 1 = true := by
  decide +kernel

theorem checkC_4_2 : checkC tableB tableL 4 2 = true := by
  decide +kernel

theorem checkC_4_3 : checkC tableB tableL 4 3 = true := by
  decide +kernel

theorem checkC_4_4 : checkC tableB tableL 4 4 = true := by
  decide +kernel

theorem checkC_4_5 : checkC tableB tableL 4 5 = true := by
  decide +kernel

theorem checkC_4_6 : checkC tableB tableL 4 6 = true := by
  decide +kernel

theorem checkC_4_7 : checkC tableB tableL 4 7 = true := by
  decide +kernel

theorem checkC_4_8 : checkC tableB tableL 4 8 = true := by
  decide +kernel

theorem checkC_4_9 : checkC tableB tableL 4 9 = true := by
  decide +kernel

theorem checkC_4_10 : checkC tableB tableL 4 10 = true := by
  decide +kernel

theorem checkC_4_11 : checkC tableB tableL 4 11 = true := by
  decide +kernel

theorem checkC_4_12 : checkC tableB tableL 4 12 = true := by
  decide +kernel

theorem checkC_4_13 : checkC tableB tableL 4 13 = true := by
  decide +kernel

theorem checkC_4_14 : checkC tableB tableL 4 14 = true := by
  decide +kernel

theorem checkC_4_15 : checkC tableB tableL 4 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
