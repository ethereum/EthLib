module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 0`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_0_0 : checkC tableB tableL 0 0 = true := by
  decide +kernel

theorem checkC_0_1 : checkC tableB tableL 0 1 = true := by
  decide +kernel

theorem checkC_0_2 : checkC tableB tableL 0 2 = true := by
  decide +kernel

theorem checkC_0_3 : checkC tableB tableL 0 3 = true := by
  decide +kernel

theorem checkC_0_4 : checkC tableB tableL 0 4 = true := by
  decide +kernel

theorem checkC_0_5 : checkC tableB tableL 0 5 = true := by
  decide +kernel

theorem checkC_0_6 : checkC tableB tableL 0 6 = true := by
  decide +kernel

theorem checkC_0_7 : checkC tableB tableL 0 7 = true := by
  decide +kernel

theorem checkC_0_8 : checkC tableB tableL 0 8 = true := by
  decide +kernel

theorem checkC_0_9 : checkC tableB tableL 0 9 = true := by
  decide +kernel

theorem checkC_0_10 : checkC tableB tableL 0 10 = true := by
  decide +kernel

theorem checkC_0_11 : checkC tableB tableL 0 11 = true := by
  decide +kernel

theorem checkC_0_12 : checkC tableB tableL 0 12 = true := by
  decide +kernel

theorem checkC_0_13 : checkC tableB tableL 0 13 = true := by
  decide +kernel

theorem checkC_0_14 : checkC tableB tableL 0 14 = true := by
  decide +kernel

theorem checkC_0_15 : checkC tableB tableL 0 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
