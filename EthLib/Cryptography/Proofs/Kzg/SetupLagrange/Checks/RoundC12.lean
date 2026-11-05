module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 12`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_12_0 : checkC tableB tableL 12 0 = true := by
  decide +kernel

theorem checkC_12_1 : checkC tableB tableL 12 1 = true := by
  decide +kernel

theorem checkC_12_2 : checkC tableB tableL 12 2 = true := by
  decide +kernel

theorem checkC_12_3 : checkC tableB tableL 12 3 = true := by
  decide +kernel

theorem checkC_12_4 : checkC tableB tableL 12 4 = true := by
  decide +kernel

theorem checkC_12_5 : checkC tableB tableL 12 5 = true := by
  decide +kernel

theorem checkC_12_6 : checkC tableB tableL 12 6 = true := by
  decide +kernel

theorem checkC_12_7 : checkC tableB tableL 12 7 = true := by
  decide +kernel

theorem checkC_12_8 : checkC tableB tableL 12 8 = true := by
  decide +kernel

theorem checkC_12_9 : checkC tableB tableL 12 9 = true := by
  decide +kernel

theorem checkC_12_10 : checkC tableB tableL 12 10 = true := by
  decide +kernel

theorem checkC_12_11 : checkC tableB tableL 12 11 = true := by
  decide +kernel

theorem checkC_12_12 : checkC tableB tableL 12 12 = true := by
  decide +kernel

theorem checkC_12_13 : checkC tableB tableL 12 13 = true := by
  decide +kernel

theorem checkC_12_14 : checkC tableB tableL 12 14 = true := by
  decide +kernel

theorem checkC_12_15 : checkC tableB tableL 12 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
