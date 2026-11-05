module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the third round at `k1 = 11`

Each theorem checks one transform of size 16 in the kernel, for `k2` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkC_11_0 : checkC tableB tableL 11 0 = true := by
  decide +kernel

theorem checkC_11_1 : checkC tableB tableL 11 1 = true := by
  decide +kernel

theorem checkC_11_2 : checkC tableB tableL 11 2 = true := by
  decide +kernel

theorem checkC_11_3 : checkC tableB tableL 11 3 = true := by
  decide +kernel

theorem checkC_11_4 : checkC tableB tableL 11 4 = true := by
  decide +kernel

theorem checkC_11_5 : checkC tableB tableL 11 5 = true := by
  decide +kernel

theorem checkC_11_6 : checkC tableB tableL 11 6 = true := by
  decide +kernel

theorem checkC_11_7 : checkC tableB tableL 11 7 = true := by
  decide +kernel

theorem checkC_11_8 : checkC tableB tableL 11 8 = true := by
  decide +kernel

theorem checkC_11_9 : checkC tableB tableL 11 9 = true := by
  decide +kernel

theorem checkC_11_10 : checkC tableB tableL 11 10 = true := by
  decide +kernel

theorem checkC_11_11 : checkC tableB tableL 11 11 = true := by
  decide +kernel

theorem checkC_11_12 : checkC tableB tableL 11 12 = true := by
  decide +kernel

theorem checkC_11_13 : checkC tableB tableL 11 13 = true := by
  decide +kernel

theorem checkC_11_14 : checkC tableB tableL 11 14 = true := by
  decide +kernel

theorem checkC_11_15 : checkC tableB tableL 11 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
