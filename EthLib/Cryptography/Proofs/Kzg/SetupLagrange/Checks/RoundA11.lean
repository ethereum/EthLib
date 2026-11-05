module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Tables

/-!
# Proofs: the checks of the first round at `j2 = 11`

Each theorem checks one transform of size 16 in the kernel, for `j3` from 0 to 15.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

theorem checkA_11_0 : checkA tableM tableA 11 0 = true := by
  decide +kernel

theorem checkA_11_1 : checkA tableM tableA 11 1 = true := by
  decide +kernel

theorem checkA_11_2 : checkA tableM tableA 11 2 = true := by
  decide +kernel

theorem checkA_11_3 : checkA tableM tableA 11 3 = true := by
  decide +kernel

theorem checkA_11_4 : checkA tableM tableA 11 4 = true := by
  decide +kernel

theorem checkA_11_5 : checkA tableM tableA 11 5 = true := by
  decide +kernel

theorem checkA_11_6 : checkA tableM tableA 11 6 = true := by
  decide +kernel

theorem checkA_11_7 : checkA tableM tableA 11 7 = true := by
  decide +kernel

theorem checkA_11_8 : checkA tableM tableA 11 8 = true := by
  decide +kernel

theorem checkA_11_9 : checkA tableM tableA 11 9 = true := by
  decide +kernel

theorem checkA_11_10 : checkA tableM tableA 11 10 = true := by
  decide +kernel

theorem checkA_11_11 : checkA tableM tableA 11 11 = true := by
  decide +kernel

theorem checkA_11_12 : checkA tableM tableA 11 12 = true := by
  decide +kernel

theorem checkA_11_13 : checkA tableM tableA 11 13 = true := by
  decide +kernel

theorem checkA_11_14 : checkA tableM tableA 11 14 = true := by
  decide +kernel

theorem checkA_11_15 : checkA tableM tableA 11 15 = true := by
  decide +kernel

end EthLib.Cryptography.Kzg.SetupLagrange
