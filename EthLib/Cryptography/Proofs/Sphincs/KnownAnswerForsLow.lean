import EthLib.Cryptography.Proofs.Sphincs.KnownAnswer

/-!
# Proofs: the known answer's FORS openings, trees 0 to 11

Each opening leads to its tree's two level-9 nodes, the ones the FORS key states.

A tree costs 10 permutations, a leaf and 9 nodes, so these 12 trees cost 120.

The 24 trees are split over two files, so each file stays within the memory of a CI runner.
-/

namespace EthLib.Cryptography.Sphincs.KnownAnswer

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

set_option maxRecDepth 100000

/-- FORS trees 0 to 3. -/
theorem forsTrees_0 : ∀ kappa : Fin FORS_TREES, 0 ≤ kappa.val → kappa.val < 4 →
    treeRecover publicKey.publicParam 65963065 kappa leaves[kappa] signature.fors[kappa] = forsKey[kappa] := by
  simp only [Kernel.treeRecover_eq]
  decide +kernel

/-- FORS trees 4 to 7. -/
theorem forsTrees_4 : ∀ kappa : Fin FORS_TREES, 4 ≤ kappa.val → kappa.val < 8 →
    treeRecover publicKey.publicParam 65963065 kappa leaves[kappa] signature.fors[kappa] = forsKey[kappa] := by
  simp only [Kernel.treeRecover_eq]
  decide +kernel

/-- FORS trees 8 to 11. -/
theorem forsTrees_8 : ∀ kappa : Fin FORS_TREES, 8 ≤ kappa.val → kappa.val < 12 →
    treeRecover publicKey.publicParam 65963065 kappa leaves[kappa] signature.fors[kappa] = forsKey[kappa] := by
  simp only [Kernel.treeRecover_eq]
  decide +kernel

end EthLib.Cryptography.Sphincs.KnownAnswer
