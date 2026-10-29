import EthLib.Cryptography.Proofs.Sphincs.KnownAnswer

/-!
# Proofs: the known answer's FORS openings, trees 12 to 23

Each opening leads to its tree's two level-9 nodes, the ones the FORS key states.

A tree costs 10 permutations, a leaf and 9 nodes, so these 12 trees cost 120.

The 24 trees are split over two files, so each file stays within the memory of a CI runner.
-/

namespace EthLib.Cryptography.Sphincs.KnownAnswer

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

set_option maxRecDepth 100000

/-- FORS trees 12 to 15. -/
theorem forsTrees_12 : ∀ kappa : Fin FORS_TREES, 12 ≤ kappa.val → kappa.val < 16 →
    treeRecover publicKey.publicParam 65963065 kappa leaves[kappa] signature.fors[kappa] = forsKey[kappa] := by
  simp only [Kernel.treeRecover_eq]
  decide +kernel

/-- FORS trees 16 to 19. -/
theorem forsTrees_16 : ∀ kappa : Fin FORS_TREES, 16 ≤ kappa.val → kappa.val < 20 →
    treeRecover publicKey.publicParam 65963065 kappa leaves[kappa] signature.fors[kappa] = forsKey[kappa] := by
  simp only [Kernel.treeRecover_eq]
  decide +kernel

/-- FORS trees 20 to 23. -/
theorem forsTrees_20 : ∀ kappa : Fin FORS_TREES, 20 ≤ kappa.val → kappa.val < 24 →
    treeRecover publicKey.publicParam 65963065 kappa leaves[kappa] signature.fors[kappa] = forsKey[kappa] := by
  simp only [Kernel.treeRecover_eq]
  decide +kernel

end EthLib.Cryptography.Sphincs.KnownAnswer
