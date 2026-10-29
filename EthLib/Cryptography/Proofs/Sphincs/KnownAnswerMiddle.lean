import EthLib.Cryptography.Proofs.Sphincs.KnownAnswer

/-!
# Proofs: the known answer's middle layer

The middle key signs the bottom root, and its path reaches the root of middle tree 1006.
-/

namespace EthLib.Cryptography.Sphincs.KnownAnswer

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

set_option maxRecDepth 100000

/-- The middle layer's counter encodes its message as a codeword. -/
theorem middleCodeword_known_answer :
    encode publicKey.publicParam (OtsKey.ofIndex .middle 65963065) (packBytes bottomRoot)
      signature.middle.counter = some middleCodeword := by
  simp only [encode, Kernel.th_eq, Kernel.toList_append, Kernel.toList_packBytes]
  decide +kernel

/-- The middle layer's chains 0 to 21, walked to their ends. -/
theorem middleChains_0 : ∀ i : Fin V, 0 ≤ i.val → i.val < 22 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .middle 65963065) middleCodeword
      signature.middle.chainValues i = middleEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The middle layer's chains 22 to 42, walked to their ends. -/
theorem middleChains_22 : ∀ i : Fin V, 22 ≤ i.val → i.val < 43 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .middle 65963065) middleCodeword
      signature.middle.chainValues i = middleEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The middle layer's chains 43 to 63, walked to their ends. -/
theorem middleChains_43 : ∀ i : Fin V, 43 ≤ i.val → i.val < 64 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .middle 65963065) middleCodeword
      signature.middle.chainValues i = middleEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- Every chain of the middle layer, walked to its end. -/
theorem middleChains : ∀ i : Fin V,
    chainEnd publicKey.publicParam (OtsKey.ofIndex .middle 65963065) middleCodeword
      signature.middle.chainValues i = middleEnds[i] := by
  intro i
  have := i.isLt
  simp only [V] at this
  -- Each chain falls in one of the three groups.
  by_cases h22 : i.val < 22
  · exact middleChains_0 i (Nat.zero_le _) h22
  by_cases h43 : i.val < 43
  · exact middleChains_22 i (by omega) h43
  exact middleChains_43 i (by omega) (by omega)

/-- The middle key's leaf, from its chain ends. -/
theorem middleLeaf_known_answer :
    otsLeafHash publicKey.publicParam (OtsKey.ofIndex .middle 65963065) middleEnds = middleLeaf := by
  simp only [otsLeafHash, Kernel.th_eq, Kernel.toList_packDigests]
  decide +kernel

/-- The middle key's path leads from its leaf to the root of middle tree 1006. -/
theorem middleFold_known_answer :
    fold publicKey.publicParam .middle (OtsKey.ofIndex .middle 65963065).tree (OtsKey.ofIndex .middle 65963065).leaf
      middleLeaf signature.middle.path = middleRoot := by
  rw [Kernel.fold_eq]
  decide +kernel

/-- The middle layer leads to the root of middle tree 1006. -/
theorem middleLayerRoot_known_answer :
    layerRoot publicKey.publicParam .middle 65963065 (packBytes bottomRoot) signature.middle = some middleRoot :=
  layerRoot_eq middleCodeword_known_answer middleChains middleLeaf_known_answer
    middleFold_known_answer

end EthLib.Cryptography.Sphincs.KnownAnswer
