import EthLib.Cryptography.Proofs.Sphincs.KnownAnswer

/-!
# Proofs: the known answer's top layer

The top key signs the middle root, and its path reaches the root of the top tree.
-/

namespace EthLib.Cryptography.Sphincs.KnownAnswer

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

set_option maxRecDepth 100000

/-- The top layer's counter encodes its message as a codeword. -/
theorem topCodeword_known_answer :
    encode publicKey.publicParam (OtsKey.ofIndex .top 65963065) (packBytes middleRoot)
      signature.top.counter = some topCodeword := by
  simp only [encode, Kernel.th_eq, Kernel.toList_append, Kernel.toList_packBytes]
  decide +kernel

/-- The top layer's chains 0 to 21, walked to their ends. -/
theorem topChains_0 : ∀ i : Fin V, 0 ≤ i.val → i.val < 22 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .top 65963065) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The top layer's chains 22 to 42, walked to their ends. -/
theorem topChains_22 : ∀ i : Fin V, 22 ≤ i.val → i.val < 43 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .top 65963065) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The top layer's chains 43 to 63, walked to their ends. -/
theorem topChains_43 : ∀ i : Fin V, 43 ≤ i.val → i.val < 64 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .top 65963065) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- Every chain of the top layer, walked to its end. -/
theorem topChains : ∀ i : Fin V,
    chainEnd publicKey.publicParam (OtsKey.ofIndex .top 65963065) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  intro i
  have := i.isLt
  simp only [V] at this
  -- Each chain falls in one of the three groups.
  by_cases h22 : i.val < 22
  · exact topChains_0 i (Nat.zero_le _) h22
  by_cases h43 : i.val < 43
  · exact topChains_22 i (by omega) h43
  exact topChains_43 i (by omega) (by omega)

/-- The top key's leaf, from its chain ends. -/
theorem topLeaf_known_answer :
    otsLeafHash publicKey.publicParam (OtsKey.ofIndex .top 65963065) topEnds = topLeaf := by
  simp only [otsLeafHash, Kernel.th_eq, Kernel.toList_packDigests]
  decide +kernel

/-- The top key's path leads from its leaf to the root of the top tree. -/
theorem topFold_known_answer :
    fold publicKey.publicParam .top (OtsKey.ofIndex .top 65963065).tree (OtsKey.ofIndex .top 65963065).leaf
      topLeaf signature.top.path = topRoot := by
  rw [Kernel.fold_eq]
  decide +kernel

/-- The top layer leads to the root of the top tree. -/
theorem topLayerRoot_known_answer :
    layerRoot publicKey.publicParam .top 65963065 (packBytes middleRoot) signature.top = some topRoot :=
  layerRoot_eq topCodeword_known_answer topChains topLeaf_known_answer
    topFold_known_answer

end EthLib.Cryptography.Sphincs.KnownAnswer
