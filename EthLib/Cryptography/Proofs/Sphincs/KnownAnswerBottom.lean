import EthLib.Cryptography.Proofs.Sphincs.KnownAnswer

/-!
# Proofs: the known answer's bottom layer

The bottom key signs the FORS key, and its path reaches the root of bottom tree 257668.
-/

namespace EthLib.Cryptography.Sphincs.KnownAnswer

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

set_option maxRecDepth 100000

/-- The bottom layer's counter encodes its message as a codeword. -/
theorem bottomCodeword_known_answer :
    encode publicKey.publicParam (OtsKey.ofIndex .bottom 65963065) (forsKeyBytes forsKey)
      signature.bottom.counter = some bottomCodeword := by
  simp only [encode, forsKeyBytes, Kernel.th_eq, Kernel.toList_append, Kernel.toList_packBytes,
    Kernel.toList_packDigests]
  decide +kernel

/-- The bottom layer's chains 0 to 21, walked to their ends. -/
theorem bottomChains_0 : ∀ i : Fin V, 0 ≤ i.val → i.val < 22 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .bottom 65963065) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The bottom layer's chains 22 to 42, walked to their ends. -/
theorem bottomChains_22 : ∀ i : Fin V, 22 ≤ i.val → i.val < 43 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .bottom 65963065) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The bottom layer's chains 43 to 63, walked to their ends. -/
theorem bottomChains_43 : ∀ i : Fin V, 43 ≤ i.val → i.val < 64 →
    chainEnd publicKey.publicParam (OtsKey.ofIndex .bottom 65963065) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- Every chain of the bottom layer, walked to its end. -/
theorem bottomChains : ∀ i : Fin V,
    chainEnd publicKey.publicParam (OtsKey.ofIndex .bottom 65963065) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  intro i
  have := i.isLt
  simp only [V] at this
  -- Each chain falls in one of the three groups.
  by_cases h22 : i.val < 22
  · exact bottomChains_0 i (Nat.zero_le _) h22
  by_cases h43 : i.val < 43
  · exact bottomChains_22 i (by omega) h43
  exact bottomChains_43 i (by omega) (by omega)

/-- The bottom key's leaf, from its chain ends. -/
theorem bottomLeaf_known_answer :
    otsLeafHash publicKey.publicParam (OtsKey.ofIndex .bottom 65963065) bottomEnds = bottomLeaf := by
  simp only [otsLeafHash, Kernel.th_eq, Kernel.toList_packDigests]
  decide +kernel

/-- The bottom key's path leads from its leaf to the root of bottom tree 257668. -/
theorem bottomFold_known_answer :
    fold publicKey.publicParam .bottom (OtsKey.ofIndex .bottom 65963065).tree (OtsKey.ofIndex .bottom 65963065).leaf
      bottomLeaf signature.bottom.path = bottomRoot := by
  rw [Kernel.fold_eq]
  decide +kernel

/-- The bottom layer leads to the root of bottom tree 257668. -/
theorem bottomLayerRoot_known_answer :
    layerRoot publicKey.publicParam .bottom 65963065 (forsKeyBytes forsKey) signature.bottom = some bottomRoot :=
  layerRoot_eq bottomCodeword_known_answer bottomChains bottomLeaf_known_answer
    bottomFold_known_answer

end EthLib.Cryptography.Sphincs.KnownAnswer
