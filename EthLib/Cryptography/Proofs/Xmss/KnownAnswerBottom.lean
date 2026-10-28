import EthLib.Cryptography.Proofs.Xmss.KnownAnswer

/-!
# Proofs: the known answer's bottom layer

The bottom key `0xA5C37E19` signs the message, and its path reaches the root of bottom tree `0xA5C3`.
-/

namespace EthLib.Cryptography.Xmss.KnownAnswer

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

set_option maxRecDepth 100000

/-- The bottom layer's digest is a codeword. -/
theorem bottomCodeword_known_answer :
    codeword? (messageDigest publicKey.publicParam .bottom (UInt32.ofNat leafIndex.toNat) (packBytes message)
      signature.bottom.randomizer) = some bottomCodeword := by
  simp only [messageDigest, Kernel.th_eq, Kernel.toList_append, Kernel.toList_packBytes]
  decide +kernel

/-- The bottom layer's chains 0 to 23, walked to their ends. -/
theorem bottomChains_0 : ∀ i : Fin V, 0 ≤ i.val → i.val < 24 →
    chainEnd publicKey.publicParam .bottom (UInt32.ofNat leafIndex.toNat) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The bottom layer's chains 24 to 43, walked to their ends. -/
theorem bottomChains_1 : ∀ i : Fin V, 24 ≤ i.val → i.val < 44 →
    chainEnd publicKey.publicParam .bottom (UInt32.ofNat leafIndex.toNat) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The bottom layer's chains 44 to 57, walked to their ends. -/
theorem bottomChains_2 : ∀ i : Fin V, 44 ≤ i.val → i.val < 58 →
    chainEnd publicKey.publicParam .bottom (UInt32.ofNat leafIndex.toNat) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- Every chain of the bottom layer, walked to its end. -/
theorem bottomChains : ∀ i : Fin V,
    chainEnd publicKey.publicParam .bottom (UInt32.ofNat leafIndex.toNat) bottomCodeword
      signature.bottom.chainValues i = bottomEnds[i] := by
  intro i
  have : (0 ≤ i.val ∧ i.val < 24)
    ∨ (24 ≤ i.val ∧ i.val < 44)
    ∨ (44 ≤ i.val ∧ i.val < 58) := by
    have := i.isLt
    simp only [V] at this
    omega
  rcases this with h | h | h
  · exact bottomChains_0 i h.1 h.2
  · exact bottomChains_1 i h.1 h.2
  · exact bottomChains_2 i h.1 h.2

/-- The bottom key's leaf, from its chain ends. -/
theorem bottomLeaf_known_answer :
    otsLeafHash publicKey.publicParam .bottom (UInt32.ofNat leafIndex.toNat) bottomEnds = bottomLeaf := by
  simp only [otsLeafHash, Kernel.th_eq, Kernel.toList_packDigests]
  decide +kernel

/-- The bottom key's path leads from its leaf to the root of bottom tree 0xA5C3. -/
theorem bottomFold_known_answer :
    fold publicKey.publicParam .bottom leafIndex.toNat bottomLeaf signature.bottom.path = bottomRoot := by
  rw [Kernel.fold_eq]
  decide +kernel

/-- The bottom layer leads to the root of bottom tree 0xA5C3. -/
theorem bottomLayerRoot_known_answer :
    layerRoot publicKey.publicParam .bottom leafIndex.toNat (packBytes message) signature.bottom = some bottomRoot :=
  layerRoot_eq bottomCodeword_known_answer bottomChains bottomLeaf_known_answer
    bottomFold_known_answer

end EthLib.Cryptography.Xmss.KnownAnswer
