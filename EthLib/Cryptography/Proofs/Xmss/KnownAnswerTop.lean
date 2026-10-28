import EthLib.Cryptography.Proofs.Xmss.KnownAnswer

/-!
# Proofs: the known answer's top layer

The top key `0xA5C3` signs the root of bottom tree `0xA5C3`, and its path reaches the key's root.
-/

namespace EthLib.Cryptography.Xmss.KnownAnswer

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

set_option maxRecDepth 100000

/-- The top layer's digest is a codeword. -/
theorem topCodeword_known_answer :
    codeword? (messageDigest publicKey.publicParam .top (UInt32.ofNat (bottomTree leafIndex)) (packBytes bottomRoot)
      signature.top.randomizer) = some topCodeword := by
  simp only [messageDigest, Kernel.th_eq, Kernel.toList_append, Kernel.toList_packBytes]
  decide +kernel

/-- The top layer's chains 0 to 22, walked to their ends. -/
theorem topChains_0 : ∀ i : Fin V, 0 ≤ i.val → i.val < 23 →
    chainEnd publicKey.publicParam .top (UInt32.ofNat (bottomTree leafIndex)) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The top layer's chains 23 to 38, walked to their ends. -/
theorem topChains_1 : ∀ i : Fin V, 23 ≤ i.val → i.val < 39 →
    chainEnd publicKey.publicParam .top (UInt32.ofNat (bottomTree leafIndex)) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- The top layer's chains 39 to 57, walked to their ends. -/
theorem topChains_2 : ∀ i : Fin V, 39 ≤ i.val → i.val < 58 →
    chainEnd publicKey.publicParam .top (UInt32.ofNat (bottomTree leafIndex)) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  simp only [chainEnd, Kernel.chain_eq]
  decide +kernel

/-- Every chain of the top layer, walked to its end. -/
theorem topChains : ∀ i : Fin V,
    chainEnd publicKey.publicParam .top (UInt32.ofNat (bottomTree leafIndex)) topCodeword
      signature.top.chainValues i = topEnds[i] := by
  intro i
  have : (0 ≤ i.val ∧ i.val < 23)
    ∨ (23 ≤ i.val ∧ i.val < 39)
    ∨ (39 ≤ i.val ∧ i.val < 58) := by
    have := i.isLt
    simp only [V] at this
    omega
  rcases this with h | h | h
  · exact topChains_0 i h.1 h.2
  · exact topChains_1 i h.1 h.2
  · exact topChains_2 i h.1 h.2

/-- The top key's leaf, from its chain ends. -/
theorem topLeaf_known_answer :
    otsLeafHash publicKey.publicParam .top (UInt32.ofNat (bottomTree leafIndex)) topEnds = topLeaf := by
  simp only [otsLeafHash, Kernel.th_eq, Kernel.toList_packDigests]
  decide +kernel

/-- The top key's path leads from its leaf to the key's root. -/
theorem topFold_known_answer :
    fold publicKey.publicParam .top (bottomTree leafIndex) topLeaf signature.top.path = publicKey.root := by
  rw [Kernel.fold_eq]
  decide +kernel

/-- The top layer leads to the key's root. -/
theorem topLayerRoot_known_answer :
    layerRoot publicKey.publicParam .top (bottomTree leafIndex) (packBytes bottomRoot) signature.top = some publicKey.root :=
  layerRoot_eq topCodeword_known_answer topChains topLeaf_known_answer
    topFold_known_answer

end EthLib.Cryptography.Xmss.KnownAnswer
