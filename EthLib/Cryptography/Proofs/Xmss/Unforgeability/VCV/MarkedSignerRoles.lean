module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSource
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerValues
public import EthLib.Cryptography.Proofs.Xmss.Ots

/-!
# The two public hash ports of honest signing

The address fixes the port even when an adversary chose the message.

Every native authentication node and chain uses the uncharged port.

Every finder trial uses the charged port, including trials that reject.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleSpec OracleComp Constants TwoLayerGraph.Honest

noncomputable abbrev signingHash (b : ByteArray) :=
  simulateQ (mark IsTrial) (hashOf sourcePass b)

private theorem chainStep_eq (pp : PublicParam) (l : Layer) (e : UInt32) (i : Fin V) :
    chainStep signingHash pp l e i = chainStep markedChainHash pp l e i := by
  funext mu value
  unfold chainStep th signingHash
  rw [chain_hash]

theorem signing_chain (pp : PublicParam) (l : Layer) (e : UInt32) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (v : Digest) :
    chain signingHash pp l e i start steps h v =
      chain markedChainHash pp l e i start steps h v := by
  unfold chain
  rw [chainStep_eq]

theorem signing_values (cb : SeedPrf (OracleComp Marked)) (pp : PublicParam) (l : Layer)
    (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    chainValues signingHash cb pp l e x = chainValues markedChainHash cb pp l e x := by
  simp only [chainValues, signing_chain]

private theorem signing_leaf (pp : PublicParam) (cb : SeedPrf (OracleComp Marked)) (l : Layer) :
    leaves signingHash pp cb l = leaves markedChainHash pp cb l := by
  funext j
  simp only [leaves, otsPublicLeaf, otsLeafHash, th, signing_chain, signingHash, leaf_hash]

private theorem signing_nodeHash (pp : PublicParam) (l : Layer) :
    nodeHash signingHash pp l = nodeHash markedChainHash pp l := by
  funext p left right
  simp only [nodeHash, th, signingHash, node_hash]

theorem signing_build (pp : PublicParam) (cb : SeedPrf (OracleComp Marked))
    (l : Layer) (h j : Nat) :
    build signingHash pp cb l h j = build markedChainHash pp cb l h j := by
  rw [build, signing_nodeHash, signing_leaf, build]

theorem signing_path (pp : PublicParam) (cb : SeedPrf (OracleComp Marked)) (l : Layer) (e : Nat) :
    path signingHash pp cb l e = path markedChainHash pp cb l e := by
  rw [path, signing_nodeHash, signing_leaf, path]

theorem signing_finder (pp : PublicParam) (l : Layer) (e : UInt32) (b : ByteArray)
    (rnd : Randomizer) (c fuel : Nat) :
    Xmss.Internal.findCodeword signingHash pp l e b rnd c fuel =
      Xmss.Internal.findCodeword markedFindHash pp l e b rnd c fuel := by
  simp only [Xmss.Internal.findCodeword_eq, messageDigest, th, signingHash, trial_hash]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
