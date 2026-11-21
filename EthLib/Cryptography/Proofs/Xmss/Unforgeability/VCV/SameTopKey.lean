module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningComponents

/-!
# Two successful replies sharing one upper one-time key

Different bottom leaf indices can have the same bottom-tree index.

Their upper signatures then authenticate the same stored bottom root.

The private randomizer, completed upper finder and disclosed upper digests all agree.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp
open ChainGraph (digestEquiv)

private theorem Stored.unique {n labels a b s} (ha : Stored (n := n) labels a s)
    (hb : Stored labels b s) : a = b := by
  apply Vector.ext
  intro i hi
  exact digestEquiv.injective (Option.some.inj ((ha ⟨i,hi⟩).symm.trans (hb ⟨i,hi⟩)))

/-- Both upper signatures and their decoded digits are identified even at different lower leaves. -/
theorem SignedFact.same_top {pp r s a b sa sb}
    (first : SignedFact pp a sa r s) (second : SignedFact pp b sb r s)
    (key : bottomTree a.leafIndex = bottomTree b.leafIndex)
    (clean : ¬ (graph pp).Conflict s) :
    sa.top = sb.top ∧ ∃ root y,
      s.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree a.leafIndex)))) =
        some (digestEquiv root) ∧
      LayerFact pp .top (bottomTree a.leafIndex) (packBytes root) sa.top y r s ∧
      LayerFact pp .top (bottomTree b.leafIndex) (packBytes root) sb.top y r s := by
  obtain ⟨_,ra,_,ya,rootA,_,upperA⟩ := first
  obtain ⟨_,rb,_,yb,rootB,_,upperB⟩ := second
  rw [← key] at rootB upperB
  obtain rfl := digestEquiv.injective (Option.some.inj (rootA.symm.trans rootB))
  have words := upperA.find.agree upperB.find clean
  obtain ⟨rho,digits⟩ := Prod.mk.inj (Option.some.inj words)
  subst yb
  have values := upperA.chains.unique upperB.chains
  have route := upperA.route.unique upperB.route
  refine ⟨?_,ra,ya,rootA,upperA,?_⟩
  · cases sa with
    | mk idx low up =>
      cases sb with
      | mk ix bot upper =>
        cases up
        cases upper
        simp_all
  · rw [← key]
    exact upperB

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
