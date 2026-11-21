module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifierCut
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifierCut

/-!
# The top root in the normalized game's public key

The native key generator reads the top tree's low output row.

That label and the public key persist through the client and its final verifier.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp OracleSpec

attribute [local irreducible] simulateQ graph Xmss.verifyWith expandLocal mixedOracle

/-- The client’s public root stays in the top low row through every terminal extension. -/
theorem mixed_public_root (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (s : DeferredState) (obs : Outcome) (out : ResidualCache pp) (t : DeferredState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run s))
    (last : SharedState) (extended : t.1 ≤ last) :
    obs.key.publicParam = pp ∧ last.2 (.inr (.inl (.top,LayerGraph.treeRole LAYER_HEIGHT 0))) =
      some (ChainGraph.digestEquiv obs.key.root) := by
  obtain ⟨key, atClient, atVerifier, _, tree, client, _, verify⟩ :=
    mixed_verifier_cut pp A left r s obs out t actual
  obtain ⟨_, root⟩ := logged_of_run (pp := pp) (p := topRoot pp) tree
  have saved := logged_root_value pp .top LAYER_HEIGHT 0 root
  have suffix : atVerifier.1 ≤ t.1 := (graph pp).le_of_mem_support_simulateQ_deferredImpl _ verify
  exact ⟨key, (client.grows.trans (suffix.trans extended)).2 saved⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
