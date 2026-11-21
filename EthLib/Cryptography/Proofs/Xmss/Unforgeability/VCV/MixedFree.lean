module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedMixed

/-!
# Uncharged computations inside the normalized cutoff

The same law applies to private residual draws and to structural graph touches.

The mixed source explicitly identifies every issued query as a zero-cost query.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig TwoLayerGraph Honest OracleComp OracleSpec CanonicalGraph.PairedQueries

/-- A zero-cost mixed interpreter can replace a local eager computation at any remaining budget. -/
theorem mixed_free {α : Type} (pp : PublicParam) (p : WithLocal (ResidualCache pp) α)
    (m : MixedLocal pp α)
    (free : ∀ r, (m.run r).AllQueriesSatisfy (fun t => mixedCost (H := ChainGraph.Word)
      (F := HashOutput) (fun _ => 0) t = 0))
    (image : ∀ r, simulateQ (graph pp).eagerImpl (p.run r) =
      simulateQ (graph pp).eagerImpl (simulateQ (expand PairedHashWord.halves) (m.run r))) :
    SameMixed pp (liftM p) m := by
  intro q r
  rw [mixedImpl, WeightedCap.run_guard_free _ _ _ q (free r)]
  simp only [OptionT.run_monadLift, StateT.run_map, StateT.run_monadLift, monadLift_self,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure, simulateQ_map]
  rw [← image r]
  simp [visible]

/-- A source tick and its uncharged mixed lookup have the same complete state. -/
theorem selected_mixed_tick (pp : PublicParam) :
    SameMixed pp (liftM (inGraph pp sourceTick)) (mixedTick pp) := by
  apply mixed_free pp _ _ (mixedTick_free pp)
  intro r
  exact congrArg (simulateQ (graph pp).eagerImpl) (expand_tick pp r).symm

/-- The local seed table supplies both halves of the same physical randomizer. -/
theorem selected_mixed_randomizer (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    SameMixed pp (liftM (graphPrf pp pp (addrRnd l e) msg)) (mixedRandomizer pp l e msg) := by
  apply mixed_free pp _ _ (mixedRandomizer_free pp l e msg)
  intro r
  exact congrArg (simulateQ (graph pp).eagerImpl) (expand_randomizer pp l e msg r).symm

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
