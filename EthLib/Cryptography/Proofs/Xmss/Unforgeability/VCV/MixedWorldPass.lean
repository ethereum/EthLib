module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedMixed
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedPhases

/-!
# The original adversary's public oracle under the selected cutoff

The adversary receives the full word from one physical request at any byte string.

A uniform sample remains available even with no budget for a public request.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig TwoLayerGraph Honest OracleComp OracleSpec CanonicalGraph.PairedQueries
open RandomOraclePairedValue SecretEncoding.Residual

/-- Forward the index and response type of the original adversary's query. -/
@[expose] def mixedWorldPass (pp : PublicParam) : QueryImpl World (MixedLocal pp) :=
  fun t => liftM (liftM (MixedWorld.query (.inl t)) : OracleComp MixedWorld _)

private theorem forward_chain (pp : PublicParam) (t : ChainWorld.Domain) :
    simulateQ (graph pp).eagerImpl (liftM (ChainWorld.query t) : OracleComp SharedSpec _) =
      (graph pp).eagerImpl (.inl t) := by
  have h := (graph pp).simulateQ_eagerImpl_liftComp
    (liftM (ChainWorld.query t) : OracleComp ChainWorld _)
  rw [liftComp_liftM_query, simulateQ_spec_query] at h
  exact h

/-- The two runs agree on the remaining budget, the warm graph and both local tables. -/
theorem mixed_world_pass (pp : PublicParam) (t : World.Domain) :
    SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark (fun _ => True)) (sourcePass t)))
      (mixedWorldPass pp t) := by
  intro q s
  rcases t with n | b
  · simp [sourcePass, ordinary, OracleSpec.withDerivationsLift, QueryImpl.apply_compose, mark,
      selectedImpl, selectedFee, WeightedCap.guard, mixedWorldPass, mixedImpl,
        mixedCost, rawCost, visible,
      eraseMark, inGraph, residualProgram, keyedProgram, Derivations.expand,
        SecretEncoding.reindexQueries,
      handler, expand, readHalves, liftPublic, liftComp, Functor.map_map]
    rw [forward_chain]
  · cases q with
    | zero =>
      simp [sourcePass, ordinary, OracleSpec.withDerivationsLift, QueryImpl.apply_compose, mark,
        selectedImpl, selectedFee, WeightedCap.guard, mixedWorldPass, mixedImpl,
          mixedCost, rawCost, visible]
    | succ q =>
      simp [sourcePass, ordinary, OracleSpec.withDerivationsLift, QueryImpl.apply_compose, mark,
        selectedImpl, selectedFee, WeightedCap.guard, mixedWorldPass, mixedImpl,
          mixedCost, rawCost, visible,
        eraseMark, inGraph, residualProgram, keyedProgram, Derivations.expand,
          Derivations.publicWord,
        Derivations.pair, SecretEncoding.reindexQueries, handler, expand,
          readHalves, liftPublic, liftComp,
        bind_map_left, map_bind, Functor.map_map]
      rw [forward_chain pp (.inl (.inr (.inl b)))]
      apply bind_congr
      intro lo
      rw [forward_chain pp (.inl (.inr (.inr b)))]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
