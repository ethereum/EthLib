module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphCalls
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphCap
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.StatefulPairs

/-!
# The local state of the actual graph continuation

The paid source splits a single physical call into its two graph rows after the cap has admitted it.

An ordinary public call and a private chain-start pair leave the two local caches in place.

The parameter and message randomizer share the local derivation table throughout the actual run.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig TwoLayerGraph OracleSpec OracleComp Constants
open SecretEncoding.Residual RandomOraclePairedValue
open Classical

/-- Interpret each physical source call using the split graph and the residual caches. -/
@[expose] noncomputable def inGraph {α : Type} (pp : PublicParam) (body : OracleComp Source α) :
    Honest.WithLocal (ResidualCache pp) α :=
  StateT.mk fun extra => liftComp (residualProgram pp body extra) Honest.SharedSpec

theorem inGraph_pure {α : Type} (pp : PublicParam) (a : α) : inGraph pp (pure a) = pure a := by
  ext extra : 1
  simp [inGraph, residualProgram, keyedProgram, liftComp]

theorem inGraph_bind {α β : Type} (pp : PublicParam) (body : OracleComp Source α)
    (next : α → OracleComp Source β) :
    inGraph pp (body >>= next) = inGraph pp body >>= fun a => inGraph pp (next a) := by
  ext extra : 1
  simp only [inGraph, StateT.run_mk, keyedProgram, residualProgram, simulateQ_bind, StateT.run_bind,
      liftComp]

private theorem inGraph_map {α β : Type} (pp : PublicParam) (f : α →
    β) (body : OracleComp Source α) :
    inGraph pp (f <$> body) = f <$> inGraph pp body := by
  simp only [← bind_pure_comp, inGraph_bind, inGraph_pure]

/-- The actual full PRF word lives in this single stateful handler at both layers. -/
@[expose] noncomputable def graphPrf (pp : PublicParam) : SeedPrf (Honest.WithLocal
    (ResidualCache pp)) :=
  fun p a d => inGraph pp (sourcePrf p a d)

/-- The fallback is never called at the paired start addresses. -/
@[expose] def emptyPrf : SeedPrf (OracleComp LayerGraph.Spec) := fun _ _ _ =>
    pure (Vector.replicate 32 0)

/-- The two real forwarded halves supply precisely the pair assumption of the graph tree proof. -/
theorem graphPrf_pairs (pp : PublicParam) (l : Layer) :
    Honest.LocalPairs pp l (graphPrf pp) (Honest.prf pp l emptyPrf) := by
  intro e j
  ext extra : 1
  rw [Honest.prf_pair pp l emptyPrf e j]
  simp only [graphPrf, sourcePrf, inGraph_map]
  simp only [StateT.run_map, inGraph, StateT.run_mk]
  rw [residual_pair]
  simp [liftComp, readCell, map_bind, Functor.map_map]
  rfl

/-- Each public word uses the shared verifier hash and preserves both local caches. -/
theorem inGraph_hash (pp : PublicParam) (b : ByteArray) :
    inGraph pp (hashOf sourcePass b) = liftM (Honest.hash b) := by
  ext extra : 1
  simp [hashOf, sourcePass, ordinary, OracleSpec.withDerivationsLift, QueryImpl.apply_compose,
    inGraph, residualProgram, keyedProgram, Derivations.expand, Derivations.pair,
    Derivations.publicWord, SecretEncoding.reindexQueries, handler, Honest.hash, liftComp,
    map_bind, Functor.map_map]
  rfl

/-- This interpreter preserves the branch, both local tables and both graph tables. -/
theorem evaluate_inGraph {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (extra : ResidualCache pp) (st : Honest.SharedState) :
    evaluate pp (graph pp) body extra st =
      (simulateQ (graph pp).eagerImpl ((inGraph pp body).run extra)).run st := by
  unfold evaluate inGraph
  rw [Subsingleton.elim (fun a b : Row =>
      Classical.propDecidable (a = b)) (inferInstance : DecidableEq Row)]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
