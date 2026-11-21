module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistrations
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RepeatedSearch

/-!
# The physical graph accompanying a chronological signer

Projection preserves both the residual output and shared graph of a completed stage.

The shared graph can only extend through later actions.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp CachedCodeword TrialGraphWatch TwoLayerGraph

@[expose] def physical (s : JointState) : D := s.1.1.1.1.1

/-- Projection preserves the physical mixed transition and its inputs and outputs. -/
protected theorem Ran.project {pp q} {α : Type} {p : Program pp α} {r s a out t}
    (ran : Ran q p r s a out t) : MixedRun (deferredMixed pp) (forget p) r
      (physical s.1) a out (physical t.1) := by
  have view := project_counts pp q (p.run r) s
  have graph := erase_run pp register (fun z b => (target pp z b).isSome) q
    (fun w => (digits w).isSome)
    (p.run r) (counters s)
  rw [← view] at graph
  unfold MixedRun deferredMixed forget
  rw [QueryImpl.simulateQ_compose]
  change _ ∈ support ((simulateQ (TwoLayerGraph.graph pp).deferredImpl
    (simulateQ (CanonicalGraph.PairedQueries.expand PairedHashWord.halves)
      (simulateQ erase (p.run r)))).run (counters s).1.1.1)
  rw [← graph, support_map, support_map]
  exact ⟨_, ⟨_, ran, rfl⟩, rfl⟩

/-- Every real signer prefix extends the full public and labeled graph stores. -/
protected theorem Ran.graph_mono {pp q} {α : Type} {p : Program pp α} {r s a out t}
    (ran : Ran q p r s a out t) : (physical s.1).1 ≤ (physical t.1).1 := by
  have seen := ran.project
  unfold MixedRun deferredMixed at seen
  rw [QueryImpl.simulateQ_compose] at seen
  exact (graph pp).le_of_mem_support_simulateQ_deferredImpl _ seen

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
