module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proofs: two computations commute under a lazy random oracle

Two computations run against the same lazily sampled random oracle can run in either order.

Their outputs and the final cache have the same joint distribution in both orders.

No independence is needed: a query that both make is answered from the cache in the second run.

The signer of the model signs the hypertree from the top layer and EthLib from the bottom layer.

This fact lets the bridge reorder the layers.

A computation whose output is discarded then changes no other output.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec MeasureTheory

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- Two computations against the lazy random oracle commute.

Both outputs and the final cache have the same joint distribution in either order. -/
theorem evalDist_simulateQ_run_bind_swap {α β γ : Type} [MeasurableSpace γ]
    (oa : OracleComp spec₀ α) (ob : OracleComp spec₀ β) (cache : spec₀.QueryCache)
    (f : α → β → spec₀.QueryCache → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ spec₀.randomOracle ob).run w.2 >>= fun v ↦ f w.1 v.1 v.2] =
      𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun v ↦
        (simulateQ spec₀.randomOracle oa).run v.2 >>= fun w ↦ f w.1 v.1 w.2] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rw [evalDist_bind_congr_of_support _ _ _ fun z _ ↦ ih z.1 z.2]
    exact randomOracle.evalDist_run_bind_simulateQ_run_swap t ob cache fun u b c ↦
      (simulateQ spec₀.randomOracle (k u)).run c >>= fun w ↦ f w.1 b w.2

/-- A computation whose output and cache are discarded changes nothing that follows.

The later computation's output has the same distribution with or without it. -/
theorem evalDist_simulateQ_run_bind_discard {α β γ : Type} [MeasurableSpace γ]
    (oa : OracleComp spec₀ α) (ob : OracleComp spec₀ β) (cache : spec₀.QueryCache)
    (f : β → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ spec₀.randomOracle ob).run w.2 >>= fun v ↦ f v.1] =
      𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun v ↦ f v.1] := by
  rw [evalDist_simulateQ_run_bind_swap oa ob cache fun _ b _ ↦ f b]
  exact evalDist_bind_congr_of_support _ _ _ fun v _ ↦
    (OracleComp.EvalDistEq.bind_const _ _).evalDist_eq

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
