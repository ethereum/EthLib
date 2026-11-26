module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
import EthLib.Cryptography.Proofs.RandomOracleWithCoins
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proofs: two computations commute under a lazy random oracle

Two computations run against the same lazily sampled random oracle can run in either order.

Their outputs and the final cache have the same joint distribution in both orders.

They may share queries: a query that both make is answered from the cache in the second run.

So a proof may reorder the steps of a signer, as when a model signs its layers in another order.

A computation whose output is discarded then changes no other output.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

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
  -- Lifted beside the coins, the two computations commute in the random-oracle model.
  have h := run_bind_bind_comm (OracleComp.liftComp oa (unifSpec + spec₀))
    (OracleComp.liftComp ob (unifSpec + spec₀)) (fun a b ↦ pure (a, b)) cache
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    QueryImpl.simulateQ_add_liftComp_right] at h
  simpa only [bind_assoc, pure_bind] using
    (h.bind_left fun z ↦ f z.1.1 z.1.2 z.2).evalDist_eq

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

end EthLib.Cryptography.HashSig
