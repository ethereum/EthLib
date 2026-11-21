module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedCap
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualSchedule
public import VCVio.OracleComp.QueryTracking.WeightedCap.Handler

/-!
# The selected physical cutoff on the shared graph

An admitted marked request spends one unit before reading either public row.

A refused request keeps the residual and graph tables from its completed prefix.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec HashSig TwoLayerGraph SecretEncoding.Residual

abbrev Selected (pp : PublicParam) := OptionT (StateT Nat (Honest.WithLocal (ResidualCache pp)))

/-- Run each admitted physical word through its original residual and shared tables. -/
@[expose] noncomputable def selectedImpl (pp : PublicParam) : QueryImpl Marked (Selected pp) :=
  WeightedCap.guard selectedFee (fun t => inGraph pp (eraseMark t))

private theorem interpret {α : Type} (pp : PublicParam) (body : OracleComp Marked α) :
    simulateQ (fun t => inGraph pp (eraseMark t)) body =
      inGraph pp (simulateQ eraseMark body) := by
  induction body using OracleComp.inductionOn with
  | pure a => simp [inGraph_pure]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, inGraph_bind, ih]

/-- This identity retains the complete four-table state even when the cap refuses a query. -/
theorem selected_run {α : Type} (pp : PublicParam) (body : OracleComp Marked α) (q : Nat) :
    Prod.fst <$> ((simulateQ (selectedImpl pp) body).run).run q =
      inGraph pp (simulateQ eraseMark (WeightedCap.capCompOpt selectedFee q body)) := by
  rw [selectedImpl, WeightedCap.run_guard, interpret]

attribute [local irreducible] markedContinuation inGraph evaluate

/-- The guarded execution is the actual marked game at the sampled public parameter. -/
theorem markedRun_guard (A : Adversary) (q : Nat) (w : HashOutput) :
    let pp := parameterOfWord w
    let extra := localState _ _ (toKeyedState pp (afterWord w))
    let guarded := simulateQ (selectedImpl pp) (markedContinuation A pp)
    markedRun A q w =
      (simulateQ (graph pp).eagerImpl ((Prod.fst <$> (guarded.run.run q)).run extra)).run
        (∅, ∅) := by
  dsimp only
  rw [selected_run, markedRun, runGraph, evaluate_inGraph]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
