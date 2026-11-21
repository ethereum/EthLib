module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphBudget

/-!
# Erasing trial notices at the physical cutoff

Registration and counters observe the same sequence of graph operations as the normalized caller.

Free notices survive a zero budget until the next paid full word is refused.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch

open OracleComp OracleSpec HashSig TwoLayerGraph CanonicalGraph.PairedQueries
open ChainGraph (Word Public)

/-- A raw graph operation keeps its original fee. A notice costs zero. -/
@[expose] def fee {Note : Type} : (Spec Note).Domain → Nat :=
  Sum.elim (mixedCost (H := Word) (F := HashOutput) (fun _ => 0)) (fun _ => 0)

/-- Erasing a notice returns unit before resuming the same adaptive caller. -/
@[expose] def erase {Note : Type} : QueryImpl (Spec Note) (OracleComp Raw) :=
  Sum.rec (fun t => liftM (Raw.query t)) (fun _ => pure ())

/-- Dropping the notices commutes with the original cutoff, also when that cutoff returns none. -/
theorem erase_cap {Note α : Type} (p : OracleComp (Spec Note) α) (q : Nat) :
    simulateQ erase (WeightedCap.capCompOpt fee q p) =
      WeightedCap.capCompOpt (mixedCost (H := Word) (F := HashOutput) (fun _ =>
        0)) q (simulateQ erase p) := by
  induction p using OracleComp.inductionOn generalizing q with
  | pure a => simp [WeightedCap.capCompOpt_pure]
  | query_bind t k ih =>
    cases t with
    | inl t =>
      have eff : fee (Note := Note) (.inl t) = mixedCost (H := Word) (F := HashOutput) (fun _ =>
        0) t := rfl
      by_cases room : mixedCost (H := Word) (F := HashOutput) (fun _ => 0) t ≤ q <;>
        simp [WeightedCap.capCompOpt_query_bind, simulateQ_bind, erase, eff, room, ih]
    | inr n =>
      have eff : fee (Note := Note) (.inr n) = 0 := rfl
      simp [WeightedCap.capCompOpt_query_bind, simulateQ_bind, erase, eff, ih]

/-- Dropping all counters and registration data retains the exact output and whole deferred state.
-/
theorem erase_run {Note R α : Type} (pp : PublicParam) (notice : Note → R → R)
    (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool)
    (p : OracleComp (Spec Note) α) (s : Observed R) :
    Prod.map id (fun t : Observed R =>
      t.1.1.1) <$> (simulateQ (observe pp notice registered q test) p).run s =
      (simulateQ (graph pp).deferredImpl (simulateQ (expand PairedHashWord.halves)
        (simulateQ erase p))).run s.1.1.1 := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply map_run_simulateQ_eq_of_query_map_eq
  rintro (t | n) h
  · simp [observe, withPost, BernoulliMoment.observe, base, QueryImpl.extendState_apply, erase,
      QueryImpl.compose, bind_pure_comp, Functor.map_map]
  · simp [observe, withPost, BernoulliMoment.observe, base, QueryImpl.extendState_apply, erase,
      QueryImpl.compose]

/--
Pre-sign trials, paid post-sign trials, and graph or seed inputs share one selected physical budget.

No successful return and no absence of conflict are required.
-/
theorem total_budget {Note R α : Type} (pp : PublicParam) (notice : Note → R → R)
    (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool)
    (body : OracleComp (Spec Note) α) (left : Nat) (reg : R) {z}
    (ran : z ∈ support ((simulateQ (observe pp notice registered q test)
      (WeightedCap.capCompOpt fee left body)).run (((((∅, ∅), []), reg), 0), 0, 0))) :
    let c := z.2.1.1.1.1.1
    (addressedInputs pp c).encard + ((z.2.1.2 : ℕ∞) + z.2.2.1) + (seedInputs c).encard ≤ left := by
  have priced := fits_run pp notice registered q test _ reg ran
  have proj := erase_run pp notice registered q test (WeightedCap.capCompOpt fee left body)
    (((((∅, ∅), []), reg), 0), 0, 0)
  rw [erase_cap] at proj
  have selected : (z.1, z.2.1.1.1) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left (simulateQ erase body))).run ((∅, ∅), [])) := by
    unfold guardedGraph
    rw [← proj, support_map]
    exact ⟨z, ran, rfl⟩
  exact (add_le_add (add_le_add le_rfl priced) le_rfl).trans (normalized_path pp left _ selected).1

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch
