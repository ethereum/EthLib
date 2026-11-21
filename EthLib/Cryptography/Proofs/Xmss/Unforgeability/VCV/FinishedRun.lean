module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinish

/-!
# Recover the actual completed finder marks from guarded execution

The public guard stops before a refused physical call.

A completed finder has both its actual preceding state and its actual ending state in the mark.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig OracleComp OracleSpec TrialGraphWatch

/-- The uncapped observer records the same finder and both states when its caller returns. -/
@[expose] noncomputable def complete (pp : PublicParam) (q : Nat) :
    QueryImpl (Ops pp) (StateT (State pp) ProbComp) := fun t => StateT.mk fun s => do
  let z ← (simulateQ (chronicle pp q) (expandCall pp t)).run s.1
  let marks := match t with
    | .inl _ => s.2
    | .inr c => ⟨c,s.1,z.1,z.2⟩ :: s.2
  return (z.1,z.2,marks)

private theorem original {pp : PublicParam} {α : Type} {q left rem s t}
    {p : OracleComp Queries α} {a : α}
    (ran : ((some a,rem),t) ∈ support
      ((((simulateQ (WeightedCap.guard fee (chronicle pp q)) p).run).run left).run s)) :
    (a,t) ∈ support ((simulateQ (chronicle pp q) p).run s) := by
  apply WeightedCap.mem_support_of_capCompOpt_some (chronicle pp q) fee p left s a t
  rw [← WeightedCap.run_guard]
  simp only [StateT.run_map, support_map]
  exact ⟨((some a,rem),t), ran,rfl⟩

private theorem complete_step {pp : PublicParam} {q left rem} (op : (Ops pp).Domain)
    (s : State pp) {a t}
    (ran : ((some a,rem),t) ∈ support (((((observeCall pp q) op).run).run left).run s)) :
    (a,t) ∈ support (((complete pp q) op).run s) := by
  simp only [observeCall, OptionT.run_mk, StateT.run_mk, mem_support_bind_iff,
    mem_support_pure_iff] at ran
  obtain ⟨⟨⟨ans,remaining⟩,st⟩, source, eq⟩ := ran
  obtain ⟨eq1,eq2⟩ := Prod.mk.inj eq
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq1
  subst t
  simp only [complete, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff]
  refine ⟨(a,st),original source,?_⟩
  cases op <;> rfl

/-- Dropping the cap on a returned path preserves the entire list of actual completed searches. -/
theorem complete_of_guard {pp : PublicParam} (q : Nat) {α : Type} (p : OracleComp (Ops pp) α)
    (left : Nat) (s : State pp) {a rem t}
    (ran : ((some a,rem),t) ∈ support ((((simulateQ (observeCall pp q) p).run).run left).run s)) :
    (a,t) ∈ support ((simulateQ (complete pp q) p).run s) := by
  induction p using OracleComp.inductionOn generalizing left s a rem t with
  | pure value =>
    simp at ran ⊢
    exact ⟨ran.1.1,ran.2⟩
  | query_bind op next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind,
      mem_support_bind_iff] at ran
    obtain ⟨⟨⟨answer,remain⟩,mid⟩,step,tail⟩ := ran
    cases answer with
    | none =>
      simp at tail
    | some x =>
      simp only at tail
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨(x,mid),complete_step op s step,ih x remain mid tail⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
