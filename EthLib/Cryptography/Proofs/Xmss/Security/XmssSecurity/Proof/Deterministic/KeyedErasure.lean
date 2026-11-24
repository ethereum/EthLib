module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Seeded.Erasure
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Deterministic.CostState

/-!
# Erasing the queries of a signer that keeps a state

A computation erases to another when it makes more queries, each extra one answered by a cache.

Erasing keeps the answers and the final cache, and can only lower the number of hash calls.

This file runs an adversary twice: with oracles that keep a state, and with oracles that keep none.

Under an invariant of the state, the two runs agree in distribution.

The second run makes at most the first's hash calls.

The calls are counted by a counter in the oracle's state, as the query bounds do.
-/

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

/-- The oracles that answer as the random oracle does and count the hash calls. -/
local notation "W" => worldHandler costHash

/-! ## Counted runs -/

/-- A counted run, its counter forgotten, is a run of the random oracle. -/
theorem mem_support_run_of_mem_support_costWorld {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (cost : Nat) {x : α × CostState}
    (hx : x ∈ support ((simulateQ W computation).run (cache, cost))) :
    (x.1, x.2.1) ∈ support ((simulateQ romImpl computation).run cache) := by
  rw [run_costWorld, support_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← countHashQueries_run_forget, support_map]
  exact ⟨y, hy, rfl⟩

/-- A counted run started `k` calls later ends `k` calls later. -/
theorem mem_support_costWorld_shift {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (cost k : Nat) {x : α × CostState}
    (hx : x ∈ support ((simulateQ W computation).run (cache, cost))) :
    (x.1, x.2.1, x.2.2 + k) ∈ support ((simulateQ W computation).run (cache, cost + k)) := by
  rw [run_costWorld, support_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, by simp only [Nat.add_right_comm]⟩

/-- A counted run of a query, then a continuation. -/
theorem run_costWorld_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (cost : Nat) :
    (simulateQ W (liftM (OracleWorld.query input) >>= next)).run (cache, cost) =
      (romImpl input).run cache >>= fun step =>
        (simulateQ W (next step.1)).run (step.2, cost + queryCost input) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, run_costQuery, bind_map_left]

/-- **A computation makes at least the hash calls of the one it erases to.**

Every counted run of the second, from a cache that knows the skipped answers, is one of the first.

The first's run has the same value and the same final cache, and at least as many calls. -/
theorem Erases.costWorld_le {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right) :
    ∀ (cache : QueryCache HashSpec), known ≤ cache → ∀ (cost : Nat) (y : α × CostState),
      y ∈ support ((simulateQ W right).run (cache, cost)) →
      ∃ x ∈ support ((simulateQ W left).run (cache, cost)),
        x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ y.2.2 ≤ x.2.2 := by
  induction h with
  | pure value =>
    intro cache _ cost y hy
    exact ⟨y, hy, rfl, rfl, le_rfl⟩
  | query input left right _ ih =>
    intro cache hcache cost y hy
    rw [run_costWorld_query_bind, mem_support_bind_iff] at hy
    obtain ⟨step, hstep, hy⟩ := hy
    obtain ⟨x, hx, h1, h2, h3⟩ := ih step.1 step.2
      (romImpl_preserves_known known cache hcache input step hstep) _ y hy
    refine ⟨x, ?_, h1, h2, h3⟩
    rw [run_costWorld_query_bind, mem_support_bind_iff]
    exact ⟨step, hstep, hx⟩
  | skip input answer hknown next right _ ih =>
    intro cache hcache cost y hy
    cases input with
    | inl input => simp [worldKnown] at hknown
    | inr input =>
      have hc : cache input = some answer := hcache hknown
      have hrun : (romImpl (.inr input)).run cache = Pure.pure (answer, cache) :=
        QueryImpl.withCaching_run_some _ hc
      obtain ⟨x, hx, h1, h2, h3⟩ := ih cache hcache cost y hy
      refine ⟨(x.1, x.2.1, x.2.2 + queryCost (.inr input)), ?_, h1, h2, h3.trans le_self_add⟩
      rw [run_costWorld_query_bind, hrun, pure_bind]
      exact mem_support_costWorld_shift _ _ _ _ hx
  | cached input answer hknown left right _ ih =>
    intro cache hcache cost y hy
    cases input with
    | inl input => simp [worldKnown] at hknown
    | inr input =>
      have hc : cache input = some answer := hcache hknown
      have hrun : (romImpl (.inr input)).run cache = Pure.pure (answer, cache) :=
        QueryImpl.withCaching_run_some _ hc
      rw [run_costWorld_query_bind, hrun, pure_bind] at hy
      obtain ⟨x, hx, h1, h2, h3⟩ := ih cache hcache _ y hy
      refine ⟨x, ?_, h1, h2, h3⟩
      rw [run_costWorld_query_bind, hrun, pure_bind]
      exact hx
  | trans _ _ first second =>
    intro cache hcache cost y hy
    obtain ⟨z, hz, h1, h2, h3⟩ := second cache hcache cost y hy
    obtain ⟨x, hx, h1', h2', h3'⟩ := first cache hcache cost z hz
    exact ⟨x, hx, h1'.trans h1, h2'.trans h2, h3.trans h3'⟩

/-- **A budget passes to a computation whose counted runs are among another's, with fewer calls.**

Both are followed by the same continuation. -/
theorem hashQueryBound_bind_of_costWorld_le {α β : Type} {first second : OracleComp OracleWorld α}
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hle : ∀ y ∈ support ((simulateQ W second).run (cache, 0)),
      ∃ x ∈ support ((simulateQ W first).run (cache, 0)),
        x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ y.2.2 ≤ x.2.2)
    (hbound : HashQueryBound (first >>= next) cache q) :
    HashQueryBound (second >>= next) cache q := by
  rw [hashQueryBound_iff_costState] at hbound ⊢
  intro y hy
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, h1, h2, h3⟩ := hle z hz
  -- The continuation runs from the first's cache, with its larger counter.
  have hshift := mem_support_costWorld_shift (next z.1) z.2.1 z.2.2 (x.2.2 - z.2.2) hy
  rw [Nat.add_sub_cancel' h3, ← h1, ← h2] at hshift
  refine le_trans le_self_add (hbound (y.1, y.2.1, y.2.2 + (x.2.2 - z.2.2)) ?_)
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨x, hx, hshift⟩

/-! ## Two simulations, one of them keeping a state -/

section Simulation

variable {ι : Type} {spec : OracleSpec ι} {σ L L' : Type} (known : QueryCache HashSpec)
  (Inv : σ → Prop)
  (implL : QueryImpl spec (StateT σ (WriterT (List L) (OracleComp OracleWorld))))
  (implR : QueryImpl spec (WriterT (List L') (OracleComp OracleWorld))) (g : L' → L)

/-- A run with a state, its state forgotten: its value and its log. -/
def forgetState {β : Type} (x : (β × σ) × List L) : β × List L :=
  (x.1.1, x.2)

/-- A run without a state, its log translated. -/
def translateLog {β : Type} (g : L' → L) (y : β × List L') : β × List L :=
  (y.1, y.2.map g)

/-- The run of a simulation with a state, from a state: its first query, then the rest. -/
theorem run_simulateQ_state_query_bind {α : Type} (q : spec.Domain)
    (k : spec.Range q → OracleComp spec α) (s : σ) :
    ((simulateQ implL (liftM (spec.query q) >>= k)).run s).run =
      ((implL q).run s).run >>= fun p =>
        (fun r => ((r.1.1, r.1.2), p.2 ++ r.2)) <$>
          ((simulateQ implL (k p.1.1)).run p.1.2).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind']
  refine bind_congr fun p => ?_
  rfl

/-- The run of a simulation without a state: its first query, then the rest. -/
theorem run_simulateQ_query_bind {α : Type} (q : spec.Domain)
    (k : spec.Range q → OracleComp spec α) :
    (simulateQ implR (liftM (spec.query q) >>= k)).run =
      (implR q).run >>= fun p =>
        (fun r => (r.1, p.2 ++ r.2)) <$> (simulateQ implR (k p.1)).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind']
  rfl

-- Take an invariant of the state.
--
-- From a state that keeps it, each query of the first erases to the same query of the second.
variable (hstep : ∀ q s, Inv s →
    Erases (worldKnown known) (forgetState <$> ((implL q).run s).run)
      (translateLog g <$> (implR q).run))
  -- After each query of the first, the new state keeps the invariant.
  (hinv : ∀ q s cache, Inv s → known ≤ cache →
    ∀ x ∈ support ((simulateQ romImpl ((implL q).run s).run).run cache), Inv x.1.1.2)

include hstep hinv

/-- **The two simulations agree in distribution.**

The value and the log agree once the state is forgotten and the second's log translated.

So does the cache after the run. -/
theorem evalDist_simulateQ_state {α : Type} (oa : OracleComp spec α) :
    ∀ (s : σ) (cache : QueryCache HashSpec), Inv s → known ≤ cache →
      (fun x => (forgetState x.1, x.2)) <$>
          (simulateQ romImpl ((simulateQ implL oa).run s).run).run cache =ᵈ
        (fun y => (translateLog g y.1, y.2)) <$>
          (simulateQ romImpl (simulateQ implR oa).run).run cache := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s cache _ _
    simp [forgetState, translateLog]
  | query_bind q k ih =>
    intro s cache hs hcache
    rw [run_simulateQ_state_query_bind, run_simulateQ_query_bind]
    -- Each side is its first query, then the same continuation of what the query returned.
    let F : spec.Range q × List L × QueryCache HashSpec →
        ProbComp ((α × List L) × QueryCache HashSpec) := fun a =>
      (fun y => ((y.1.1, a.2.1 ++ (y.1.2.map g)), y.2)) <$>
        (simulateQ romImpl (simulateQ implR (k a.1)).run).run a.2.2
    have hleft : (fun x => (forgetState x.1, x.2)) <$> (simulateQ romImpl
        (((implL q).run s).run >>= fun p => (fun r => ((r.1.1, r.1.2), p.2 ++ r.2)) <$>
          ((simulateQ implL (k p.1.1)).run p.1.2).run)).run cache =ᵈ
        ((fun z => (z.1.1.1, z.1.2, z.2)) <$>
          (simulateQ romImpl ((implL q).run s).run).run cache) >>= F := by
      simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
        bind_map_left, Functor.map_map]
      refine OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => ?_
      have h := (ih z.1.1.1 z.1.1.2 z.2 (hinv q s cache hs hcache z hz)
        (hcache.trans (xmssRom_cache_le _ _ _ hz))).map
        (fun p => ((p.1.1, z.1.2 ++ p.1.2), p.2))
      simp only [Functor.map_map, forgetState, translateLog] at h ⊢
      exact h
    have hright : (fun y => (translateLog g y.1, y.2)) <$> (simulateQ romImpl
        ((implR q).run >>= fun p => (fun r => (r.1, p.2 ++ r.2)) <$>
          (simulateQ implR (k p.1)).run)).run cache =
        ((fun z => (z.1.1, z.1.2.map g, z.2)) <$>
          (simulateQ romImpl (implR q).run).run cache) >>= F := by
      simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
        bind_map_left, Functor.map_map, F, translateLog, List.map_append]
    rw [hright]
    refine hleft.trans (EvalDistEq.bind_left ?_ F)
    -- The first queries agree, by the erasure of the first query.
    have hrun := (hstep q s hs).evalDist_run cache hcache
    simp only [simulateQ_map, StateT.run_map] at hrun
    have h := hrun.map (fun z => (z.1.1, z.1.2, z.2))
    simp only [Functor.map_map, forgetState, translateLog] at h
    exact h

/-- **The simulation without a state makes at most the other's hash calls.**

Every counted run of the second is one of the first, with the same value, log and cache.

The first's run has at least as many calls. -/
theorem costWorld_le_simulateQ_state {α : Type} (oa : OracleComp spec α) :
    ∀ (s : σ) (cache : QueryCache HashSpec), Inv s → known ≤ cache → ∀ (cost : Nat)
      (y : (α × List L') × CostState),
      y ∈ support ((simulateQ W (simulateQ implR oa).run).run (cache, cost)) →
      ∃ x ∈ support ((simulateQ W ((simulateQ implL oa).run s).run).run (cache, cost)),
        forgetState x.1 = translateLog g y.1 ∧ x.2.1 = y.2.1 ∧ y.2.2 ≤ x.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s cache _ _ cost y hy
    simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨(((a, s), []), (cache, cost)), ?_, rfl, rfl, le_rfl⟩
    simp
  | query_bind q k ih =>
    intro s cache hs hcache cost y hy
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    rw [simulateQ_map, StateT.run_map, support_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    -- The first query: the stateful oracle makes at least the calls of the other.
    have hzmap : (translateLog g z.1, z.2) ∈ support ((simulateQ W
        (translateLog g <$> (implR q).run)).run (cache, cost)) := by
      rw [simulateQ_map, StateT.run_map, support_map]
      exact ⟨z, hz, rfl⟩
    obtain ⟨x0, hx0, h01, h02, h03⟩ :=
      (hstep q s hs).costWorld_le cache hcache cost _ hzmap
    rw [simulateQ_map, StateT.run_map, support_map] at hx0
    obtain ⟨p, hp, rfl⟩ := hx0
    have hrom := mem_support_run_of_mem_support_costWorld _ _ _ hp
    have hs' : Inv p.1.1.2 := hinv q s cache hs hcache (p.1, p.2.1) hrom
    have hcache' : known ≤ p.2.1 := hcache.trans (xmssRom_cache_le _ _ _ hrom)
    -- The rest: the run of the second from the first's cache, then shifted to its counter.
    simp only [forgetState, translateLog, Prod.mk.injEq] at h01
    obtain ⟨hu, hl⟩ := h01
    have hy'' : y' ∈ support ((simulateQ W (simulateQ implR (k p.1.1.1)).run).run
        (p.2.1, z.2.2)) := by
      rw [hu, h02]
      exact hy'
    obtain ⟨x, hx, h1, h2, h3⟩ := ih p.1.1.1 p.1.1.2 p.2.1 hs' hcache' _ y' hy''
    have hshift := mem_support_costWorld_shift _ _ _ (p.2.2 - z.2.2) hx
    rw [Nat.add_sub_cancel' h03] at hshift
    refine ⟨((((x.1.1.1, x.1.1.2), p.1.2 ++ x.1.2)), x.2.1, x.2.2 + (p.2.2 - z.2.2)), ?_, ?_,
      h2, h3.trans le_self_add⟩
    · rw [run_simulateQ_state_query_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      refine ⟨p, hp, ?_⟩
      rw [simulateQ_map, StateT.run_map, support_map]
      exact ⟨_, hshift, rfl⟩
    · simp only [forgetState, translateLog, Prod.mk.injEq] at h1 ⊢
      exact ⟨h1.1, by rw [hl, h1.2, List.map_append]⟩

end Simulation

end XmssSecurity.Seeded
