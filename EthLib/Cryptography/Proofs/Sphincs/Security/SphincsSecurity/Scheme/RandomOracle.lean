module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Lemmas

/-!
# The lazy random oracle

This file defines the random oracle without query costs, with free uniform sampling beside it.

A lazy run of the oracle only adds answers to its cache.

Any fixed answer function that agrees with the final cache replays the run and gives its result.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SphincsSecurity.Completeness

variable [Params]

/-- Uniform sampling and the lazy random oracle, with no query cost. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

omit [Params] in
theorem simulate_lift_hash {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ romImpl (liftM oa : OracleComp OracleWorld α) = simulateQ randomOracle oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa

omit [Params] in
theorem run_lift_prob {α : Type} (oa : ProbComp α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM oa : OracleComp OracleWorld α)).run cache =
      (fun x => (x, cache)) <$> oa :=
  roSim.run_liftM _ oa cache

omit [Params] in
/-- A query to the lazy oracle records its answer and keeps every earlier answer. -/
theorem query_support_cached (input : HashInput) (cache : QueryCache HashSpec)
    (answer : HashOutput) (cache' : QueryCache HashSpec)
    (hmem : (answer, cache') ∈ support ((randomOracle (spec := HashSpec) input).run cache)) :
    cache ≤ cache' ∧ cache' input = some answer := by
  refine ⟨QueryImpl.withCaching_cache_le uniformSampleImpl input cache (answer, cache') hmem, ?_⟩
  cases hc : cache input with
  | some old =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hc
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, support_map] at hmem
      obtain ⟨sample, _, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := heq
      exact QueryCache.cacheQuery_self cache input answer

omit [Params] in
/-- An answer function that agrees with the final cache of a lazy run replays that run. -/
theorem replay_hash_support {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support ((simulateQ randomOracle oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f) :
    cache ≤ cache' ∧ evalWithAnswerFn f oa = a := by
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨le_rfl, rfl⟩
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      obtain ⟨hqueryLe, hcached⟩ := query_support_cached input cache answer cacheMid hquery
      obtain ⟨hrestLe, heval⟩ := ih answer cacheMid a cache' hrest hf
      have hfinput : f input = answer := hf (hrestLe hcached)
      refine ⟨hqueryLe.trans hrestLe, ?_⟩
      rw [evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, hfinput]
      exact heval

omit [Params] in
/-- A run that only queries the hash never deletes or changes an earlier answer. -/
theorem hash_support_cache_le {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support ((simulateQ randomOracle oa).run cache)) :
    cache ≤ cache' := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn cache'
  exact (replay_hash_support oa cache a cache' hmem f hf).1

end SphincsSecurity.Completeness
