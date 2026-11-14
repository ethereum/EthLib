/- Authors: Matthias Meijers -/

module

public import EthereumXMSSHypertree.HypertreePRF
import all HashSig.GXMSS.Hypertree.PRFDerivedScheme

/-!
# Full-response cache transport for the actual paired-counter queries

Restricting a persistent byte-input cache along the proved injective query map
preserves the complete response and final cache for every adaptive client.
All 32 bytes are retained, so a repeated grouped request retains both halves.
-/

public section

namespace EthereumXMSSHypertree.HypertreeCache

open EthLib.Cryptography.Xmss OracleComp OracleSpec HypertreePRF

/-- Equality of actual paired-counter requests is decided without enumerating their domain. -/
noncomputable instance queryDecidableEq : DecidableEq Query := Classical.decEq _

/-- The complete-response cache at the reviewed generic paired-counter query domain. -/
abbrev Cache := (Query →ₒ FullResponse).QueryCache

/-- Restrict one persistent source byte cache to every actual paired-counter input. -/
@[expose]
def restrictCache (seed : Seed) (cache : ByteCache) : Cache :=
  QueryCache.ofFn fun query => cache (queryInput seed query)

/-- Restriction reads the entire original response at every actual encoded query. -/
@[simp]
theorem restrictCache_apply (seed : Seed) (cache : ByteCache) (query : Query) :
    restrictCache seed cache query = cache (queryInput seed query) := rfl

/-- Empty byte caches restrict to empty actual-query caches. -/
@[simp]
theorem restrictCache_empty (seed : Seed) : restrictCache seed ∅ = ∅ := by
  ext query
  simp

/-- Injectivity makes insertion of one complete response commute with cache restriction. -/
theorem restrictCache_insert (seed : Seed) (cache : ByteCache) (query : Query)
    (response : FullResponse) :
    restrictCache seed (cache.cacheQuery (queryInput seed query) response) =
      (restrictCache seed cache).cacheQuery query response := by
  ext other
  by_cases h : other = query
  · subst other
    simp
  · have hinput := (queryInput_injective seed).ne h
    simp [QueryCache.cacheQuery_of_ne, h, hinput]

/-- Answer the actual generic queries at their exact source byte inputs. -/
@[expose]
def answers {m : Type → Type}
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed) :
    QueryImpl (Query →ₒ FullResponse) m := fun query => draw (queryInput seed query)

/-- Route each actual generic query through the persistent full-response byte cache. -/
@[expose]
def routed {m : Type → Type} [Monad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed) :
    QueryImpl (Query →ₒ FullResponse) (StateT ByteCache m) :=
  fun query => draw.withCaching (queryInput seed query)

/-- One routed query preserves its complete output and restricted final cache. -/
theorem routed_projection {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed)
    (query : Query) (cache : ByteCache) :
    Prod.map id (restrictCache seed) <$> (routed draw seed query).run cache =
      ((answers draw seed).withCaching query).run (restrictCache seed cache) := by
  change Prod.map id (restrictCache seed) <$>
    (draw.withCaching (queryInput seed query)).run cache = _
  cases h : cache (queryInput seed query) with
  | none =>
    rw [QueryImpl.withCaching_run_none draw h,
      QueryImpl.withCaching_run_none _ (show restrictCache seed cache query = none from h)]
    simp only [Functor.map_map, Prod.map_apply, id_eq, restrictCache_insert, answers]
  | some response =>
    rw [QueryImpl.withCaching_run_some draw h,
      QueryImpl.withCaching_run_some _
        (show restrictCache seed cache query = some response from h)]
    simp

/-- Any adaptive client preserves its full output and related persistent final response cache. -/
theorem adaptive_projection {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed) {A : Type}
    (program : OracleComp (Query →ₒ FullResponse) A) (cache : ByteCache) :
    Prod.map id (restrictCache seed) <$> (simulateQ (routed draw seed) program).run cache =
      (simulateQ (answers draw seed).withCaching program).run (restrictCache seed cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (restrictCache seed)
    (routed_projection draw seed) program cache

/-- Repeated actual queries return both original halves and leave the entire byte cache intact. -/
theorem routed_halves_of_hit {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed) (query : Query)
    (cache : ByteCache) (response : FullResponse) (hit : cache (queryInput seed query) =
      some response) :
    (fun result => (splitResponse result.1, result.2)) <$> (routed draw seed query).run cache =
      pure (splitResponse response, cache) := by
  change (fun result => (splitResponse result.1, result.2)) <$>
    (draw.withCaching (queryInput seed query)).run cache = _
  rw [QueryImpl.withCaching_run_some draw hit, map_pure]

/-- One initial miss installs all 32 bytes and the repeated actual query uses the same response. -/
theorem routed_repeated_of_miss {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed) (query : Query)
    (cache : ByteCache) (miss : cache (queryInput seed query) = none) :
    (do
      let first ← routed draw seed query
      let second ← routed draw seed query
      pure (splitResponse first, splitResponse second) :
        StateT ByteCache m ((Digest × Digest) × (Digest × Digest))).run cache =
      (fun response => ((splitResponse response, splitResponse response),
        cache.cacheQuery (queryInput seed query) response)) <$> draw (queryInput seed query) := by
  simp only [StateT.run_bind, StateT.run_pure, routed,
    QueryImpl.withCaching_run_none draw miss, bind_map_left]
  simp only [QueryImpl.withCaching_run_some draw (QueryCache.cacheQuery_self _ _ _),
    map_pure, bind_pure_comp]

/-- The native PRF ideal handler at the actual reviewed paired-counter query domain. -/
noncomputable abbrev nativeIdeal :
    QueryImpl (PRFScheme.PRFOracleSpec Query FullResponse) (StateT Cache ProbComp) :=
  PRFScheme.prfIdealQueryImpl

/-- Forward private sampling and route actual function requests into the source byte cache. -/
@[expose]
def routedIdeal (seed : Seed) :
    QueryImpl (PRFScheme.PRFOracleSpec Query FullResponse) (StateT ByteCache ProbComp) :=
  unifSpec.passthrough + routed uniformSampleImpl seed

/-- The native ideal function-query step is exactly the routed uniform response step. -/
theorem routedIdeal_projection (seed : Seed)
    (query : (PRFScheme.PRFOracleSpec Query FullResponse).Domain) (cache : ByteCache) :
    Prod.map id (restrictCache seed) <$> (routedIdeal seed query).run cache =
      (nativeIdeal query).run (restrictCache seed cache) := by
  cases query with
  | inl index =>
    simp [routedIdeal, nativeIdeal, PRFScheme.prfIdealQueryImpl, unifFwdImpl]
  | inr query =>
    change Prod.map id (restrictCache seed) <$>
      (routed uniformSampleImpl seed query).run cache =
        ((Query →ₒ FullResponse).randomOracle query).run (restrictCache seed cache)
    exact routed_projection uniformSampleImpl seed query cache

/-- Native ideal PRF clients with private sampling preserve outputs and the full final cache. -/
theorem routedIdeal_adaptive_projection (seed : Seed) {A : Type}
    (program : OracleComp (PRFScheme.PRFOracleSpec Query FullResponse) A) (cache : ByteCache) :
    Prod.map id (restrictCache seed) <$> (simulateQ (routedIdeal seed) program).run cache =
      (simulateQ nativeIdeal program).run (restrictCache seed cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (restrictCache seed)
    (routedIdeal_projection seed) program cache

/-- The reviewed hypertree wrapper's public replay law retains the same complete response. -/
theorem reviewed_cachedQuery_replay (cache : Cache) (query : Query) (response : FullResponse)
    (hit : cache query = some response) :
    ((GXMSS.Hypertree.PRFDerived.cachedQueryImpl (PP := PublicParam) (M := Message) (H := Digest)
      (S := ConcreteHypertree.shape) (layout := .pairedCounter)
      (budget := GXMSS.Hypertree.PRFDerived.retryBudget HypertreeStrategies.sourceRetrySampling)
      (Sum.inr query)).run cache) = pure (response, cache) :=
  GXMSS.Hypertree.PRFDerived.cachedQuery_replay cache query response hit

private theorem cachedQueryImpl_eq_native :
    (GXMSS.Hypertree.PRFDerived.cachedQueryImpl (PP := PublicParam) (M := Message) (H := Digest)
      (S := ConcreteHypertree.shape) (layout := .pairedCounter)
      (budget := GXMSS.Hypertree.PRFDerived.retryBudget HypertreeStrategies.sourceRetrySampling) :
        QueryImpl (PRFScheme.PRFOracleSpec Query FullResponse) (StateT Cache ProbComp)) =
      nativeIdeal := rfl

/-- The reviewed hypertree cache wrapper is the standard native ideal PRF implementation. -/
theorem reviewed_cachedQueryImpl_eq_native :
    (GXMSS.Hypertree.PRFDerived.cachedQueryImpl (PP := PublicParam) (M := Message) (H := Digest)
      (S := ConcreteHypertree.shape) (layout := .pairedCounter)
      (budget := GXMSS.Hypertree.PRFDerived.retryBudget HypertreeStrategies.sourceRetrySampling) :
        QueryImpl (PRFScheme.PRFOracleSpec Query FullResponse) (StateT Cache ProbComp)) =
      nativeIdeal := cachedQueryImpl_eq_native

/-- The actual reviewed ideal client preserves its output and the restricted full final cache. -/
theorem reviewed_cachedQueryImpl_adaptive_projection (seed : Seed) {A : Type}
    (program : OracleComp (PRFScheme.PRFOracleSpec Query FullResponse) A) (cache : ByteCache) :
    Prod.map id (restrictCache seed) <$> (simulateQ (routedIdeal seed) program).run cache =
      (simulateQ (GXMSS.Hypertree.PRFDerived.cachedQueryImpl (PP := PublicParam) (M := Message)
        (H := Digest) (S := ConcreteHypertree.shape) (layout := .pairedCounter)
        (budget := GXMSS.Hypertree.PRFDerived.retryBudget HypertreeStrategies.sourceRetrySampling))
          program).run (restrictCache seed cache) := by
  rw [reviewed_cachedQueryImpl_eq_native]
  exact routedIdeal_adaptive_projection seed program cache

end EthereumXMSSHypertree.HypertreeCache
