module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.ProgramLogic.Unary.HoareTriple
public import EthLib.Cryptography.Proofs.HashSig.Calls
import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Proofs: a long failed search is unlikely in the random-oracle model, whoever queries it

A search hashes the points of its trials `0, 1, ...` in order and stops at the first that passes.

The hash is a lazily sampled random oracle, and the cache is shared by everyone who queries it.

A search fails its first `T` trials when the cache holds a failing answer at each of their points.

Some of those points may have been queried before the search starts, by anyone.

Take a run from an empty cache with at most `n` hash calls.

Its final cache holds a search that failed its first `T` trials with probability at most `n * q^T`.

Here `q` is the chance that one uniform answer fails.

The proof follows a potential.

A search whose trials are partly cached, with no passing answer among them, weighs `q^(T - k)`.

Here `k` counts its cached trials, so for `T >= 1` a search that failed all `T` trials weighs 1.

A fresh answer at a point of a touched search does not raise its expected weight.

A fresh answer at a point of an untouched search raises the expected total by at most `q^T`.

So each hash call adds at most `q^T` to the expected total, and the total starts at 0.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleSpec OracleComp ENNReal OracleComp.ProgramLogic
open scoped OracleComp.Lower

variable {ι R P : Type} [DecidableEq ι] [SampleableType R]

/-- Search `p` hashes the point `point p j` at trial `j`; an answer `u` fails when `fail u`.

Some search has failed its first `T` trials: the cache holds a failing answer at each point. -/
def FailedSearch (point : P → ℕ → ι) (fail : R → Prop) (T : ℕ)
    (cache : (ι →ₒ R).QueryCache) : Prop :=
  ∃ p, ∀ j < T, ∃ u, cache (point p j) = some u ∧ fail u

/-- The weight of one search in a cache, when one answer fails with probability `q`.

A search with none of its first `T` trials cached weighs 0.

So does a search with a passing answer among its first `T` trials.

Otherwise, with `k` of its first `T` trials cached, the search weighs `q^(T - k)`. -/
noncomputable def searchWeight (point : P → ℕ → ι) (fail : R → Prop) [DecidablePred fail]
    (T : ℕ) (q : ℝ≥0∞) (cache : (ι →ₒ R).QueryCache) (p : P) : ℝ≥0∞ :=
  if (∀ j < T, cache (point p j) = none) ∨
      (∃ j < T, ∃ u, cache (point p j) = some u ∧ ¬fail u) then 0
  else q ^ (T - ((Finset.range T).filter fun j => (cache (point p j)).isSome).card)

/-- The potential of a cache: the total weight of all searches. -/
noncomputable def searchPotential (point : P → ℕ → ι) (fail : R → Prop) [DecidablePred fail]
    (T : ℕ) (q : ℝ≥0∞) (cache : (ι →ₒ R).QueryCache) : ℝ≥0∞ :=
  ∑' p, searchWeight point fail T q cache p

variable (point : P → ℕ → ι) (fail : R → Prop) [DecidablePred fail] (T : ℕ)

omit [DecidableEq ι] [SampleableType R] [DecidablePred fail] in
/-- A failed search stays failed in a larger cache. -/
theorem FailedSearch.mono {cache cache' : (ι →ₒ R).QueryCache} (hle : cache ≤ cache')
    (h : FailedSearch point fail T cache) : FailedSearch point fail T cache' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun j hj => (hp j hj).imp fun _ hu => ⟨hle hu.1, hu.2⟩⟩

/-- **A run of a hash computation is its run under one answer function, with every query cached.**

The computation starts from any cache and ends with a value and a cache.

Some answer function agrees with the final cache and gives the value.

The final cache holds the answer of the function at every point that the computation queries. -/
theorem exists_answerFn_of_mem_support {β : Type} (oc : OracleComp (ι →ₒ R) β)
    (cache : (ι →ₒ R).QueryCache) (z : β × (ι →ₒ R).QueryCache)
    (hz : z ∈ support ((simulateQ (ι →ₒ R).romImpl
      (liftM oc : OracleComp (unifSpec + (ι →ₒ R)) β)).run cache)) :
    ∃ f : QueryImpl (ι →ₒ R) Id, z.2.AgreesWithFn f ∧ z.1 = evalWithAnswerFn f oc ∧
      ∀ x ∈ queriesWith f oc, z.2 x = some (f x) := by
  induction oc using OracleComp.inductionOn generalizing cache z with
  | pure x =>
    simp only [liftM_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := ι →ₒ R) cache
    exact ⟨f, hf, rfl, by simp⟩
  | query_bind t k ih =>
    have h1 : simulateQ (ι →ₒ R).romImpl (liftM (liftM (OracleSpec.query t) :
        OracleComp (ι →ₒ R) _) : OracleComp (unifSpec + (ι →ₒ R)) _) =
        (ι →ₒ R).randomOracle t := QueryImpl.simulateQ_add_liftM_query_right _ _ t
    rw [liftM_bind, simulateQ_bind, h1, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, c⟩, hw, hz⟩ := hz
    obtain ⟨f, hf, hval, hq⟩ := ih u c z hz
    have hct : c t = some u := by
      rw [randomOracle.run_eq] at hw
      rcases hc : cache t with _ | v
      · rw [hc] at hw
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hw
        obtain ⟨v, -, rfl, rfl⟩ := hw
        exact QueryCache.cacheQuery_self _ _ _
      · rw [hc] at hw
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact hc
    -- The final cache keeps the answer at `t`, so the answer function gives it there.
    have hzt : z.2 t = some u :=
      OracleComp.le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ hz hct
    have hfu : f t = u := hf hzt
    refine ⟨f, hf, ?_, ?_⟩
    · change z.1 = evalWithAnswerFn f (k (f t))
      rw [hfu, hval]
    · intro x hx
      change x ∈ t :: queriesWith f (k (f t)) at hx
      rw [hfu, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [hfu]
        exact hzt
      · exact hq x hx

omit [DecidableEq ι] in
/-- The empty cache has potential 0. -/
theorem searchPotential_empty (q : ℝ≥0∞) : searchPotential point fail T q ∅ = 0 := by
  simp [searchPotential, searchWeight, QueryCache.empty_apply]

omit [DecidableEq ι] [SampleableType R] in
/-- A cache in which some search failed its first `T >= 1` trials has potential at least 1. -/
theorem one_le_searchPotential (hT : 1 ≤ T) (q : ℝ≥0∞) (cache : (ι →ₒ R).QueryCache)
    (h : FailedSearch point fail T cache) : 1 ≤ searchPotential point fail T q cache := by
  obtain ⟨p, hp⟩ := h
  refine le_trans ?_ (le_tsum _ p)
  have hnone : ¬∀ j < T, cache (point p j) = none := fun hall => by
    obtain ⟨u, hu, -⟩ := hp 0 hT
    simp [hall 0 hT] at hu
  have hpass : ¬∃ j < T, ∃ u, cache (point p j) = some u ∧ ¬fail u := by
    rintro ⟨j, hj, u, hu, hfu⟩
    obtain ⟨u', hu', hfu'⟩ := hp j hj
    rw [hu] at hu'
    exact hfu (Option.some.inj hu' ▸ hfu')
  have hcard : ((Finset.range T).filter fun j => (cache (point p j)).isSome).card = T := by
    rw [Finset.filter_true_of_mem, Finset.card_range]
    intro j hj
    obtain ⟨u, hu, -⟩ := hp j (Finset.mem_range.mp hj)
    simp [hu]
  simp [searchWeight, hnone, hpass, hcard]

omit [DecidableEq ι] [SampleableType R] in
/-- The weight of a search depends only on the cache entries at the points of its first trials. -/
theorem searchWeight_congr (q : ℝ≥0∞) {cache cache' : (ι →ₒ R).QueryCache} (p : P)
    (h : ∀ j < T, cache (point p j) = cache' (point p j)) :
    searchWeight point fail T q cache p = searchWeight point fail T q cache' p := by
  have hf : (Finset.range T).filter (fun j => (cache (point p j)).isSome) =
      (Finset.range T).filter (fun j => (cache' (point p j)).isSome) :=
    Finset.filter_congr fun j hj => by rw [h j (Finset.mem_range.mp hj)]
  have h1 : (∀ j < T, cache (point p j) = none) ↔ ∀ j < T, cache' (point p j) = none :=
    forall₂_congr fun j hj => by rw [h j hj]
  have h2 : (∃ j < T, ∃ u, cache (point p j) = some u ∧ ¬fail u) ↔
      ∃ j < T, ∃ u, cache' (point p j) = some u ∧ ¬fail u :=
    exists_congr fun j => and_congr_right fun hj => by rw [h j hj]
  simp only [searchWeight, hf, h1, h2]

omit [DecidableEq ι] in
/-- Expectations over a uniform answer commute with sums over searches. -/
theorem wp_uniform_tsum (f : P → R → ℝ≥0∞) :
    wp ($ᵗ R) (fun u => ∑' p, f p u) = ∑' p, wp ($ᵗ R) (f p) := by
  simp_rw [wp_eq_tsum, ← ENNReal.tsum_mul_left]
  exact tsum_comm

/-- **A fresh answer does not raise the expected weight of a search, but by `q^T` if untouched.**

The answer is uniform at an uncached point, and fails with probability at most `q`.

The extra `q^T` arises only for an untouched search with a trial at that point. -/
theorem wp_searchWeight_cacheQuery_le
    (hinj : ∀ p p' j j', j < T → j' < T → point p j = point p' j' → p = p' ∧ j = j')
    (q : ℝ≥0∞) (hq : Pr{let u ← $ᵗ R}[fail u] ≤ q) {cache : (ι →ₒ R).QueryCache} {t : ι}
    (ht : cache t = none) (p : P) :
    wp ($ᵗ R) (fun u => searchWeight point fail T q (cache.cacheQuery t u) p) ≤
      searchWeight point fail T q cache p +
        if (∃ j < T, point p j = t) ∧ ∀ j < T, cache (point p j) = none then q ^ T else 0 := by
  by_cases hp : ∃ j < T, point p j = t
  swap
  · -- No trial of the search hashes the point, so its weight does not move.
    push Not at hp
    have h : ∀ u, searchWeight point fail T q (cache.cacheQuery t u) p =
        searchWeight point fail T q cache p := fun u =>
      searchWeight_congr point fail T q p fun j hj => QueryCache.cacheQuery_of_ne _ _ (hp j hj)
    simp only [h, wp_const]
    exact le_self_add
  obtain ⟨j₀, hj₀, rfl⟩ := hp
  -- The fresh answer lands at trial `j₀` only.
  have hval : ∀ u, ∀ j < T, cache.cacheQuery (point p j₀) u (point p j) =
      if j = j₀ then some u else cache (point p j) := by
    intro u j hj
    split_ifs with h
    · subst h
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.cacheQuery_of_ne _ _ fun he => h (hinj p p j j₀ hj hj₀ he).2
  by_cases hpass : ∃ j < T, ∃ v, cache (point p j) = some v ∧ ¬fail v
  · -- A cached passing answer keeps the weight at 0.
    have h0 : ∀ u, searchWeight point fail T q (cache.cacheQuery (point p j₀) u) p = 0 := by
      intro u
      obtain ⟨j, hj, v, hv, hfv⟩ := hpass
      have hjj : j ≠ j₀ := by
        rintro rfl
        rw [ht] at hv
        cases hv
      unfold searchWeight
      rw [ite_eq_left (Or.inr ⟨j, hj, v, by rw [hval u j hj, ite_eq_right hjj, hv], hfv⟩)]
    simp only [h0, wp_const]
    exact zero_le
  obtain ⟨k, hk⟩ : ∃ k, ((Finset.range T).filter fun j => (cache (point p j)).isSome).card = k :=
    ⟨_, rfl⟩
  have hnot : j₀ ∉ (Finset.range T).filter fun j => (cache (point p j)).isSome := by
    simp [ht]
  -- The fresh answer adds trial `j₀` to the cached trials.
  have hcard : ∀ u, ((Finset.range T).filter fun j =>
      (cache.cacheQuery (point p j₀) u (point p j)).isSome).card = k + 1 := by
    intro u
    have hs : ((Finset.range T).filter fun j =>
        (cache.cacheQuery (point p j₀) u (point p j)).isSome) =
        insert j₀ ((Finset.range T).filter fun j => (cache (point p j)).isSome) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
      constructor
      · rintro ⟨hj, hs⟩
        rw [hval u j hj] at hs
        split_ifs at hs with h
        · exact Or.inl h
        · exact Or.inr ⟨hj, hs⟩
      · rintro (h | ⟨hj, hs⟩)
        · rw [h]
          simp [hj₀]
        · refine ⟨hj, ?_⟩
          rw [hval u j hj, ite_eq_right]
          · exact hs
          · rintro rfl
            simp [ht] at hs
    rw [hs, Finset.card_insert_of_notMem hnot, hk]
  have hkT : k < T := by
    rw [← hk]
    calc _ < (Finset.range T).card :=
          Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨j₀, Finset.mem_range.mpr hj₀, by
            simp [ht]⟩)
      _ = T := Finset.card_range T
  -- After the answer, the weight is `q^(T - k - 1)` when the answer fails, and 0 otherwise.
  have hw' : ∀ u, searchWeight point fail T q (cache.cacheQuery (point p j₀) u) p =
      (if fail u then 1 else 0) * q ^ (T - (k + 1)) := by
    intro u
    have hn1 : ¬∀ j < T, cache.cacheQuery (point p j₀) u (point p j) = none := fun h => by
      simpa [hval u j₀ hj₀] using h j₀ hj₀
    have hn2 : (∃ j < T, ∃ v, cache.cacheQuery (point p j₀) u (point p j) = some v ∧
        ¬fail v) ↔ ¬fail u := by
      constructor
      · rintro ⟨j, hj, v, hv, hfv⟩
        rw [hval u j hj] at hv
        split_ifs at hv with h
        · rwa [Option.some.inj hv]
        · exact absurd ⟨j, hj, v, hv, hfv⟩ hpass
      · intro hfu
        exact ⟨j₀, hj₀, u, by simp, hfu⟩
    unfold searchWeight
    rw [hcard u]
    by_cases hfu : fail u <;> simp [hn1, hn2, hfu]
  simp only [hw']
  rw [wp_const_mul, ← prEvent_eq_wp_indicator]
  calc Pr{let u ← $ᵗ R}[fail u] * q ^ (T - (k + 1)) ≤ q * q ^ (T - (k + 1)) := by gcongr
    _ = q ^ (T - k) := by
      rw [← pow_succ']
      congr 1
      omega
    _ ≤ _ := by
      by_cases hall : ∀ j < T, cache (point p j) = none
      · have hk0 : k = 0 := by
          rw [← hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j hj
          simp [hall j (Finset.mem_range.mp hj)]
        rw [ite_eq_left ⟨⟨j₀, hj₀, rfl⟩, hall⟩, hk0, Nat.sub_zero]
        exact le_add_self
      · unfold searchWeight
        rw [ite_eq_right (not_or.mpr ⟨hall, hpass⟩), hk]
        exact le_self_add

/-- **A fresh answer raises the expected potential by at most `q^T`.**

The answer is uniform at an uncached point, and fails with probability at most `q`.

Only one search can have a trial at that point, so only one search gains. -/
theorem wp_searchPotential_cacheQuery_le
    (hinj : ∀ p p' j j', j < T → j' < T → point p j = point p' j' → p = p' ∧ j = j')
    (q : ℝ≥0∞) (hq : Pr{let u ← $ᵗ R}[fail u] ≤ q) {cache : (ι →ₒ R).QueryCache} {t : ι}
    (ht : cache t = none) :
    wp ($ᵗ R) (fun u => searchPotential point fail T q (cache.cacheQuery t u)) ≤
      searchPotential point fail T q cache + q ^ T := by
  unfold searchPotential
  rw [wp_uniform_tsum]
  refine (tsum_le_tsum fun p =>
    wp_searchWeight_cacheQuery_le point fail T hinj q hq ht p).trans ?_
  rw [tsum_add]
  gcongr
  -- At most one search has a trial at the point.
  by_cases h : ∃ p₀, ∃ j < T, point p₀ j = t
  · obtain ⟨p₀, j₀, hj₀, rfl⟩ := h
    rw [tsum_eq_single p₀]
    · split_ifs <;> simp
    · intro p hp
      rw [ite_eq_right]
      rintro ⟨⟨j, hj, he⟩, -⟩
      exact hp (hinj p p₀ j j₀ hj hj₀ he).1
  · push Not at h
    rw [tsum_eq_zero_iff.mpr fun p => ite_eq_right fun hc => ?_]
    · exact zero_le
    · obtain ⟨⟨j, hj, he⟩, -⟩ := hc
      exact h p j hj he

/-- A run that starts with a query costs that query, then a run of the continuation.

The query alone costs at most `n`.

Each run of the continuation, after one answer of the query, costs at most `n` minus that cost. -/
theorem cost_le_of_query_bind {α : Type} (cost : (unifSpec + (ι →ₒ R)).Domain → ℕ)
    (t : (unifSpec + (ι →ₒ R)).Domain)
    (k : (unifSpec + (ι →ₒ R)).Range t → OracleComp (unifSpec + (ι →ₒ R)) α)
    (n : ℕ) (cache : (ι →ₒ R).QueryCache)
    (hn : ∀ z ∈ support ((simulateQ ((ι →ₒ R).romImpl.withAddCost cost)
      (liftM (OracleSpec.query t) >>= k)).run.run' cache), z.2 ≤ n)
    {w : (unifSpec + (ι →ₒ R)).Range t × (ι →ₒ R).QueryCache}
    (hw : w ∈ support (((ι →ₒ R).romImpl t).run cache)) :
    cost t ≤ n ∧ ∀ z ∈ support ((simulateQ ((ι →ₒ R).romImpl.withAddCost cost)
      (k w.1)).run.run' w.2), z.2 ≤ n - cost t := by
  simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.withAddCost_apply,
    WriterT.run_bind, StateT.run'_eq, StateT.run_bind] at hn
  simp [WriterT.run_liftM, AddWriterT.addTell] at hn
  have key : ∀ z ∈ support ((simulateQ ((ι →ₒ R).romImpl.withAddCost cost)
      (k w.1)).run.run' w.2), cost t + Multiplicative.toAdd z.2 ≤ n := by
    rintro ⟨a, c⟩ hz
    simp at hz
    obtain ⟨c', hc'⟩ := hz
    exact hn a _ w.1 w.2 (by simpa using hw) a (Multiplicative.toAdd c) c' hc' rfl rfl
  obtain ⟨z, hz⟩ := support_nonempty ((simulateQ ((ι →ₒ R).romImpl.withAddCost cost)
      (k w.1)).run.run' w.2)
  have := key z hz
  refine ⟨by omega, fun z hz => ?_⟩
  have := key z hz
  change Multiplicative.toAdd z.2 ≤ n - cost t
  omega

/-- **From any cache, the run raises the potential by at most `q^T` per hash call, in expectation.**

The first `T` trials of distinct searches, and distinct ones of one search, hash distinct points.

One uniform answer fails with probability at most `q`.

Every run of the computation from the cache costs at most `n`, and each hash call costs at least 1.

Then the final cache has expected potential at most the initial one plus `n * q^T`. -/
theorem wp_searchPotential_le
    (hinj : ∀ p p' j j', j < T → j' < T → point p j = point p' j' → p = p' ∧ j = j')
    (q : ℝ≥0∞) (hq : Pr{let u ← $ᵗ R}[fail u] ≤ q)
    (cost : (unifSpec + (ι →ₒ R)).Domain → ℕ) (hcost : ∀ x, 1 ≤ cost (.inr x))
    {α : Type} (oa : OracleComp (unifSpec + (ι →ₒ R)) α) (n : ℕ)
    (cache : (ι →ₒ R).QueryCache)
    (hn : ∀ z ∈ support ((simulateQ ((ι →ₒ R).romImpl.withAddCost cost) oa).run.run' cache),
      z.2 ≤ n) :
    wp ((simulateQ (ι →ₒ R).romImpl oa).run cache)
        (fun z => searchPotential point fail T q z.2) ≤
      searchPotential point fail T q cache + (n : ℝ≥0∞) * q ^ T := by
  induction oa using OracleComp.inductionOn generalizing cache n with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, wp_pure]
    exact le_self_add
  | query_bind t k ih =>
    have hstep := fun w hw => cost_le_of_query_bind cost t k n cache hn (w := w) hw
    have hq' : simulateQ (ι →ₒ R).romImpl (liftM (OracleSpec.query t) :
        OracleComp (unifSpec + (ι →ₒ R)) _) = (ι →ₒ R).romImpl t := simulateQ_spec_query _ t
    rw [simulateQ_bind, hq', StateT.run_bind, wp_bind]
    -- A continuation run allowed `n - c` raises the potential by at most `n * q^T` too.
    have hmono : ∀ c : ℕ, searchPotential point fail T q cache + ((n - c : ℕ) : ℝ≥0∞) * q ^ T ≤
        searchPotential point fail T q cache + (n : ℝ≥0∞) * q ^ T := fun c => by
      gcongr
      exact Nat.sub_le n c
    -- A query that keeps the cache passes the bound to the continuation.
    have hsame : (∀ w ∈ support (((ι →ₒ R).romImpl t).run cache), w.2 = cache) →
        (wp (((ι →ₒ R).romImpl t).run cache) fun w =>
          wp ((simulateQ (ι →ₒ R).romImpl (k w.1)).run w.2) fun z =>
            searchPotential point fail T q z.2) ≤
          searchPotential point fail T q cache + (n : ℝ≥0∞) * q ^ T := fun h =>
      wp_le_const_of_support _ fun w hw =>
        (ih w.1 _ w.2 (hstep w hw).2).trans (by rw [h w hw]; exact hmono _)
    rcases t with i | t
    · -- A coin query keeps the cache.
      refine hsame fun w hw => ?_
      rw [roSim.run_apply_inl, support_map] at hw
      obtain ⟨u, -, rfl⟩ := hw
      rfl
    rcases hc : cache t with _ | v
    swap
    · -- A cached hash query keeps the cache.
      refine hsame fun w hw => ?_
      rw [OracleSpec.romImpl_apply_inr, randomOracle.run_eq, hc, support_pure] at hw
      rw [hw]
    -- A fresh hash query samples a uniform answer and caches it.
    have hmem : ∀ u : R, (u, cache.cacheQuery t u) ∈
        support (((ι →ₒ R).romImpl (.inr t)).run cache) := fun u => by
      rw [OracleSpec.romImpl_apply_inr, randomOracle.run_eq, hc]
      simp
    obtain ⟨u₀⟩ := (inferInstance : Nonempty R)
    have hcn := (hstep _ (hmem u₀)).1
    have h1 := hcost t
    rw [OracleSpec.romImpl_apply_inr, randomOracle.run_eq, hc, wp_bind]
    simp only [wp_pure]
    calc (wp ($ᵗ R) fun u => wp ((simulateQ (ι →ₒ R).romImpl (k u)).run (cache.cacheQuery t u))
          fun z => searchPotential point fail T q z.2)
        ≤ wp ($ᵗ R) fun u => searchPotential point fail T q (cache.cacheQuery t u) +
            ((n - cost (.inr t) : ℕ) : ℝ≥0∞) * q ^ T :=
          wp_mono _ fun u => ih u _ _ (hstep _ (hmem u)).2
      _ = wp ($ᵗ R) (fun u => searchPotential point fail T q (cache.cacheQuery t u)) +
            ((n - cost (.inr t) : ℕ) : ℝ≥0∞) * q ^ T := by
          rw [wp_add, wp_const]
      _ ≤ searchPotential point fail T q cache + q ^ T +
            ((n - cost (.inr t) : ℕ) : ℝ≥0∞) * q ^ T := by
          gcongr
          exact wp_searchPotential_cacheQuery_le point fail T hinj q hq hc
      _ = searchPotential point fail T q cache +
            ((1 + (n - cost (.inr t)) : ℕ) : ℝ≥0∞) * q ^ T := by
          push_cast
          ring
      _ ≤ searchPotential point fail T q cache + (n : ℝ≥0∞) * q ^ T := by
          gcongr
          omega

/-- **A run with at most `n` hash calls leaves a failed search with probability `<= n * q^T`.**

A failed search is one whose first `T` trials all failed.

The cache starts empty, and `T >= 1`.

The first `T` trials of distinct searches, and distinct ones of one search, hash distinct points.

`q` is the chance that one uniform answer fails.

Every run costs at most `n`, and each hash call costs at least 1. -/
theorem prEvent_failedSearch_le (hT : 1 ≤ T)
    (hinj : ∀ p p' j j', j < T → j' < T → point p j = point p' j' → p = p' ∧ j = j')
    (cost : (unifSpec + (ι →ₒ R)).Domain → ℕ) (hcost : ∀ x, 1 ≤ cost (.inr x))
    {α : Type} (oa : OracleComp (unifSpec + (ι →ₒ R)) α) (n : ℕ)
    (hn : ∀ z ∈ support ((simulateQ ((ι →ₒ R).romImpl.withAddCost cost) oa).run.run' ∅),
      z.2 ≤ n) :
    Pr{let z ← (simulateQ (ι →ₒ R).romImpl oa).run ∅}[FailedSearch point fail T z.2] ≤
      (n : ℝ≥0∞) * Pr{let u ← $ᵗ R}[fail u] ^ T := by
  -- A failed search means a potential of at least 1.
  rw [prEvent_eq_wp_propInd]
  refine (wp_mono _ fun z => ?_).trans ((wp_searchPotential_le point fail T hinj _ le_rfl cost
    hcost oa n ∅ hn).trans_eq (by rw [searchPotential_empty, zero_add]))
  by_cases h : FailedSearch point fail T z.2
  · rw [propInd_eq_one_iff.mpr h]
    exact one_le_searchPotential point fail T hT _ _ h
  · rw [propInd_eq_zero_iff.mpr h]
    exact zero_le

end EthLib.Cryptography.HashSig
