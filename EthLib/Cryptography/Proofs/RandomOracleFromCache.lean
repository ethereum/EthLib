module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Proofs: lazy random-oracle runs from a cache that is not empty

A later phase of a game starts from the cache that the earlier phases left.

These are the fresh-answer bounds of the framework, restated from any finite cache.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleComp OracleSpec ENNReal

variable {ι α : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- A run of at most `q` oracle calls adds at most `q` entries to its starting cache. -/
theorem enncard_le_of_mem_support_run_romImpl
    {oa : OracleComp (unifSpec + spec) α} {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) {c₀ : spec.QueryCache}
    {z : α × spec.QueryCache}
    (hz : z ∈ support ((simulateQ spec.romImpl oa).run c₀)) :
    QueryCache.enncard z.2 ≤ QueryCache.enncard c₀ + q := by
  -- Each oracle call adds at most one entry.
  have key := hq.resource_le_add_of_mem_support_run_simulateQ (fun c => c.toSet.encard)
    (fun t c w hw => ?_) hz
  · simpa [QueryCache.enncard] using ENat.toENNReal_le.mpr key
  rcases t with i | t
  · obtain ⟨samp, hsamp⟩ := exists_run_unifFwdImpl_add_randomOracle_inl (spec := spec) i c
    rw [hsamp, support_map] at hw
    obtain ⟨u, -, rfl⟩ := hw
    simp
  · rw [OracleSpec.romImpl, QueryImpl.add_apply_inr] at hw
    rcases hc : c t with _ | u
    · rw [QueryImpl.withCaching_run_none _ hc, support_map] at hw
      obtain ⟨u, -, rfl⟩ := hw
      simpa using QueryCache.toSet_encard_cacheQuery_le c t u
    · rw [QueryImpl.withCaching_run_some _ hc] at hw
      simp_all

/-- A bad event fires with probability at most `q * ε` on runs that add at most `q` entries.

It must fail at the start, and each fresh answer must fire it with probability at most `ε`. -/
theorem prEvent_run_and_enncard_le_of_fresh_bound_from (P : spec.QueryCache → Prop)
    (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : spec.Domain) (c : spec.QueryCache), ¬ P c → c t = none →
      Pr{let u ← $ᵗ spec.Range t}[P (c.cacheQuery t u)] ≤ ε)
    (oa : OracleComp (unifSpec + spec) α) (q : Nat) (c₀ : spec.QueryCache)
    (hc₀ : ¬ P c₀) (hfin : QueryCache.enncard c₀ ≠ ⊤) :
    Pr{let z ← (simulateQ spec.romImpl oa).run c₀}[
      P z.2 ∧ QueryCache.enncard z.2 ≤ QueryCache.enncard c₀ + q] ≤ q * ε := by
  -- The potential is `ε` per cache entry.
  have hmono : ∀ (t : (unifSpec + spec).Domain) (c : spec.QueryCache),
      ∀ z ∈ support ((spec.romImpl t).run c),
        QueryCache.enncard c * ε ≤ QueryCache.enncard z.2 * ε := by
    intro t c z hz
    have hle : c ≤ z.2 := le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl
      (liftM (OracleSpec.query t) : OracleComp (unifSpec + spec) _) (by simpa using hz)
    gcongr
    exact QueryCache.enncard_mono hle
  -- The run gains at most `q * ε` of potential.
  have key := prEvent_and_le_of_potential spec.romImpl P
    (fun c => QueryCache.enncard c * ε) hmono (fun t c hc => ?_) oa
    ((QueryCache.enncard c₀ + q) * ε) (mul_ne_top (add_ne_top.2 ⟨hfin, by simp⟩) hε) c₀ hc₀
  · -- `(n + q) * ε - n * ε = q * ε`, as the start is finite.
    refine (prEvent_mono _ _ _ fun z hz => ⟨hz.1, by gcongr; exact hz.2⟩).trans (key.trans ?_)
    rw [add_mul, ENNReal.add_sub_cancel_left (mul_ne_top hfin hε)]
  rcases t with i | t
  · obtain ⟨samp, hsamp⟩ := exists_run_unifFwdImpl_add_randomOracle_inl (spec := spec) i c
    exact Or.inr ⟨samp, fun _ => c, 0, hsamp, by simp [hc], fun _ => by simp⟩
  · rcases h : c t with _ | u
    · exact Or.inr ⟨$ᵗ spec.Range t, fun u => c.cacheQuery t u, ε,
        QueryImpl.withCaching_run_none _ h, hfresh t c hc h,
        fun u => by rw [QueryCache.enncard_cacheQuery c t u h, add_mul, one_mul, add_comm]⟩
    · exact Or.inl ⟨u, c, QueryImpl.withCaching_run_some _ h, hc⟩

/-- A run of at most `q` oracle calls fires a bad event with probability at most `q * ε`.

It must fail at the start, and each fresh answer must fire it with probability at most `ε`. -/
theorem prEvent_run_le_of_fresh_bound_from (P : spec.QueryCache → Prop) (ε : ℝ≥0∞)
    (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : spec.Domain) (c : spec.QueryCache), ¬ P c → c t = none →
      Pr{let u ← $ᵗ spec.Range t}[P (c.cacheQuery t u)] ≤ ε)
    (oa : OracleComp (unifSpec + spec) α) {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) (c₀ : spec.QueryCache)
    (hc₀ : ¬ P c₀) (hfin : QueryCache.enncard c₀ ≠ ⊤) :
    Pr{let z ← (simulateQ spec.romImpl oa).run c₀}[P z.2] ≤ q * ε :=
  le_trans (prEvent_mono_of_support _ _ _ fun _ hz hPz =>
      ⟨hPz, enncard_le_of_mem_support_run_romImpl hq hz⟩)
    (prEvent_run_and_enncard_le_of_fresh_bound_from P ε hε hfresh oa q c₀ hc₀ hfin)

/-- A computation that the cache answers runs without sampling and keeps the cache. -/
theorem run_randomOracle_of_partial {c : spec.QueryCache}
    (oa : OracleComp spec α) {a : α} (ha : simulateQ c.toPartialImpl oa = some a) :
    (simulateQ spec.randomOracle oa).run c = pure (a, c) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using ha
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at ha ⊢
    obtain ⟨u, hu, ha⟩ := Option.bind_eq_some_iff.mp ha
    rw [StateT.run_bind, QueryImpl.withCaching_run_some _ hu, pure_bind]
    exact ih u ha

omit [DecidableEq ι] [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- A cache that replays each computation of a list replays the computations in sequence. -/
theorem partial_mapM_isSome {β γ : Type} (c : spec.QueryCache)
    (f : β → OracleComp spec γ) :
    ∀ l : List β, (∀ x ∈ l, (simulateQ c.toPartialImpl (f x)).isSome) →
      (simulateQ c.toPartialImpl (l.mapM f)).isSome
  | [], _ => by simp
  | x :: l, h => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    obtain ⟨as, has⟩ := Option.isSome_iff_exists.mp
      (partial_mapM_isSome c f l fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [List.mapM_cons, simulateQ_bind, ha, has]

end EthLib.Cryptography
