module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedUnifiedExpectedDigest
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedEncodingGameTrace
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Scan.Frame

/-!
# The adversary phase with a ghost query count

The traced handler of the capped adversary phase, extended with a count.

The count is of the adversary's own hash queries.

This file proves that, under a hash-query bound, the count never reaches the budget.

It also splits the source game's count of a class into the adversary's queries and the signer's.

So the source game's count bounds the adversary's encoding queries.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Ghost

/-- A hash query of the adversary. -/
def IsAdvHash : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

noncomputable instance : DecidablePred IsAdvHash := Classical.decPred _

/-- A query of the adversary in a class of the game's queries. -/
def IsAdvQuery (R : OracleWorld.Domain → Prop) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl input => R input
  | .inr _ => False

noncomputable instance (R : OracleWorld.Domain → Prop) : DecidablePred (IsAdvQuery R) :=
  Classical.decPred _

/-- An encoding query of the adversary. -/
def IsAdvEncoding (parameter : PublicParameter) : (OracleWorld + SigningSpec).Domain → Prop :=
  IsAdvQuery (CappedEncodingMonitor.IsEncodingHashQuery parameter)

noncomputable instance (parameter : PublicParameter) : DecidablePred (IsAdvEncoding parameter) :=
  Classical.decPred _

abbrev State := (QueryCache HashSpec × SigningCacheTrace) × ℕ

/-- The count after a query. -/
noncomputable def tick (input : (OracleWorld + SigningSpec).Domain) (k : ℕ) : ℕ :=
  if IsAdvHash input then k + 1 else k

/-- The traced handler with the ghost count of adversary hash queries. -/
noncomputable def impl (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp) :=
  QueryImpl.extendState (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    fun input _ _ _ k => tick input k

variable (publicKey : PublicKey) (secretKey : SecretKey)

theorem impl_run (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (k : ℕ) :
    (impl publicKey secretKey input).run ((cache, trace), k) =
      (fun r => (r.1, ((r.2, signingCacheTraceUpdate input cache r.1 r.2 trace), tick input k))) <$>
        (simulateQ romImpl (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input)).run
          cache := by
  rw [impl, QueryImpl.extendState_apply, cappedCacheTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, CappedEncodingMonitor.cappedUnloggedMappedAdversaryImpl_eq_source_compose]
  simp only [QueryImpl.apply_compose, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem source_world (input : OracleWorld.Domain) :
    cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey (.inl input) =
      liftM (OracleWorld.query input) := rfl

theorem source_sign (request : SignRequest) :
    cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      Concrete.scheme.sign secretKey request.leafIndex request.message := rfl

theorem simulateQ_source_world (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey (.inl input))).run
      cache = (romImpl input).run cache := by
  rw [source_world]
  change (simulateQ romImpl (liftM (OracleWorld.query input) :
    OracleComp OracleWorld (OracleWorld.Range input))).run cache = _
  rw [simulateQ_spec_query]

theorem expect_world (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (k : ℕ) (F : State → ℝ≥0∞) :
    ∑' r, Pr{let x ← (impl publicKey secretKey (.inl input)).run ((cache, trace), k)}[x = r] * F r.2 =
      ∑' r, Pr{let x ← (romImpl input).run cache}[x = r] * F ((r.2, trace), tick (.inl input) k) := by
  rw [impl_run, OracleComp.tsum_prEvent_map_mul, simulateQ_source_world]
  rfl

theorem expect_sign (request : SignRequest) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (k : ℕ) (F : State → ℝ≥0∞) :
    ∑' r, Pr{let x ← (impl publicKey secretKey (.inr request)).run ((cache, trace), k)}[x = r] * F r.2 =
      ∑' r, Pr{let x ← ((simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex
          request.message)).run cache)}[x = r] *
        F ((r.2, trace ++ [⟨request, r.1, cache, r.2⟩]), k) := by
  rw [impl_run, OracleComp.tsum_prEvent_map_mul]
  simp [tick, IsAdvHash, signingCacheTraceUpdate, source_sign]

theorem mem_support_world {input : OracleWorld.Domain} {cache : QueryCache HashSpec}
    {trace : SigningCacheTrace} {k : ℕ} {r}
    (hr : r ∈ support ((impl publicKey secretKey (.inl input)).run ((cache, trace), k))) :
    ∃ r0 ∈ support ((romImpl input).run cache), r = (r0.1, ((r0.2, trace), tick (.inl input) k)) := by
  rw [impl_run, support_map, simulateQ_source_world] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  exact ⟨r0, hr0, rfl⟩

/-- An output of a query comes from an output of the source handler on it.

The new state records the handler's cache, the updated trace and the counted query.

It holds for any query, so the kernel checks it without running the signer. -/
private theorem mem_support_impl {input : (OracleWorld + SigningSpec).Domain}
    {cache : QueryCache HashSpec} {trace : SigningCacheTrace} {k : ℕ} {r}
    (hr : r ∈ support ((impl publicKey secretKey input).run ((cache, trace), k))) :
    ∃ r0 ∈ support ((simulateQ romImpl
        (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input)).run cache),
      r = (r0.1, ((r0.2, signingCacheTraceUpdate input cache r0.1 r0.2 trace), tick input k)) := by
  rw [impl_run, support_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  exact ⟨r0, hr0, rfl⟩

/-- The source handler runs the scheme's signer on a signing query.

A proof rewrites with it, so the kernel compares the two forms as computations. -/
private theorem simulateQ_source_sign_run (request : SignRequest) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
        (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey (.inr request))).run cache =
      ((simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex request.message)).run
        cache : ProbComp (Option Signature × QueryCache HashSpec)) :=
  rfl

theorem mem_support_sign {request : SignRequest} {cache : QueryCache HashSpec}
    {trace : SigningCacheTrace} {k : ℕ} {r}
    (hr : r ∈ support ((impl publicKey secretKey (.inr request)).run ((cache, trace), k))) :
    ∃ r0 ∈ support ((simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex
        request.message)).run cache),
      r = (r0.1, ((r0.2, trace ++ [⟨request, r0.1, cache, r0.2⟩]), k)) := by
  -- Step through lemmas for any query: the kernel would run the signer to match two forms.
  obtain ⟨⟨output, finalCache⟩, hr0, rfl⟩ := mem_support_impl publicKey secretKey hr
  rw [simulateQ_source_sign_run] at hr0
  exact ⟨_, mem_support_range_inr request _ output finalCache hr0,
    by simp [tick, IsAdvHash, signingCacheTraceUpdate]⟩

/-- Forgetting the count gives the source game's adversary run. -/
theorem impl_run_proj (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (fun r => (r.1, r.2.1.1)) <$> (simulateQ (impl publicKey secretKey) computation).run ((cache, []), 0) =
      (simulateQ romImpl (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        computation)).run cache := by
  rw [← CappedEncodingMonitor.cappedUnloggedMappedAdversary_simulateQ_run_eq_source,
    ← cappedCacheTracedMappedAdversaryImpl_cache_projection publicKey secretKey computation cache [],
    ← OracleComp.extendState_run_proj_eq (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
      (fun input _ _ _ k => tick input k) computation (cache, []) 0, Functor.map_map]
  rfl

theorem simulateQ_source_query_bind (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input >>= fun r =>
        simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) (next r) := by
  simp [simulateQ_bind]

/-- The cost of an adversary hash query made with the budget `Q` spent. -/
noncomputable def overBudget (Q : ℕ) (input : (OracleWorld + SigningSpec).Domain) (s : State) : ℝ≥0∞ :=
  if IsAdvHash input ∧ Q ≤ s.2 then ⊤ else 0

/-- The budget is never exceeded. -/
theorem expectedSimulatedCost_overBudget_eq_zero (Q : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (k : ℕ),
      HashQueryBound (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        computation) cache (Q - k) → k ≤ Q →
      expectedSimulatedCost (impl publicKey secretKey) (overBudget Q) computation ((cache, trace), k) = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      intro cache trace k hbound hk
      rw [simulateQ_source_query_bind] at hbound
      rw [expectedSimulatedCost_query_bind]
      cases input with
      | inl world =>
          have hb : HashQueryBound (liftM (OracleWorld.query world) >>= fun r =>
              simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) (next r))
              cache (Q - k) := hbound
          obtain ⟨r1, hr1⟩ := probComp_support_nonempty ((romImpl world).run cache)
          have hfirst := (hashQueryBound_query_bind world _ cache (Q - k) hb r1 hr1).1
          have hcost : overBudget Q (.inl world) ((cache, trace), k) = 0 := by
            unfold overBudget
            rw [ite_eq_right]
            rintro ⟨hadv, hQ⟩
            cases world with
            | inl _ => exact hadv
            | inr _ => simp at hfirst; omega
          rw [hcost, zero_add]
          refine tsum_eq_zero_iff.2 fun r => ?_
          by_cases hr : r ∈ support ((impl publicKey secretKey (.inl world)).run ((cache, trace), k))
          · obtain ⟨r0, hr0, rfl⟩ := mem_support_world publicKey secretKey hr
            have hnext := (hashQueryBound_query_bind world _ cache (Q - k) hb r0 hr0).2
            rw [ih r0.1 r0.2 trace _ _ _, mul_zero]
            · cases world with
              | inl _ => simpa [tick, IsAdvHash] using hnext
              | inr _ => simpa [tick, IsAdvHash, Nat.sub_sub] using hnext
            · cases world with
              | inl _ => simpa [tick, IsAdvHash] using hk
              | inr _ => simp at hfirst; simp [tick, IsAdvHash]; omega
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul]
      | inr request =>
          have hcost : overBudget Q (.inr request) ((cache, trace), k) = 0 := by
            unfold overBudget; rw [ite_eq_right]; rintro ⟨hadv, _⟩; exact hadv
          rw [hcost, zero_add]
          refine tsum_eq_zero_iff.2 fun r => ?_
          by_cases hr : r ∈ support ((impl publicKey secretKey (.inr request)).run ((cache, trace), k))
          · -- Keep the handler's form of the query: the kernel would run the signer to match two.
            obtain ⟨r0, hr0, rfl⟩ := mem_support_impl publicKey secretKey hr
            have htick : tick (.inr request) k = k := by simp [tick, IsAdvHash]
            rw [htick, ih r0.1 r0.2 _ k (hashQueryBound_bind_right _ _ cache _ hbound r0 hr0) hk,
              mul_zero]
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul]

/-- The budget is never exceeded, under a bound on the adversary's own hash queries. -/
theorem expectedSimulatedCost_overBudget_eq_zero_of_isQueryBoundP (Q : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (n : ℕ) (s : State), IsQueryBoundP computation IsAdvHash n → s.2 + n ≤ Q →
      expectedSimulatedCost (impl publicKey secretKey) (overBudget Q) computation s = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      rintro n ⟨⟨cache, trace⟩, k⟩ hbound hk
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [expectedSimulatedCost_query_bind]
      have hcost : overBudget Q input ((cache, trace), k) = 0 := by
        unfold overBudget
        rw [ite_eq_right]
        rintro ⟨hadv, hQ⟩
        have := hbound.1.resolve_left (not_not.2 hadv)
        dsimp only at hk
        omega
      rw [hcost, zero_add]
      refine tsum_eq_zero_iff.2 fun r => ?_
      by_cases hr : r ∈ support ((impl publicKey secretKey input).run ((cache, trace), k))
      · obtain ⟨r0, hr0, rfl⟩ := mem_support_impl publicKey secretKey hr
        refine mul_eq_zero_of_right _ (ih r0.1 _ _ (hbound.2 r0.1) ?_)
        dsimp only at hk ⊢
        unfold tick
        split_ifs with h
        · have := hbound.1.resolve_left (not_not.2 h)
          omega
        · exact hk
      · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul]

/-- A run's expected cost is at most a bound on the queries that each cost at most one. -/
theorem expectedSimulatedCost_le_of_isQueryBoundP {ι σ : Type} {spec : OracleSpec ι}
    (implementation : QueryImpl spec (StateT σ ProbComp)) {p : ι → Prop} [DecidablePred p]
    {cost : ι → σ → ℝ≥0∞} (hcost : ∀ input s, cost input s ≤ if p input then 1 else 0)
    (computation : OracleComp spec α) :
    ∀ (n : ℕ) (s : σ), IsQueryBoundP computation p n →
      expectedSimulatedCost implementation cost computation s ≤ n := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      intro n s hbound
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [expectedSimulatedCost_query_bind]
      calc _ ≤ (if p input then 1 else 0) + ∑' r, Pr{let x ← (implementation input).run s}[x = r] *
            ((if p input then n - 1 else n : ℕ) : ℝ≥0∞) :=
          add_le_add (hcost input s)
            (tsum_le_tsum fun r => mul_le_mul' le_rfl (ih r.1 _ r.2 (hbound.2 r.1)))
        _ ≤ (if p input then 1 else 0) + ((if p input then n - 1 else n : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.tsum_mul_right]
          exact add_le_add le_rfl (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _))
        _ ≤ n := by
          split_ifs with h
          · have := hbound.1.resolve_left (not_not.2 h)
            rw [← Nat.cast_one, ← Nat.cast_add]
            exact_mod_cast (by omega : 1 + (n - 1) ≤ n)
          · simp

/-- An encoding query of the adversary is one of its hash queries. -/
theorem isAdvHash_of_isAdvEncoding {parameter : PublicParameter} :
    ∀ {input : (OracleWorld + SigningSpec).Domain}, IsAdvEncoding parameter input → IsAdvHash input
  | .inl (.inr _), _ => trivial
  | .inl (.inl _), h => h.elim
  | .inr _, h => h.elim

/-- One query of the game counts one in a class that holds it, and none otherwise. -/
theorem expectedSimulatedQueryCount_liftM_query_eq (R : OracleWorld.Domain → Prop)
    [DecidablePred R] (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl R
        (liftM (OracleWorld.query input) : OracleComp OracleWorld _) cache =
      if R input then 1 else 0 := by
  rw [← bind_pure (liftM (OracleWorld.query input) : OracleComp OracleWorld _),
    expectedSimulatedQueryCount_query_bind]
  simp

/-- The cost of a query in a class.

It is one for an adversary query in the class, and the signer's expected count for a request. -/
noncomputable def sourceCost (R : OracleWorld.Domain → Prop) [DecidablePred R] :
    (OracleWorld + SigningSpec).Domain → State → ℝ≥0∞
  | .inl input, _ => if R input then 1 else 0
  | .inr request, s => expectedSimulatedQueryCount romImpl R
      (Concrete.scheme.sign secretKey request.leafIndex request.message) s.1.1

/-- The source game's count of a class is the adversary's queries in it plus the signer's. -/
theorem expectedSimulatedQueryCount_source_eq (R : OracleWorld.Domain → Prop) [DecidablePred R]
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (k : ℕ),
      expectedSimulatedQueryCount romImpl R
          (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation)
          cache =
        expectedSimulatedCost (impl publicKey secretKey) (sourceCost secretKey R) computation
          ((cache, trace), k) := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      intro cache trace k
      rw [expectedSimulatedCost_query_bind, simulateQ_source_query_bind,
        expectedSimulatedQueryCount_bind, impl_run, OracleComp.tsum_prEvent_map_mul]
      congr 1
      · cases input with
        | inl world =>
            rw [source_world]
            exact expectedSimulatedQueryCount_liftM_query_eq R world cache
        | inr request => rfl
      · exact tsum_congr fun r => by rw [ih r.1 r.2 _ _]

/-- With a signer that makes no query in the class, the source game counts only the adversary's. -/
theorem expectedSimulatedQueryCount_source_le_adv (R : OracleWorld.Domain → Prop)
    [DecidablePred R]
    (hsign : ∀ request : SignRequest,
      IsQueryBoundP (Concrete.scheme.sign secretKey request.leafIndex request.message) R 0)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (k : ℕ) :
    expectedSimulatedQueryCount romImpl R
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation)
        cache ≤
      expectedSimulatedCost (impl publicKey secretKey)
        (fun input _ => if IsAdvQuery R input then 1 else 0) computation ((cache, trace), k) := by
  rw [expectedSimulatedQueryCount_source_eq publicKey secretKey R computation cache trace k]
  refine expectedSimulatedCost_mono _ (fun input s => ?_) computation _
  cases input with
  | inl world =>
      by_cases h : R world
      · rw [ite_eq_left (show IsAdvQuery R (.inl world) from h)]
        exact (ite_eq_left h).le
      · rw [ite_eq_right (show ¬IsAdvQuery R (.inl world) from h)]
        exact (ite_eq_right h).le
  | inr request =>
      -- The signer's count is at most its query bound, which is zero.
      refine le_trans ?_ zero_le
      rw [sourceCost, ← expectedSimulatedCost_indicator]
      exact_mod_cast expectedSimulatedCost_le_of_isQueryBoundP romImpl (fun _ _ => le_rfl) _ 0
        s.1.1 (hsign request)

/-- The source game counts the adversary's encoding queries. -/
theorem expectedSimulatedCost_advEncoding_le (parameter : PublicParameter)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (k : ℕ),
      expectedSimulatedCost (impl publicKey secretKey)
          (fun input _ => if IsAdvEncoding parameter input then 1 else 0) computation ((cache, trace), k) ≤
        expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery parameter)
          (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation) cache := by
  intro cache trace k
  rw [expectedSimulatedQueryCount_source_eq publicKey secretKey _ computation cache trace k]
  refine expectedSimulatedCost_mono _ (fun input s => ?_) computation _
  cases input with
  | inl world =>
      by_cases h : CappedEncodingMonitor.IsEncodingHashQuery parameter world
      · rw [ite_eq_left (show IsAdvEncoding parameter (.inl world) from h)]
        exact (ite_eq_left h).ge
      · rw [ite_eq_right (show ¬IsAdvEncoding parameter (.inl world) from h)]
        exact zero_le
  | inr request =>
      rw [ite_eq_right (show ¬IsAdvEncoding parameter (.inr request) from id)]
      exact zero_le

end XmssSecurity.Ghost
