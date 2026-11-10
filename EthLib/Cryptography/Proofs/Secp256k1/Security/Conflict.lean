module

public import EthLib.Cryptography.Proofs.BadOnBudget
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Programmed
public import EthLib.Cryptography.Proofs.Secp256k1.Security.QueryBound

/-!
# Proofs: the chance of a conflict in the ECDSA game with `Π` programmed

In the game with `Π` programmed, two pairs of the cache of `Π` may share a query or an answer.

That is a conflict, and this module bounds its chance.

Take an adversary with at most `q_Π` queries to `Π` or its inverse, and `q_S` signing queries.

The check of the forgery may relay one more query, so `Π` gets at most `q_Π + 1` relayed queries.

The signer programs `Π` at most `fuel` times per signing query.

So the cache holds at most `N = q_Π + 1 + fuel · q_S` pairs.

A relayed query gets a uniform answer outside the relayed answers.

It conflicts only when it hits one of the at most `fuel · q_S` programmed pairs.

So it conflicts with chance at most `fuel · q_S / (|A| - N)`.

That bound is infinite once `N` reaches `|A|`.

A nonzero nonce `k` programs the query `φ(k g)` with a uniform answer of `A`.

At most two nonzero nonces give one encoding, when `g` is nonzero and `φ` is semi-injective.

So the query is cached with chance at most `2 N / |F|`, over a nonce drawn from all scalars.

A zero nonce programs nothing, so it adds nothing to that chance.

The answer is cached with chance at most `N / |A|`.

A signing query tries at most `fuel` nonces.

The union bound over all queries adds these chances.

It is a union bound with a potential on the pair of budgets that remain.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

Their aborts in lines 05, 11, 13 and 25 of Figure 5 are conflicts here.

The proof of their Theorem 1, §4.1, bounds the chance of each of these aborts.

Their term for line 11 is `2 Q_s Q / (q - 1)`, with a nonzero nonce, where `q` is the group order.

Their signer tries one nonce, so their counts of `Q_s` programmed pairs become `fuel · Q_s` here.

The check of the forgery relays one more query, which their Definition 4 rules out.

So their `Q_Π` becomes `q_Π + 1` here.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- The bound on the chance of a conflict.

Its arguments are the scalars `F`, the set `A` that `Π` permutes, and `fuel`.

Then come the queries `q_Π` to `Π` or its inverse, and the signing queries `q_S`.

Let `N = q_Π + 1 + fuel · q_S`, the most pairs that the cache of `Π` can hold.

Each of the `q_Π + 1` relayed queries adds `fuel · q_S / (|A| - N)`.

The difference is of natural numbers, so the bound is infinite once `N` reaches `|A|`.

Each of the `q_S` signing queries adds `fuel` times `2 N / |F| + N / |A|`. -/
noncomputable def conflictBound (F A : Type) [FinEnum F] [FinEnum A] (fuel qPerm qSign : ℕ) :
    ℝ≥0∞ :=
  let N : ℕ := qPerm + 1 + fuel * qSign
  ((qPerm + 1 : ℕ) : ℝ≥0∞) * (((fuel * qSign : ℕ) : ℝ≥0∞) / ((FinEnum.card A - N : ℕ) : ℝ≥0∞)) +
    (qSign : ℝ≥0∞) * ((fuel : ℝ≥0∞) *
      (2 * (N : ℝ≥0∞) / FinEnum.card F + (N : ℝ≥0∞) / FinEnum.card A))

/-! ## The query budget of the run with its check -/

section

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]

/-- The run with its check asks `Π` or its inverse at most once more than the adversary.

It asks for signatures as often as the adversary. -/
private theorem isQueryBound_runWithCheck [DecidableEq G] (scheme : Scheme F G A M)
    (adversary : Adversary F G A M) (X : G) {qPerm qSign : ℕ}
    (hPerm : IsQueryBoundP (adversary.main X) (isPermQuery · = true) qPerm)
    (hSign : IsQueryBoundP (adversary.main X) (isSignQuery · = true) qSign) :
    IsQueryBound (runWithCheck scheme adversary X) (qPerm + 1, qSign)
      (fun t b => (¬isPermQuery t = true ∨ 0 < b.1) ∧ (¬isSignQuery t = true ∨ 0 < b.2))
      (fun t b => (if isPermQuery t = true then b.1 - 1 else b.1,
        if isSignQuery t = true then b.2 - 1 else b.2)) := by
  refine IsQueryBoundP.and_isQueryBound_pair ?_ ?_
  · refine isQueryBoundP_bind hPerm fun z _ => isQueryBoundP_bind (m := 0)
      ((isQueryBoundP_verifyQ scheme _ _ _ _).simulateQ_of_step ?_ ?_)
      fun _ _ => isQueryBoundP_pure _ _ _
    all_goals rintro (n | a | b) ht <;>
      simp only [keyOnlyLift_inl, keyOnlyLift_inr_inl, keyOnlyLift_inr_inr] <;>
      exact (isQueryBoundP_query_iff _ _ _).2 (by simp_all [isPermQuery])
  · refine isQueryBoundP_bind (m := 0) hSign fun z _ => isQueryBoundP_bind (m := 0)
      (isQueryBoundP_simulateQ_zero _ ?_) fun _ _ => isQueryBoundP_pure _ _ _
    rintro (n | a | b) <;> exact (isQueryBoundP_query_iff _ _ _).2 (by simp [isSignQuery])

/-! ## A query of `Π` within the budgets -/

variable [FinEnum A]

/-- A query to the overlay keeps the invariant of the budgets, with one query of `Π` spent. -/
private theorem overlayLazyOracle_budget_step {σ : Type} (sc : σ) (q : (PermSpec A).Domain)
    {fuel qPerm qSign p k : ℕ} {c : ProgrammedCache A} {l : PermCache A} (hl : l = c.relayed)
    (hR : c.relayed.length + (p + 1) ≤ qPerm + 1)
    (hP : c.length + fuel * k ≤ fuel * qSign + c.relayed.length) (z)
    (hz : z ∈ support ((fun z => (z.1, (sc, z.2))) <$> (overlayLazyOracle q).run (c, l))) :
    z.2.2.2 = z.2.2.1.relayed ∧ z.2.2.1.relayed.length + p ≤ qPerm + 1 ∧
      z.2.2.1.length + fuel * k ≤ fuel * qSign + z.2.2.1.relayed.length := by
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases overlayLazyOracle_step _ (c, l) w hw with h | ⟨q, h₁, h₂⟩
  · rw [h]
    dsimp only
    exact ⟨hl, by omega, by omega⟩
  · rw [h₁, h₂ hl, ProgrammedCache.relayed_cons_false, hl]
    simp only [List.length_cons, true_and]
    omega

/-- A query to the overlay, within the budgets, makes a conflict with a bounded chance.

The bound is `fuel · q_S` over `|A| - N`, with `N = q_Π + 1 + fuel · q_S`. -/
private theorem prEvent_overlayLazyOracle_budget_le {σ : Type} (sc : σ)
    (q : (PermSpec A).Domain) {fuel qPerm qSign p k : ℕ} {c : ProgrammedCache A}
    (hc : ¬c.Conflict) (hR : c.relayed.length + (p + 1) ≤ qPerm + 1)
    (hP : c.length + fuel * k ≤ fuel * qSign + c.relayed.length) :
    Pr{let z ← (fun z => (z.1, (sc, z.2))) <$> (overlayLazyOracle q).run (c, c.relayed)}[
        z.2.2.1.Conflict] ≤
      ((fuel * qSign : ℕ) : ℝ≥0∞) /
        ((FinEnum.card A - (qPerm + 1 + fuel * qSign) : ℕ) : ℝ≥0∞) := by
  have hlen := c.length_eq_length_relayed_add
  rw [prEvent_map]
  exact (prEvent_overlayLazyOracle_conflict_le q c hc).trans
    (ENNReal.div_le_div (Nat.cast_le.2 (by omega)) (Nat.cast_le.2 (by omega)))

/-! ## The nonces of a signing query -/

/-- A run beside the programming oracle keeps the lazy cache and the relayed pairs.

It adds at most one pair per query of `Π`. -/
private theorem state_of_mem_support_programPermImpl {α : Type} {oa : PermComp A α} {n : ℕ}
    (h : IsQueryBoundP oa (·.isRight = true) n) (c : ProgrammedCache A) (l : PermCache A) (z)
    (hz : z ∈ support ((simulateQ programPermImpl oa).run (c, l))) :
    z.2.2 = l ∧ z.2.1.relayed = c.relayed ∧ z.2.1.length ≤ c.length + n := by
  have hinv : QueryImpl.PreservesInv programPermImpl
      fun s : ProgrammedCache A × PermCache A => s.2 = l ∧ s.1.relayed = c.relayed :=
    (preservesInv_passthrough _).add fun q s hs w hw => by
      obtain ⟨p, hp⟩ := programPermOracle_step q s w hw
      rw [hp]
      exact ⟨hs.1, by simpa using hs.2⟩
  have hs := simulateQ_run_preservesInv _ _ hinv oa _ ⟨rfl, rfl⟩ z hz
  refine ⟨hs.1, hs.2, h.cost_le_of_mem_support_run_simulateQ (fun s => s.1.length) ?_ ?_ _ z hz⟩
  · rintro (n | q) hq s w hw
    · simp at hq
    · obtain ⟨p, hp⟩ := programPermOracle_step q s w hw
      rw [hp]
      simp
  · rintro (n | q) hq s w hw
    · rw [passthrough_add_inl_run] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨_, -, rfl⟩ := hw
      exact le_refl _
    · simp at hq

variable [SampleableType F]

/-- Signing with one more nonce tries a nonce, and stops or signs with the others. -/
private theorem simulateQ_programPermImpl_signFreshQ_succ_run (scheme : Scheme F G A M) (x : F)
    (m : M) (n : ℕ) (s : ProgrammedCache A × PermCache A) :
    (simulateQ programPermImpl (signFreshQ scheme x m (n + 1))).run s =
      (($ᵗ F : ProbComp F) >>= fun k =>
        (simulateQ programPermImpl (signNonceQ scheme x m k)).run s) >>= fun z =>
        match z.1 with
        | some σ => pure (some σ, z.2)
        | none => (simulateQ programPermImpl (signFreshQ scheme x m n)).run z.2 := by
  simp only [signFreshQ, simulateQ_bind, StateT.run_bind, simulateQ_passthrough_add_liftM_run,
    bind_map_left, bind_assoc]
  refine bind_congr fun k => bind_congr fun z => ?_
  rcases z with ⟨_ | σ, s'⟩ <;> simp

variable [FinEnum F]

/-- A uniform scalar is nonzero and has the encoding of its multiple of `g` in a list rarely.

The chance is at most twice the length of the list over `|F|`. -/
private theorem prEvent_encode_smul_mem_le (scheme : Scheme F G A M) (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (L : List A) :
    Pr{let k ← ($ᵗ F : ProbComp F)}[k ≠ 0 ∧ scheme.encode (k • scheme.g) ∈ L] ≤
      2 * (L.length : ℝ≥0∞) / FinEnum.card F := by
  induction L with
  | nil => simp
  | cons α L ih =>
    have hα : Pr{let k ← ($ᵗ F : ProbComp F)}[k ≠ 0 ∧ scheme.encode (k • scheme.g) = α] ≤
        2 / FinEnum.card F := by
      by_cases h : ∃ k₀ : F, k₀ ≠ 0 ∧ scheme.encode (k₀ • scheme.g) = α
      · obtain ⟨k₀, hk₀, rfl⟩ := h
        refine (prEvent_mono _ _ (fun k : F => k = k₀ ∨ k = -k₀) fun k ⟨hk, h⟩ =>
          Scheme.eq_or_eq_neg_of_encode_smul_eq hsemi hg hk₀ hk h).trans
          ((prEvent_or_le _ _ _).trans (le_of_eq ?_))
        rw [SampleableType.prEvent_uniformSample_eq_singleton,
          SampleableType.prEvent_uniformSample_eq_singleton, FinEnum.card_eq_fintypeCard,
          ← two_mul, div_eq_mul_inv]
      · exact (prEvent_eq_zero_of_forall_not ($ᵗ F : ProbComp F) _
          fun k hk => h ⟨k, hk⟩).trans_le zero_le
    refine (prEvent_mono _ _ (fun k => (k ≠ 0 ∧ scheme.encode (k • scheme.g) = α) ∨
        (k ≠ 0 ∧ scheme.encode (k • scheme.g) ∈ L)) fun k ⟨hk, h⟩ => ?_).trans
      ((prEvent_or_le _ _ _).trans ((add_le_add hα ih).trans (le_of_eq ?_)))
    · rw [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one, ENNReal.add_div,
        add_comm]
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨hk, h⟩

/-- One nonce, from a cache with no conflict, makes one with a bounded chance.

The chance is at most twice the size of the cache over `|F|`, plus the size over `|A|`. -/
private theorem prEvent_nonce_conflict_le (scheme : Scheme F G A M) (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (x : F) (m : M) (c : ProgrammedCache A) (l : PermCache A)
    (hc : ¬c.Conflict) :
    Pr{let z ← ($ᵗ F : ProbComp F) >>= fun k =>
        (simulateQ programPermImpl (signNonceQ scheme x m k)).run (c, l)}[z.2.1.Conflict] ≤
      2 * (c.length : ℝ≥0∞) / FinEnum.card F + (c.length : ℝ≥0∞) / FinEnum.card A := by
  refine (prEvent_bind_le_prEvent_add_of_support _ _
    (fun k => k ≠ 0 ∧ scheme.encode (k • scheme.g) ∈ (TaggedCache.untag c).map Prod.fst) _
    fun k _ hk => ?_).trans (add_le_add_left ?_ _)
  · by_cases hk0 : k = 0
    · subst hk0
      simp [signNonceQ, hc]
    · have hf := simulateQ_programPermImpl_signNonceQ_run scheme x m hk0 (c, l)
      rw [hf, prEvent_map]
      have hα := fun h => hk ⟨hk0, h⟩
      refine (prEvent_mono _ _ (fun b => b ∈ (TaggedCache.untag c).map Prod.snd)
        fun b hb => ?_).trans ((prEvent_uniformOutside_nil_mem_le _ _).trans (le_of_eq ?_))
      · by_contra hb'
        exact hb ((PermCache.isPartialBijection_cons_iff _ _).2 ⟨hα, hb', not_not.1 hc⟩)
      · simp [TaggedCache.untag]
  · exact (prEvent_encode_smul_mem_le scheme hg hsemi _).trans
      (le_of_eq (by simp [TaggedCache.untag]))

/-- Signing, from a cache with no conflict, makes one with a bounded chance.

Take a bound `L` on the size of the cache plus the number of nonces.

Each nonce adds at most twice `L` over `|F|`, plus `L` over `|A|`. -/
private theorem prEvent_signFreshQ_conflict_le (scheme : Scheme F G A M) (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (x : F) (m : M) (L n : ℕ) :
    ∀ (c : ProgrammedCache A) (l : PermCache A), ¬c.Conflict → c.length + n ≤ L →
      Pr{let z ← (simulateQ programPermImpl (signFreshQ scheme x m n)).run (c, l)}[
        z.2.1.Conflict] ≤
      (n : ℝ≥0∞) * (2 * (L : ℝ≥0∞) / FinEnum.card F + (L : ℝ≥0∞) / FinEnum.card A) := by
  induction n with
  | zero =>
    intro c l hc _
    simp [signFreshQ, hc]
  | succ n ih =>
    intro c l hc hL
    rw [simulateQ_programPermImpl_signFreshQ_succ_run]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z => z.2.1.Conflict) _
      (ε := (n : ℝ≥0∞) * (2 * (L : ℝ≥0∞) / FinEnum.card F + (L : ℝ≥0∞) / FinEnum.card A))
      fun z hz hzc => ?_).trans ?_
    · rw [mem_support_bind_iff] at hz
      obtain ⟨k, -, hz⟩ := hz
      have hlen := (state_of_mem_support_programPermImpl
        (isQueryBoundP_signNonceQ scheme x m k) c l z hz).2.2
      rcases z with ⟨_ | σ, c', l'⟩
      · exact ih c' l' hzc (by simp only at hlen; omega)
      · simp [hzc]
    · refine (add_le_add_left (prEvent_nonce_conflict_le scheme hg hsemi x m c l hc) _).trans ?_
      have hc : (c.length : ℝ≥0∞) ≤ L := by exact_mod_cast (by omega : c.length ≤ L)
      rw [Nat.cast_succ, add_mul, one_mul, add_comm (_ * _)]
      gcongr

end

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]
  [FinEnum F] [SampleableType F] [FinEnum A]

/-- **The chance of a conflict in the game with `Π` programmed.**

The adversary asks for `Π` or its inverse at most `q_Π` times, on every key.

It asks for signatures at most `q_S` times, on every key.

The base point must be nonzero, and the encoding semi-injective.

Then a conflict in the final cache of `Π` has chance at most the bound on a conflict.

That bound reads the sizes of `F` and `A`, `fuel`, `q_Π` and `q_S`. -/
theorem prEvent_programmedExperiment_conflict_le {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (fuel : ℕ) (adversary : Adversary F G A M) {qPerm qSign : ℕ}
    (hPerm : ∀ X, IsQueryBoundP (adversary.main X) (isPermQuery · = true) qPerm)
    (hSign : ∀ X, IsQueryBoundP (adversary.main X) (isSignQuery · = true) qSign) :
    Pr{let z ← programmedExperiment scheme fuel adversary}[z.2.2.1.Conflict] ≤
      conflictBound F A fuel qPerm qSign := by
  set N : ℕ := qPerm + 1 + fuel * qSign with hN
  set εR : ℝ≥0∞ :=
    ((fuel * qSign : ℕ) : ℝ≥0∞) / ((FinEnum.card A - N : ℕ) : ℝ≥0∞) with hεR
  set εS : ℝ≥0∞ :=
    (fuel : ℝ≥0∞) * (2 * (N : ℝ≥0∞) / FinEnum.card F + (N : ℝ≥0∞) / FinEnum.card A) with hεS
  have hbound : conflictBound F A fuel qPerm qSign =
      ((qPerm + 1 : ℕ) : ℝ≥0∞) * εR + (qSign : ℝ≥0∞) * εS := rfl
  rw [hbound, programmedExperiment]
  refine prEvent_bind_le_of_forall_le _ _ _ fun x => ?_
  refine prEvent_bad_le_of_isQueryBound
    (impl := jointImpl overlayLazyOracle
      (liftFresh programPermOracle fun m => signFreshQ scheme x m fuel))
    (fun b s => s.2.2 = s.2.1.relayed ∧ s.2.1.relayed.length + b.1 ≤ qPerm + 1 ∧
      s.2.1.length + fuel * b.2 ≤ fuel * qSign + s.2.1.relayed.length)
    (fun s => s.2.1.Conflict) (fun b => (b.1 : ℝ≥0∞) * εR + (b.2 : ℝ≥0∞) * εS) ?_ ?_
    (isQueryBound_runWithCheck scheme adversary _ (hPerm _) (hSign _))
    (s := (([] : Cache F M), (([] : ProgrammedCache A), ([] : PermCache A))))
    ⟨rfl, by simp [ProgrammedCache.relayed, TaggedCache.untag],
      by simp [ProgrammedCache.relayed, TaggedCache.untag]⟩
    (by simp [ProgrammedCache.Conflict, PermCache.IsPartialBijection, TaggedCache.untag])
  · rintro t ⟨p, k⟩ ⟨sc, c, l⟩ ⟨hp, hk⟩ ⟨hl, hR, hP⟩ - z hz -
    simp only at hl hR hP
    rcases t with n | a | b | m
    · change z ∈ support ((·, (sc, (c, l))) <$>
        (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp only [isPermQuery, isSignQuery, Bool.false_eq_true, ite_false]
      exact ⟨hl, hR, hP⟩
    · change z ∈ support ((fun z => (z.1, (sc, z.2))) <$>
        (overlayLazyOracle (.inl a)).run (c, l)) at hz
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
        (by simpa [isPermQuery] using hp : 0 < p).ne'
      simp only [isPermQuery, isSignQuery, ite_true, Bool.false_eq_true, ite_false,
        Nat.add_sub_cancel]
      exact overlayLazyOracle_budget_step sc (.inl a) hl hR hP _ hz
    · change z ∈ support ((fun z => (z.1, (sc, z.2))) <$>
        (overlayLazyOracle (.inr b)).run (c, l)) at hz
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
        (by simpa [isPermQuery] using hp : 0 < p).ne'
      simp only [isPermQuery, isSignQuery, ite_true, Bool.false_eq_true, ite_false,
        Nat.add_sub_cancel]
      exact overlayLazyOracle_budget_step sc (.inr b) hl hR hP _ hz
    · change z ∈ support (match sc.lookup m with
          | some a => pure (a, (sc, (c, l)))
          | none => (fun z : Option (F × F) × (ProgrammedCache A × PermCache A) =>
              (z.1, (sc ++ [(m, z.1)], z.2))) <$>
            (liftFresh programPermOracle (fun m => signFreshQ scheme x m fuel) m).run (c, l))
        at hz
      have hk' : 0 < k := by simpa [isSignQuery] using hk
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk'.ne'
      simp only [isPermQuery, isSignQuery, ite_true, Bool.false_eq_true, ite_false,
        Nat.add_sub_cancel]
      rw [Nat.mul_succ] at hP
      rcases h : sc.lookup m with _ | a <;> rw [h] at hz
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        obtain ⟨h₁, h₂, h₃⟩ := state_of_mem_support_programPermImpl
          (isQueryBoundP_signFreshQ scheme x m fuel) c l w hw
        dsimp only
        rw [h₁, h₂, hl]
        exact ⟨rfl, hR, by omega⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        dsimp only
        exact ⟨hl, hR, by omega⟩
  · rintro t ⟨p, k⟩ ⟨sc, c, l⟩ ⟨hp, hk⟩ ⟨hl, hR, hP⟩ hc
    simp only at hl hR hP hc
    subst hl
    rcases t with n | a | b | m
    · change Pr{let z ← (·, (sc, (c, c.relayed))) <$>
        (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))}[z.2.2.1.Conflict] + _ ≤ _
      rw [prEvent_map]
      simp [hc, isPermQuery, isSignQuery]
    · change Pr{let z ← (fun z => (z.1, (sc, z.2))) <$>
        (overlayLazyOracle (.inl a)).run (c, c.relayed)}[z.2.2.1.Conflict] + _ ≤ _
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
        (by simpa [isPermQuery] using hp : 0 < p).ne'
      simp only [isPermQuery, isSignQuery, ite_true, Bool.false_eq_true, ite_false,
        Nat.add_sub_cancel]
      refine (add_le_add_left (prEvent_overlayLazyOracle_budget_le sc _ hc hR hP) _).trans
        (le_of_eq ?_)
      change εR + _ = _
      push_cast
      ring
    · change Pr{let z ← (fun z => (z.1, (sc, z.2))) <$>
        (overlayLazyOracle (.inr b)).run (c, c.relayed)}[z.2.2.1.Conflict] + _ ≤ _
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
        (by simpa [isPermQuery] using hp : 0 < p).ne'
      simp only [isPermQuery, isSignQuery, ite_true, Bool.false_eq_true, ite_false,
        Nat.add_sub_cancel]
      refine (add_le_add_left (prEvent_overlayLazyOracle_budget_le sc _ hc hR hP) _).trans
        (le_of_eq ?_)
      change εR + _ = _
      push_cast
      ring
    · change Pr{let z ← (match sc.lookup m with
          | some a => pure (a, (sc, (c, c.relayed)))
          | none => (fun z : Option (F × F) × (ProgrammedCache A × PermCache A) =>
              (z.1, (sc ++ [(m, z.1)], z.2))) <$>
            (liftFresh programPermOracle (fun m => signFreshQ scheme x m fuel) m).run
              (c, c.relayed))}[z.2.2.1.Conflict] + _ ≤ _
      have hk' : 0 < k := by simpa [isSignQuery] using hk
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk'.ne'
      simp only [isPermQuery, isSignQuery, ite_true, Bool.false_eq_true, ite_false,
        Nat.add_sub_cancel]
      rw [Nat.mul_succ] at hP
      have hle : ((p : ℝ≥0∞) * εR + (k : ℝ≥0∞) * εS) + εS =
          (p : ℝ≥0∞) * εR + ((k + 1 : ℕ) : ℝ≥0∞) * εS := by
        push_cast
        ring
      rcases h : sc.lookup m with _ | a
      · rw [prEvent_map, ← hle, add_comm _ εS]
        refine add_le_add_left ?_ _
        exact prEvent_signFreshQ_conflict_le scheme hg hsemi x m N fuel c c.relayed hc (by omega)
      · show Pr{let z ← (pure (a, sc, c, c.relayed) : ProbComp _)}[z.2.2.1.Conflict] + _ ≤ _
        classical
        rw [prEvent_pure]
        simp only [hc, ↓reduceIte, zero_add, ← hle]
        exact le_self_add

end EthLib.Cryptography.Secp256k1.Security
