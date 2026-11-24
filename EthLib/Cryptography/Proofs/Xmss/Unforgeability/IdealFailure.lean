module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.IdealSearch

/-!
# Proofs: a bound on the failure of a signing request

In the ideal game of the derivations, a request may fail or leave a search without a codeword.

Its chance is at most `Q / 2^95 + 2 exp(-4000)`, as long as every earlier search found one.

Here `Q` bounds the game's hash calls on every run, and so the size of its cache.

With the two hidden-seed hops, this bounds the failure in the real game.

The bound then completes the one of the signer that tells why signing failed.

That signer keeps its key across requests, as the theorem's game does.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open XmssSecurity (HashSpec HashOutput)

open EthLib.Cryptography.Xmss

/-! ## Maps and public programs -/

/-- A map of the output fails when the output fails under the map. -/
theorem FailsAtMost.map {α β : Type} {fail : β → Prop} {Q : ℕ} {ε : ℝ≥0∞}
    {oa : OracleComp PrfSpec α} (f : α → β) (h : FailsAtMost (fun a => fail (f a)) Q ε oa) :
    FailsAtMost fail Q ε (f <$> oa) := by
  intro st hst
  rw [simulateQ_map, StateT.run_map, prEvent_map]
  exact h st hst

/-- A program with public queries only never fails, when no output counts as a failure. -/
theorem FailsAtMost.of_withDerivationsLift {α : Type} {Q : ℕ}
    (oa : OracleComp XmssSecurity.OracleWorld α) :
    FailsAtMost (fun _ => False) Q 0
      (simulateQ (HashSpec.withDerivationsLift PrfInput HashOutput) oa) := by
  rintro ⟨C, T⟩ hst
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hE => ?_)
  have hC := (le_of_mem_support_run_idealImpl _ hz).1
  rw [run_simulateQ_idealImpl_withDerivationsLift, support_map] at hz
  obtain ⟨w, -, rfl⟩ := hz
  rcases hE.1 with hf | hs
  · exact hf
  · exact hs (hst.mono hC fun _ _ _ _ => rfl)

/-- The verification of the second hop's game is the verification over `H`, lifted. -/
theorem verifyWith_hashD (pk : PublicKey) (msg : Message) (sig : Signature) :
    verifyWith hashD pk msg sig =
      simulateQ (HashSpec.withDerivationsLift PrfInput HashOutput)
        (verifyWith queryH pk msg sig : OracleComp XmssSecurity.OracleWorld Bool) := by
  rw [verifyWith_map_monad (simulateQ (HashSpec.withDerivationsLift PrfInput HashOutput))
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
  simp only [simulateQ_queryH]

/-! ## The adversary's run -/

/-- **Each request of the adversary adds its failure bound.**

The adversary makes at most `n` signing requests.

The key's kept trees must hold top signatures, as the key of key generation does.

Some request fails, or a search is left without a codeword, with chance `<= n` times a request's.

Count only the runs whose cache ends with at most `Q` entries. -/
theorem failsAtMost_run_failSignerOf (Q : ℕ) {α : Type}
    (oa : OracleComp (XmssSecurity.OracleWorld + ReasonSigningSpec) α) {n : ℕ}
    (h : IsQueryBoundP oa IsAdversaryRequest n) (sk : SecretKey) (hsk : KeptOk sk) :
    FailsAtMost (fun z : (α × SecretKey) × QueryLog SigningSpec => ∃ entry ∈ z.2, entry.2 = none)
      Q (n * ((Q : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000))))
      ((simulateQ (failSignerOf (HashSpec.withDerivationsLift PrfInput HashOutput) prfD) oa).run
        sk).run := by
  -- A union bound over the `r` requests bounds the chance of a failure.
  --
  -- It goes by induction on the adversary.
  --
  -- Every tree the key keeps holds a top signature, since no earlier request failed.
  induction oa using OracleComp.inductionOn generalizing n sk with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure']
    exact (FailsAtMost.pure (by simp)).mono_bound zero_le
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind']
    rcases t with t | request
    · have hrun : ((failSignerOf (HashSpec.withDerivationsLift PrfInput HashOutput) prfD
          (.inl t)).run sk).run =
            (fun u => ((u, sk), ([] : QueryLog SigningSpec))) <$>
              HashSpec.withDerivationsLift PrfInput HashOutput t := by
        simp [failSignerOf]
      have hnr : ¬IsAdversaryRequest (.inl t) := id
      simp only [hnr, ite_false] at h
      rw [hrun, bind_map_left]
      refine (FailsAtMost.bind (failA := fun _ => False) (ε₁ := 0)
        (FailsAtMost.of_allQueriesSatisfy (allQueriesSatisfy_of_isQueryBoundP ?_))
        fun u _ => FailsAtMost.map _ ((ih u (h.2 u) sk hsk).mono_fail ?_)).mono_bound (by simp)
      · rcases t with n | x <;> simp [IsRndQuery, OracleSpec.withDerivationsLift]
      · simp
    · have hrun : ((failSignerOf (HashSpec.withDerivationsLift PrfInput HashOutput) prfD
          (.inr request)).run sk).run =
            (fun r => ((r.1, r.2), [⟨request, r.1.toOption⟩])) <$>
              Internal.signWithTrials hashD prfD sk request.leafIndex request.message
                (hashTrials hashD) := by
        simp [failSignerOf, hashD]
      have hr : IsAdversaryRequest (.inr request) := trivial
      simp only [hr, ite_true, not_true, false_or] at h
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero h.1.ne'
      rw [hrun, bind_map_left]
      refine (FailsAtMost.bind (failA := fun r => r.1.toOption = none ∨ ¬KeptOk r.2)
        (ε₁ := (Q : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000)))
        ((failsAtMost_signWithTrials Q sk hsk _ _).mono_bound (le_of_eq ?_)) fun u hu =>
          FailsAtMost.map _
            ((ih u.1 (h.2 u.1) u.2 (not_not.1 (not_or.1 hu).2)).mono_fail ?_)).mono_bound ?_
      · rw [mul_add, ← two_pow_mul_div_two_pow 1 95, pow_one]
      · rintro ⟨a, w⟩ ⟨entry, hmem, hnone⟩
        simp only [Prod.map, List.mem_append, List.mem_singleton] at hmem
        rcases hmem with rfl | hmem
        · exact absurd hnone (not_or.1 hu).1
        · exact ⟨entry, hmem, hnone⟩
      · rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-! ## The size of the cache

The bound charges each new search the whole cache, at most `Q` entries, as hits on its trials.

`Q` grows with the requests, so the term is quadratic in `r`: at least `r^2 / 2^62`.
-/

/-- A step of the ideal game adds at most one cache entry, and only on a hash query. -/
theorem encard_le_of_mem_support_idealImpl {t : PrfSpec.Domain} {st : IdealState}
    {w : PrfSpec.Range t × IdealState}
    (hw : w ∈ support ((SecretEncoding.idealImpl HashSpec PrfInput HashOutput t).run st)) :
    w.2.1.toSet.encard ≤ st.1.toSet.encard + if IsHashD t then 1 else 0 := by
  rcases t with (n | t) | x
  · simp only [SecretEncoding.idealImpl, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact le_self_add
  · cases h : st.1 t with
    | some v =>
      rw [SecretEncoding.idealImpl_run_pub_some h] at hw
      simp only [support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact le_self_add
    | none =>
      rw [SecretEncoding.idealImpl_run_pub_none h] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨u, -, rfl⟩ := hw
      simpa [IsHashD] using QueryCache.toSet_encard_cacheQuery_le st.1 t u
  · cases h : st.2 x with
    | some v =>
      rw [SecretEncoding.idealImpl_run_derive_some h] at hw
      simp only [support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact le_self_add
    | none =>
      rw [SecretEncoding.idealImpl_run_derive_none h] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨u, -, rfl⟩ := hw
      exact le_self_add

/-- **A run of the game from empty caches ends with at most one cached input per hash call.**

The adversary makes at most `qH` hash queries and `r` signing requests. -/
theorem enncard_le_of_mem_support_prfGame (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r)
    {z : FailOutput × IdealState}
    (hz : z ∈ support ((simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
      (prfGame adversary)).run (∅, ∅))) :
    z.2.1.enncard ≤ gameQueries qH r := by
  -- Compare the sets: the kernel reduces a membership in `support` by running the computation.
  have h := (isQueryBoundP_prfGame adversary hh hr).resource_le_add_of_mem_support_run_simulateQ
    (fun s : IdealState => s.1.toSet.encard)
    (fun _ _ _ hw => encard_le_of_mem_support_idealImpl hw)
    (Set.mem_of_subset_of_mem (by exact subset_rfl) hz)
  simpa [QueryCache.enncard] using h

/-! ## The whole game -/

section Game

-- Unfolding the tree height would build the whole tree when a bound is checked.
attribute [local irreducible] Constants.LAYER_HEIGHT

/-- **The game fails as the adversary's requests do.**

The adversary makes at most `r` signing requests.

Count only the runs whose cache ends with at most `Q` entries. -/
theorem failsAtMost_prfGame (Q : ℕ) (adversary : ReasonAdversary) {r : ℕ}
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    FailsAtMost SomeFailure Q
      (r * ((Q : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000))))
      (prfGame adversary) := by
  unfold prfGame failGameOf Internal.keyGenFrom
  rw [pure_bind]
  simp only [bind_assoc]
  refine FailsAtMost.bind_of_noBase isQueryBoundP_publicParamOf fun publicParam => ?_
  refine FailsAtMost.bind_of_noBase (isQueryBoundP_build publicParam .top _ _) fun top => ?_
  simp only [pure_bind]
  -- The key of key generation keeps no tree.
  refine (FailsAtMost.bind (failsAtMost_run_failSignerOf Q _ (hr _) _
    fun _ h => absurd h List.not_mem_nil) fun z hz => ?_).mono_bound (add_zero _).le
  rcases z with ⟨⟨forgery, sk'⟩, log⟩
  dsimp only
  rw [show verifyWith (hashOf (HashSpec.withDerivationsLift PrfInput HashOutput))
      { root := top.value, publicParam := publicParam } forgery.message forgery.signature = _ from
    verifyWith_hashD _ _ _]
  refine (FailsAtMost.bind (failA := fun _ => False) (ε₁ := 0) (ε₂ := 0)
    (FailsAtMost.of_withDerivationsLift
      (verifyWith queryH { root := top.value, publicParam := publicParam } forgery.message
        forgery.signature : OracleComp XmssSecurity.OracleWorld Bool))
    fun v _ => ?_).mono_bound (add_zero _).le
  exact FailsAtMost.pure (fail := SomeFailure) (a := (forgery, log, v)) hz

end Game

/-- **The failure of some request, in the ideal game of the derivations.**

The adversary makes at most `qH` hash queries and `r` signing requests.

The bound is `r (Q / 2^95 + 2 exp(-4000))`, quadratic in `r` through the budget `Q`.

It exceeds 1 from about `2^31` requests, half of a key's `2^32` leaf indices, or for `qH >= 2^95`.

This loss comes from the proof, not from leanXMSS.

Other keys' trials have other addresses, and messages have a fixed length.

So only the adversary's queries can hold a trial input of a new search.

A count of only those queries would give a bound linear in `r`.

So would a count of how many trials are cached, rather than of whether one is. -/
theorem prEvent_prfGame_ideal_le (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl HashSpec PrfInput HashOutput)
        (prfGame adversary)).run (∅, ∅)}[SomeFailure z.1] ≤
      r * ((gameQueries qH r : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000))) :=
  (prEvent_mono_of_support _ _ _ fun z hz hE =>
    ⟨Or.inl hE, enncard_le_of_mem_support_prfGame adversary hh hr hz⟩).trans
    (failsAtMost_prfGame (gameQueries qH r) adversary hr (∅, ∅) fun _ _ _ _ _ h => by simp at h)

/-- **The failure of some signing request.**

The adversary makes at most `qH` hash queries and `r` signing requests.

Let `Q` be the bound on the hash calls of the game, for `qH` and `r`.

Some request fails with probability at most `2 Q / 2^256 + r (Q / 2^95 + 2 exp(-4000))`. -/
theorem signingFailure_le (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    signingFailure adversary ≤
      2 * (gameQueries qH r : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
        r * ((gameQueries qH r : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000))) :=
  (signingFailure_le_prfGame adversary hh hr).trans <| by
    rw [add_comm]
    exact add_le_add_right (prEvent_prfGame_ideal_le adversary hh hr) _

/-- **leanXMSS with a signer that reveals its reasons, with its failure term bounded.**

Take an adversary whose reduction to the theorem's game has a budget of `q >= 1` hash calls.

The adversary itself makes at most `qH` hash queries and `r` signing requests.

Let `Q` be the bound on the game's hash calls, for the same adversary.

The bound says nothing from about `2^31` requests, since its last term is quadratic in `r`.

It forges with probability at most `q / 2^127 + 2 Q / 2^256 + r (Q / 2^95 + 2 exp(-4000))`. -/
theorem reasonForgeAdvantage_le_bounded (q : ℕ) (hq : 1 ≤ q) (adversary : ReasonAdversary)
    (hbound : HasHashQueryBound (hideReasons adversary) q) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    reasonForgeAdvantage adversary ≤
      q / ((2 ^ 127 : ℕ) : ℝ≥0∞) + (2 * (gameQueries qH r : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
        r * ((gameQueries qH r : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000)))) :=
  (reasonForgeAdvantage_le_add q hq adversary hbound).trans
    (add_le_add_right (signingFailure_le adversary hh hr) _)

end EthLib.Cryptography.Xmss.Unforgeability
