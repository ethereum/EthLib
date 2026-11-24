module

public import EthLib.Cryptography.Proofs.Bls.Security.Reduction

/-!
# Proofs: BLS forgeries against several honest keys

Against `n` honest keys, a forger within `q` hash calls wins at most `n * q` times a co-CDH solver.

The keys are honest from the start, and the game has no corruption oracle.

Source: the one-key game of [Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf), §3.

Here signing and the forgery also name a key.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open OracleComp OracleSpec ENNReal

variable {F G₁ G₂ M : Type} {n : ℕ}

/-- The oracles against `n` keys: uniform coins, the hash `H`, and signing by a chosen key. -/
abbrev MultiSpec (n : ℕ) (M G₂ : Type) := unifSpec + ((M →ₒ G₂) + ((Fin n × M) →ₒ G₂))

/-- An adversary against `n` keys: it returns a key, a message and a claimed signature. -/
structure MultiAdversary (n : ℕ) (G₁ G₂ M : Type) where
  /-- The adversary's run, with access to the oracles. -/
  main : (Fin n → G₁) → OracleComp (MultiSpec n M G₂) (Fin n × M × G₂)

/-- The state of the game against `n` keys. -/
structure MultiState (n : ℕ) (F M : Type) where
  /-- Each hashed message once, in the order of its first hash call, with its scalar. -/
  table : List (M × F)
  /-- The signing requests in order, each with the key that signed and the message. -/
  signed : List (Fin n × M)
  /-- The number of hash calls so far, repeated messages included. -/
  calls : ℕ

/-- The empty state, at the start of the game. -/
def MultiState.init : MultiState n F M := ⟨[], [], 0⟩

/-- The state of the game against key `i` alone: the same hashes, and the requests to `i`. -/
def MultiState.toState (i : Fin n) (st : MultiState n F M) : State F M :=
  ⟨st.table, (st.signed.filter (·.1 = i)).map Prod.snd, st.calls⟩

variable [DecidableEq M] [CommRing F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- The random oracle `H` of the game against one key, on the hashes and calls of this state. -/
def multiHash (g₂ : G₂) (m : M) : StateT (MultiState n F M) ProbComp G₂ := fun st =>
  (fun z => (z.1, { st with table := z.2.table, calls := z.2.calls })) <$>
    hash g₂ m ⟨st.table, [], st.calls⟩

/-- The signing oracle under the secret keys `a`: key `j` returns `a j • H(m)`. -/
def multiSign (g₂ : G₂) (a : Fin n → F) (request : Fin n × M) :
    StateT (MultiState n F M) ProbComp G₂ := fun st =>
  -- The request `(j, m)` is recorded with its key.
  (fun z => (a request.1 • z.1, { z.2 with signed := z.2.signed ++ [request] })) <$>
    multiHash g₂ request.2 st

/-- The oracles of the game under the secret keys `a`. -/
def multiImpl (g₂ : G₂) (a : Fin n → F) :
    QueryImpl (MultiSpec n M G₂) (StateT (MultiState n F M) ProbComp)
  -- Coins pass through, and the state is unchanged by them.
  | .inl k => fun st => (·, st) <$> (query (spec := unifSpec) k : ProbComp (Fin (k + 1)))
  | .inr (.inl m) => (multiHash g₂ m : StateT (MultiState n F M) ProbComp G₂)
  | .inr (.inr request) => (multiSign g₂ a request : StateT (MultiState n F M) ProbComp G₂)

/-- The adversary's run on the public keys, then the hash call that verification makes. -/
def multiRun (adversary : MultiAdversary n G₁ G₂ M) (pks : Fin n → G₁) :
    OracleComp (MultiSpec n M G₂) (Fin n × M × G₂ × G₂) := do
  let (j, m, σ) ← adversary.main pks
  -- It returns the key, the message, the claimed signature and the hash of the message.
  let h ← query (spec := MultiSpec n M G₂) (.inr (.inl m))
  return (j, m, σ, h)

/-- The game: sample the secret keys, run the adversary with its oracles, and check the forgery. -/
def multiExperiment (scheme : Scheme G₁ G₂) (adversary : MultiAdversary n G₁ G₂ M) :
    ProbComp (Bool × MultiState n F M) := do
  let a ← $ᵗ (Fin n → F)
  let pks := fun j => a j • scheme.g₁
  let ((j, m, σ, h), st) ← (simulateQ (multiImpl scheme.g₂ a) (multiRun adversary pks)).run
    MultiState.init
  -- The forgery verifies under key `j`, which never signed its message, whatever other keys did.
  return (decide ((j, m) ∉ st.signed) && scheme.isDh (pks j) h σ,
    -- The final state comes back too, since its count of hash calls bounds the adversary.
    st)

variable (F)

/-- The probability that the adversary forges for one of the `n` keys. -/
noncomputable def multiForgeAdvantage (scheme : Scheme G₁ G₂)
    (adversary : MultiAdversary n G₁ G₂ M) : ℝ≥0∞ :=
  Pr{let z ← multiExperiment (F := F) scheme adversary}[z.1 = true]

/-- Every run of the game against `n` keys makes at most `q` hash calls.

That counts the adversary's calls, those of signing, and the one of the final verification. -/
def MultiHashCallBound (scheme : Scheme G₁ G₂) (adversary : MultiAdversary n G₁ G₂ M)
    (q : ℕ) : Prop :=
  ∀ z ∈ support (multiExperiment (F := F) scheme adversary), z.2.calls ≤ q

/-! ## The guess of the key -/

variable {F}

/-- Answer the oracles of the game against `n` keys with those of key `i` alone. -/
def guessImpl (i : Fin n) (b : Fin n → F) :
    QueryImpl (MultiSpec n M G₂) (OracleComp (Spec M G₂))
  | .inl k => query (spec := Spec M G₂) (.inl k)
  | .inr (.inl m) => query (spec := Spec M G₂) (.inr (.inl m))
  | .inr (.inr (j, m)) =>
    -- Key `i` asks the signing oracle; another key `j` signs as `b j • H(m)`, from one hash call.
    if j = i then query (spec := Spec M G₂) (.inr (.inr m))
    else (b j • · : G₂ → G₂) <$> query (spec := Spec M G₂) (.inr (.inl m))

variable (F) [NeZero n]

/-- The forger against one key: it guesses the key of the forgery and draws the other keys. -/
def MultiAdversary.guess (g₁ : G₁) (adversary : MultiAdversary n G₁ G₂ M) :
    Adversary G₁ G₂ M where
  main pk := do
    -- The guess `i` is uniform and independent of the adversary's view, so it matches with `1 / n`.
    let i ← (liftM ($ᵗ (Fin n)) : OracleComp (Spec M G₂) (Fin n))
    let b ← (liftM ($ᵗ (Fin n → F)) : OracleComp (Spec M G₂) (Fin n → F))
    let (_, m, σ) ← simulateQ (guessImpl i b)
      -- The challenge key takes place `i`, and `b j • g1` each other place, so `b` signs for them.
      (adversary.main (Function.update (fun j => b j • g₁) i pk))
    -- The message and signature go back whatever key the adversary names.
    return (m, σ)

variable {F}

/-- A hash call reads and writes the table and the count, and leaves the signed messages alone. -/
private theorem hash_mk (g₂ : G₂) (m : M) (T : List (M × F)) (S : List M) (c : ℕ) :
    hash g₂ m (⟨T, S, c⟩ : State F M) =
      (fun z => (z.1, { z.2 with signed := S })) <$> hash g₂ m (⟨T, [], c⟩ : State F M) := by
  cases h : lookup m T with
  | some x =>
    rw [hash_of_lookup_some (st := ⟨T, S, c⟩) h, hash_of_lookup_some (st := ⟨T, [], c⟩) h]
    rfl
  | none =>
    rw [hash_of_lookup_none (st := ⟨T, S, c⟩) h, hash_of_lookup_none (st := ⟨T, [], c⟩) h,
      Functor.map_map]

omit [NeZero n] in
/-- Each oracle of the game against `n` keys, seen from key `i`, is the guess's oracle. -/
private theorem map_toState_multiImpl (g₂ : G₂) (a : F) (i : Fin n) (b : Fin n → F)
    (t : (MultiSpec n M G₂).Domain) (st : MultiState n F M) :
    Prod.map id (MultiState.toState i) <$> (multiImpl g₂ (Function.update b i a) t).run st =
      (simulateQ (impl g₂ a) (guessImpl i b t)).run (st.toState i) := by
  rcases t with k | m | ⟨j, m⟩
  · simp only [guessImpl, simulateQ_HasQuery_query]
    change Prod.map id (MultiState.toState i) <$>
        ((·, st) <$> (query (spec := unifSpec) k : ProbComp (Fin (k + 1)))) =
      (·, st.toState i) <$> (query (spec := unifSpec) k : ProbComp (Fin (k + 1)))
    rw [Functor.map_map]
    rfl
  · simp only [guessImpl, simulateQ_HasQuery_query]
    change Prod.map id (MultiState.toState i) <$>
        ((fun z => (z.1, { st with table := z.2.table, calls := z.2.calls })) <$>
          hash g₂ m (⟨st.table, [], st.calls⟩ : State F M)) =
      hash g₂ m ⟨st.table, (st.signed.filter (·.1 = i)).map Prod.snd, st.calls⟩
    conv_rhs => rw [hash_mk]
    rw [Functor.map_map]
    rfl
  · by_cases hj : j = i
    · subst hj
      simp only [guessImpl, ↓reduceIte, simulateQ_HasQuery_query]
      change Prod.map id (MultiState.toState j) <$>
          ((fun z => (Function.update b j a j • z.1,
              { z.2 with signed := z.2.signed ++ [(j, m)] })) <$>
            ((fun z => (z.1, { st with table := z.2.table, calls := z.2.calls })) <$>
              hash g₂ m (⟨st.table, [], st.calls⟩ : State F M))) =
        (fun z => (a • z.1, { z.2 with signed := z.2.signed ++ [m] })) <$>
          hash g₂ m ⟨st.table, (st.signed.filter (·.1 = j)).map Prod.snd, st.calls⟩
      conv_rhs => rw [hash_mk]
      simp only [Functor.map_map]
      refine congrArg (· <$> _) (funext fun z => ?_)
      simp [MultiState.toState]
    · simp only [guessImpl, hj, ↓reduceIte, simulateQ_map, simulateQ_HasQuery_query, StateT.run_map]
      change Prod.map id (MultiState.toState i) <$>
          ((fun z => (Function.update b i a j • z.1,
              { z.2 with signed := z.2.signed ++ [(j, m)] })) <$>
            ((fun z => (z.1, { st with table := z.2.table, calls := z.2.calls })) <$>
              hash g₂ m (⟨st.table, [], st.calls⟩ : State F M))) =
        (fun p => (b j • p.1, p.2)) <$>
          hash g₂ m ⟨st.table, (st.signed.filter (·.1 = i)).map Prod.snd, st.calls⟩
      conv_rhs => rw [hash_mk]
      simp only [Functor.map_map]
      refine congrArg (· <$> _) (funext fun z => ?_)
      simp [MultiState.toState, hj]

omit [NeZero n] in
/-- The game against `n` keys, seen from key `i`, is the game of the guess against key `i`. -/
private theorem map_toState_run (g₂ : G₂) (a : F) (i : Fin n) (b : Fin n → F) {α : Type}
    (oa : OracleComp (MultiSpec n M G₂) α) (st : MultiState n F M) :
    Prod.map id (MultiState.toState i) <$>
        (simulateQ (multiImpl g₂ (Function.update b i a)) oa).run st =
      (simulateQ (impl g₂ a) (simulateQ (guessImpl i b) oa)).run (st.toState i) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _
    (map_toState_multiImpl g₂ a i b) oa st

omit [NeZero n] in
/-- Coins lifted into the game pass through its oracles and leave the state alone. -/
private theorem run_simulateQ_impl_liftM (g₂ : G₂) (a : F) {α : Type} (p : ProbComp α)
    (st : State F M) :
    (simulateQ (impl g₂ a) (liftM p : OracleComp (Spec M G₂) α)).run st = (·, st) <$> p := by
  rw [← OracleComp.liftComp_eq_liftM]
  induction p using OracleComp.inductionOn generalizing st with
  | pure x => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query, simulateQ_bind, StateT.run_bind]
    change (simulateQ (impl g₂ a) (liftM ((Spec M G₂).query (.inl t)))).run st >>= _ = _
    rw [simulateQ_spec_query]
    change ((·, st) <$> (query (spec := unifSpec) t : ProbComp _)) >>= _ = _
    rw [bind_map_left, map_bind]
    exact bind_congr fun u => ih u st

omit [DecidableEq M] in
/-- The run of the guess: draw the guess and the other keys, then run the game against `n` keys. -/
private theorem run_guess (g₁ : G₁) (adversary : MultiAdversary n G₁ G₂ M) (pk : G₁) :
    run (adversary.guess F g₁) pk =
      (liftM ($ᵗ (Fin n)) : OracleComp (Spec M G₂) (Fin n)) >>= fun i =>
        (liftM ($ᵗ (Fin n → F)) : OracleComp (Spec M G₂) (Fin n → F)) >>= fun b =>
          (fun z => (z.2.1, z.2.2.1, z.2.2.2)) <$> simulateQ (guessImpl i b)
            (multiRun adversary (Function.update (fun j => b j • g₁) i pk)) := by
  simp [run, MultiAdversary.guess, multiRun, guessImpl, bind_assoc, map_bind, simulateQ_bind]

/-- The game of the guess under the secret `a` runs the game against `n` keys, seen from key `i`.

The guess `i` and the other keys `b` are drawn first, and key `i` gets `a`. -/
private theorem gameRun_guess (g₁ : G₁) (g₂ : G₂) (adversary : MultiAdversary n G₁ G₂ M)
    (a : F) :
    gameRun g₂ (adversary.guess F g₁) (a • g₁) a =
      $ᵗ (Fin n) >>= fun i => $ᵗ (Fin n → F) >>= fun b =>
        (fun z => ((z.1.2.1, z.1.2.2.1, z.1.2.2.2), z.2.toState i)) <$>
          (simulateQ (multiImpl g₂ (Function.update b i a))
            (multiRun adversary fun j => Function.update b i a j • g₁)).run MultiState.init := by
  have hpk : ∀ i (b : Fin n → F), Function.update (fun j => b j • g₁) i (a • g₁) =
      fun j => Function.update b i a j • g₁ := by
    intro i b
    funext j
    by_cases h : j = i <;> simp [h]
  rw [gameRun, run_guess, simulateQ_bind, StateT.run_bind, run_simulateQ_impl_liftM,
    bind_map_left]
  refine bind_congr fun i => ?_
  rw [simulateQ_bind, StateT.run_bind, run_simulateQ_impl_liftM, bind_map_left]
  refine bind_congr fun b => ?_
  rw [simulateQ_map, StateT.run_map, hpk,
    show (State.init : State F M) = MultiState.toState i MultiState.init from rfl,
    ← map_toState_run, Functor.map_map]
  rfl

omit [DecidableEq M] [CommRing F] [NeZero n] in
/-- Uniform keys with key `i` replaced by an independent uniform scalar are uniform keys. -/
private theorem prEvent_update_uniform (i : Fin n) (h : (Fin n → F) → ProbComp Prop) :
    prEvent ($ᵗ F >>= fun a => $ᵗ (Fin n → F) >>= fun b => h (Function.update b i a)) =
      prEvent ($ᵗ (Fin n → F) >>= h) := by
  -- The pair of the new keys and the old key `i` is a uniform pair.
  have hbij : Function.Bijective
      (Function.uncurry fun (a : F) (b : Fin n → F) => (Function.update b i a, b i)) := by
    refine ⟨fun ⟨a, b⟩ ⟨a', b'⟩ hab => ?_, fun ⟨k, c⟩ => ⟨(k i, Function.update k i c), ?_⟩⟩
    · simp only [Function.uncurry_apply_pair, Prod.mk.injEq] at hab
      obtain ⟨h1, h2⟩ := hab
      obtain rfl : a = a' := by simpa using congrFun h1 i
      refine congrArg _ (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj
        exact h2
      · simpa [hj] using congrFun h1 j
    · simp
  have e := evalDistEq_iff_evalDist_eq.mp
    ((SampleableType.evalDistEq_uniformSample_pair_of_bijective hbij).bind_left fun z => h z.1)
  rw [prEvent_def, prEvent_def]
  refine congrArg (fun μ : MeasureTheory.Measure Prop => μ {True}) ?_
  calc _ = 𝒟[(do
          let a ← $ᵗ F
          let b ← $ᵗ (Fin n → F)
          pure (Function.update b i a, b i)) >>= fun z => h z.1] := by
        simp only [bind_assoc, pure_bind]
    _ = _ := e.trans (SampleableType.evalDist_uniformSample_prod_bind_fst h)

omit [NeZero n] in
/-- The forger against `n` keys wins at most the sum, over each key, of its wins with that key. -/
private theorem multiForgeAdvantage_le_sum (scheme : Scheme G₁ G₂)
    (adversary : MultiAdversary n G₁ G₂ M) :
    multiForgeAdvantage F scheme adversary ≤ ∑ i, prEvent ($ᵗ (Fin n → F) >>= fun k =>
      (fun y => ((y.1.1, y.1.2.1) ∉ y.2.signed ∧
          scheme.isDh (k y.1.1 • scheme.g₁) y.1.2.2.2 y.1.2.2.1 = true) ∧ y.1.1 = i) <$>
        (simulateQ (multiImpl scheme.g₂ k)
          (multiRun adversary fun j => k j • scheme.g₁)).run MultiState.init) := by
  let : MeasurableSpace (Fin n → F) := ⊤
  unfold multiForgeAdvantage multiExperiment
  rw [prEvent_bind_eq_lintegral_of_discrete]
  simp only [prEvent_bind_of_discrete]
  rw [← MeasureTheory.lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
  refine MeasureTheory.lintegral_mono fun k => ?_
  rw [bind_pure_comp, prEvent_map]
  have h := prEvent_exists_finset_le (Finset.univ : Finset (Fin n))
    ((simulateQ (multiImpl scheme.g₂ k)
      (multiRun adversary fun j => k j • scheme.g₁)).run MultiState.init)
    fun i y => ((y.1.1, y.1.2.1) ∉ y.2.signed ∧
      scheme.isDh (k y.1.1 • scheme.g₁) y.1.2.2.2 y.1.2.2.1 = true) ∧ y.1.1 = i
  refine le_trans (prEvent_mono _ _ _ fun y hy => ⟨y.1.1, Finset.mem_univ _, ?_, rfl⟩) h
  simpa using hy

/-- Summed over the keys, the forger's wins with each key are at most `n` times the guess's. -/
private theorem sum_le_forgeAdvantage_guess (scheme : Scheme G₁ G₂)
    (adversary : MultiAdversary n G₁ G₂ M) :
    ∑ i, prEvent ($ᵗ (Fin n → F) >>= fun k =>
      (fun y => ((y.1.1, y.1.2.1) ∉ y.2.signed ∧
          scheme.isDh (k y.1.1 • scheme.g₁) y.1.2.2.2 y.1.2.2.1 = true) ∧ y.1.1 = i) <$>
        (simulateQ (multiImpl scheme.g₂ k)
          (multiRun adversary fun j => k j • scheme.g₁)).run MultiState.init) ≤
      n * forgeAdvantage F scheme (adversary.guess F scheme.g₁) := by
  let : MeasurableSpace F := ⊤
  let : MeasurableSpace (Fin n) := ⊤
  let : MeasurableSpace (Fin n → F) := ⊤
  rw [forgeAdvantage_eq]
  simp only [gameRun_guess, map_bind, Functor.map_map]
  rw [← prEvent_bind_of_discrete, prEvent_bind_bind_swap_of_uniform, prEvent_bind_of_discrete,
    MeasureTheory.lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin, mul_comm, mul_assoc,
    ENNReal.inv_mul_cancel (NeZero.ne _) (by simp), mul_one, ← prEvent_update_uniform i]
  simp only [prEvent_bind_of_discrete]
  refine MeasureTheory.lintegral_mono fun a => MeasureTheory.lintegral_mono fun b =>
    prEvent_mono _ _ _ fun y ⟨⟨hfresh, hdh⟩, hi⟩ => ⟨fun hm => hfresh ?_, ?_⟩
  · simp only [MultiState.toState, List.mem_map, List.mem_filter, decide_eq_true_eq] at hm
    obtain ⟨⟨j, m⟩, ⟨hmem, rfl⟩, rfl⟩ := hm
    rwa [hi]
  · rwa [hi, Function.update_self] at hdh

variable (F)

/-- The forger against one key makes the hash calls of the game against `n` keys. -/
theorem hashCallBound_guess (scheme : Scheme G₁ G₂) (adversary : MultiAdversary n G₁ G₂ M)
    {q : ℕ} (hq : MultiHashCallBound F scheme adversary q) :
    HashCallBound F scheme (adversary.guess F scheme.g₁) q := by
  intro z hz
  unfold experiment at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨a, -, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  change w ∈ support (gameRun scheme.g₂ (adversary.guess F scheme.g₁) (a • scheme.g₁) a) at hw
  rw [gameRun_guess] at hw
  simp only [mem_support_bind_iff, support_map, Set.mem_image] at hw
  obtain ⟨i, -, b, -, y, hy, rfl⟩ := hw
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  refine hq (decide ((y.1.1, y.1.2.1) ∉ y.2.signed) &&
    scheme.isDh (Function.update b i a y.1.1 • scheme.g₁) y.1.2.2.2 y.1.2.2.1, y.2) ?_
  unfold multiExperiment
  rw [mem_support_bind_iff]
  refine ⟨Function.update b i a, by simp, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨y, hy, by simp⟩

/-- A forger against `n` keys wins at most `n` times as often as its guess against one key. -/
theorem multiForgeAdvantage_le (scheme : Scheme G₁ G₂) (adversary : MultiAdversary n G₁ G₂ M) :
    multiForgeAdvantage F scheme adversary ≤
      n * forgeAdvantage F scheme (adversary.guess F scheme.g₁) :=
  (multiForgeAdvantage_le_sum scheme adversary).trans (sum_le_forgeAdvantage_guess scheme adversary)

/-- **BLS signatures are unforgeable against `n` keys from co-CDH**, in the random oracle model.

Within `q >= 1` hash calls, a forger wins at most `n * q` times as often as a named solver. -/
theorem multiForgeAdvantage_le_coCdhAdvantage [DecidableEq G₂] (scheme : Scheme G₁ G₂)
    (hsound : scheme.Sound F) (adversary : MultiAdversary n G₁ G₂ M) {q : ℕ} (hq0 : 0 < q)
    (hq : MultiHashCallBound F scheme adversary q) :
    multiForgeAdvantage F scheme adversary ≤
      n * (q * coCdhAdvantage F scheme.g₁ scheme.g₂
        (reduction (F := F) scheme.g₂ (adversary.guess F scheme.g₁) q)) :=
  (multiForgeAdvantage_le F scheme adversary).trans
    (mul_le_mul_right (forgeAdvantage_le scheme hsound _ hq0
      (hashCallBound_guess F scheme adversary hq)) _)

end EthLib.Cryptography.Bls.Security
