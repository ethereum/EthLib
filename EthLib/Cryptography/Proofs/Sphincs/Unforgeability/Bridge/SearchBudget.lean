module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Search

/-!
# Proofs: the wrapped adversary's hash calls

The wrapped adversary forwards the adversary's queries until an answer has a long search.

Up to there its run is a run of the adversary.

So it makes at most the adversary's own hash calls and requests.

Every request before the last one was answered with short searches.

So each of them cost at most `470595 + 3 T` calls.

The last request cost at most `470595 + 3 * 2^32` calls, and after it the wrapper sends nothing.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld)
open SphincsSecurity.Security.Prefix (hashCalls)

/-! ## One step of the adversary's run in the game -/

variable (f : QueryImpl HashSpec Id) (sign : Message → OracleComp HashSpec (Option Signature))

/-- The adversary's run in the game, with its hash calls counted and its requests logged. -/
local notation "runOf " sign:max A:max => WriterT.run (simulateQ (QueryImpl.ofLift OracleWorld
    (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
      QueryImpl.withLogging (fun msg => liftM (sign msg) :
        QueryImpl SigningSpec (OracleComp OracleWorld)))
    (SphincsSecurity.QueryCap.counted IsAdversaryHashCall A))

/-- A computation lifted to the logging monad logs nothing. -/
theorem run_liftM_writerT {β : Type} (c : OracleComp OracleWorld β) :
    (liftM c : WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) β).run =
      (fun u => (u, ∅)) <$> c := by
  change (monadLift c : WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) β).run = _
  rw [WriterT.run_monadLift']

/-- A run that returns at once makes no call and no request. -/
theorem mem_support_runOf_pure {α : Type} (a : α) (y : ((α × Nat) × QueryLog SigningSpec) × Nat) :
    y ∈ support (countedRun f (runOf sign (pure a : OracleComp (OracleWorld + SigningSpec) α))) ↔
      y = (((a, 0), []), 0) := by
  rw [SphincsSecurity.QueryCap.counted_pure, simulateQ_pure, WriterT.run_pure',
    countedRun_pure, support_pure, Set.mem_singleton_iff]
  rfl

/-- A coin or a hash call of the adversary is answered as under `f`, then the run goes on. -/
theorem mem_support_runOf_inl {α : Type} (w : OracleWorld.Domain)
    (k : OracleWorld.Range w → OracleComp (OracleWorld + SigningSpec) α)
    (y : ((α × Nat) × QueryLog SigningSpec) × Nat) :
    y ∈ support (countedRun f (runOf sign
        ((OracleWorld + SigningSpec).query (.inl w) >>= k))) ↔
      ∃ u ∈ support (unifFwdAnswerImpl f w), ∃ z ∈ support (countedRun f (runOf sign (k u))),
        y = (((z.1.1.1, (if isHashCall w then 1 else 0) + z.1.1.2), z.1.2),
          (if isHashCall w then 1 else 0) + z.2) := by
  rw [SphincsSecurity.QueryCap.counted_query_bind]
  simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind,
    QueryImpl.add_apply_inl, QueryImpl.ofLift_apply, simulateQ_pure, WriterT.run_pure',
    map_pure]
  have hl : (liftM (OracleWorld.query w) :
      WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run =
        (fun u => (u, ∅)) <$> liftM (OracleWorld.query w) := rfl
  rw [hl, bind_map_left, mem_support_countedRun_bind]
  simp only [bind_pure_comp, countedRun_map, support_map, countedRun_query]
  have hc : IsAdversaryHashCall (.inl w) ↔ isHashCall w := Iff.rfl
  simp only [hc, Set.mem_image, List.empty_eq, List.nil_append, List.append_nil]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    exact ⟨u, hu, z, hz, rfl⟩
  · rintro ⟨u, hu, z, hz, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, _, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩

/-- A request is answered by the signer under `f`, logged, and charged its calls. -/
theorem mem_support_runOf_inr {α : Type} (msg : Message)
    (k : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (y : ((α × Nat) × QueryLog SigningSpec) × Nat) :
    y ∈ support (countedRun f (runOf sign
        ((OracleWorld + SigningSpec).query (.inr msg) >>= k))) ↔
      ∃ z ∈ support (countedRun f (runOf sign (k (evalWithAnswerFn f (sign msg))))),
        y = (((z.1.1.1, z.1.1.2), ⟨msg, evalWithAnswerFn f (sign msg)⟩ :: z.1.2),
          hashCalls f (sign msg) + z.2) := by
  rw [SphincsSecurity.QueryCap.counted_query_bind]
  simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.add_apply_inr,
    QueryImpl.withLogging_apply, WriterT.run_tell, bind_assoc,
    map_eq_bind_pure_comp, Function.comp_def, pure_bind, simulateQ_pure,
    WriterT.run_pure']
  rw [run_liftM_writerT, bind_map_left, mem_support_countedRun_liftM_bind]
  have hc : ¬IsAdversaryHashCall (.inr msg) := id
  simp only [hc, ↓reduceIte, Nat.zero_add, List.empty_eq, List.nil_append, List.append_nil,
    List.singleton_append, bind_pure_comp, countedRun_map, support_map, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩


/-! ## One step of the wrapped adversary -/

/-- The wrapper forwards a coin, and a hash call before the flag. -/
theorem capRun_inl {α : Type} (T : Nat) (w : OracleWorld.Domain) (b : Bool)
    (hw : w.isLeft ∨ b = false)
    (k : OracleWorld.Range w → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (capImpl T) ((OracleWorld + SigningSpec).query (.inl w) >>= k)).run b =
      (liftM ((OracleWorld + SigningSpec).query (.inl w)) :
        OracleComp (OracleWorld + SigningSpec) _) >>= fun u =>
        (simulateQ (capImpl T) (k u)).run b := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rcases w with n | x
  · rfl
  · obtain h | rfl := hw
    · exact absurd h (by simp)
    · rfl

/-- After the flag, the wrapper answers a hash call with 0 itself. -/
theorem capRun_hash_true {α : Type} (T : Nat) (x : HashSig.HashInput)
    (k : HashSig.HashOutput → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (capImpl T) ((OracleWorld + SigningSpec).query (.inl (.inr x)) >>= k)).run true =
      (simulateQ (capImpl T) (k 0)).run true := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

/-- Before the flag, the wrapper forwards a request and raises the flag on a long answer. -/
theorem capRun_inr_false {α : Type} (T : Nat) (msg : Message)
    (k : Option Signature → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (capImpl T) ((OracleWorld + SigningSpec).query (.inr msg) >>= k)).run false =
      (liftM ((OracleWorld + SigningSpec).query (.inr msg)) :
        OracleComp (OracleWorld + SigningSpec) _) >>= fun a =>
        (simulateQ (capImpl T) (k a)).run (!decide (SearchesBelow T a)) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

/-- After the flag, the wrapper answers a request with nothing itself. -/
theorem capRun_inr_true {α : Type} (T : Nat) (msg : Message)
    (k : Option Signature → OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (capImpl T) ((OracleWorld + SigningSpec).query (.inr msg) >>= k)).run true =
      (simulateQ (capImpl T) (k none)).run true := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

/-! ## The wrapped adversary's run against the adversary's run -/

/-- After the flag, the wrapped adversary makes no hash call and no request. -/
theorem runOf_capRun_true {α : Type} (T : Nat) (A : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ y ∈ support (countedRun f (runOf sign ((simulateQ (capImpl T) A).run true))),
      y.1.1.2 = 0 ∧ y.1.2 = [] ∧ y.2 = 0 := by
  induction A using OracleComp.inductionOn with
  | pure a =>
    intro y hy
    rw [simulateQ_pure, StateT.run_pure, mem_support_runOf_pure] at hy
    subst hy
    exact ⟨rfl, rfl, rfl⟩
  | query_bind t k ih =>
    intro y hy
    rcases t with (n | x) | msg
    · rw [capRun_inl T (.inl n) true (Or.inl rfl), mem_support_runOf_inl] at hy
      obtain ⟨u, -, z, hz, rfl⟩ := hy
      obtain ⟨h₁, h₂, h₃⟩ := ih u z hz
      have hc : ¬isHashCall (.inl n) := by simp [isHashCall]
      simp only [hc, ↓reduceIte, Nat.zero_add]
      exact ⟨h₁, h₂, h₃⟩
    · rw [capRun_hash_true] at hy
      exact ih _ y hy
    · rw [capRun_inr_true] at hy
      exact ih _ y hy

/-- Before the flag, a run of the adversary makes at least the wrapper's own calls and requests. -/
theorem runOf_capRun_false {α : Type} (T C L : Nat)
    (hbelow : ∀ msg, SearchesBelow T (evalWithAnswerFn f (sign msg)) →
      hashCalls f (sign msg) ≤ C)
    (hall : ∀ msg, hashCalls f (sign msg) ≤ C + L)
    (A : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ y ∈ support (countedRun f (runOf sign ((simulateQ (capImpl T) A).run false))),
      ∃ x ∈ support (countedRun f (runOf sign A)), y.1.1.2 ≤ x.1.1.2 ∧
        y.1.2.length ≤ x.1.2.length ∧ y.2 ≤ y.1.1.2 + y.1.2.length * C + L := by
  induction A using OracleComp.inductionOn with
  | pure a =>
    intro y hy
    rw [simulateQ_pure, StateT.run_pure, mem_support_runOf_pure] at hy
    subst hy
    exact ⟨_, (mem_support_runOf_pure f sign a _).2 rfl, le_rfl, le_rfl, Nat.zero_le _⟩
  | query_bind t k ih =>
    intro y hy
    rcases t with w | msg
    · rw [capRun_inl T w false (Or.inr rfl), mem_support_runOf_inl] at hy
      obtain ⟨u, hu, z, hz, rfl⟩ := hy
      obtain ⟨x, hx, h₁, h₂, h₃⟩ := ih u z hz
      refine ⟨_, (mem_support_runOf_inl f sign w k _).2 ⟨u, hu, x, hx, rfl⟩, ?_, h₂, ?_⟩
      · dsimp only
        omega
      · dsimp only at h₃ ⊢
        omega
    · rw [capRun_inr_false, mem_support_runOf_inr] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      by_cases hs : SearchesBelow T (evalWithAnswerFn f (sign msg))
      · simp only [hs, decide_true, Bool.not_true] at hz
        obtain ⟨x, hx, h₁, h₂, h₃⟩ := ih _ z hz
        refine ⟨_, (mem_support_runOf_inr f sign msg k _).2 ⟨x, hx, rfl⟩, h₁, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · have hc := hbelow msg hs
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
      · simp only [hs, decide_false, Bool.not_false] at hz
        obtain ⟨h₁, h₂, h₃⟩ := runOf_capRun_true f sign T _ z hz
        obtain ⟨x, hx⟩ := OracleComp.support_nonempty
          (countedRun f (runOf sign (k (evalWithAnswerFn f (sign msg)))))
        refine ⟨_, (mem_support_runOf_inr f sign msg k _).2 ⟨x, hx, rfl⟩, ?_, ?_, ?_⟩
        · dsimp only
          omega
        · simp only [h₂, List.length_cons, List.length_nil]
          omega
        · have hc := hall msg
          simp only [h₂, List.length_cons, List.length_nil]
          omega

/-! ## The game of the wrapped adversary -/

/-- A game of this shape with the wrapped adversary is bounded by a run with the adversary. -/
theorem calls_capGame {Seed' SK PK : Type} (seeds : ProbComp Seed')
    (keygen : Seed' → OracleComp HashSpec (SK × PK))
    (signer : SK → Message → OracleComp HashSpec (Option Signature))
    (verify : PK → Forgery → OracleComp HashSpec Bool)
    (win : Forgery → QueryLog SigningSpec → Bool → Bool)
    (main : PK → OracleComp (OracleWorld + SigningSpec) Forgery) (T K C L V : Nat)
    (hK : ∀ seed, hashCalls f (keygen seed) ≤ K)
    (hbelow : ∀ sk msg, SearchesBelow T (evalWithAnswerFn f (signer sk msg)) →
      hashCalls f (signer sk msg) ≤ C)
    (hall : ∀ sk msg, hashCalls f (signer sk msg) ≤ C + L)
    (hV : ∀ pk forgery, hashCalls f (verify pk forgery) ≤ V) :
    ∀ r ∈ support (countedRun f (do
      let seed ← liftM seeds
      let keys ← liftM (keygen seed)
      let run ← runOf (signer keys.1) ((simulateQ (capImpl T) (main keys.2)).run' false)
      let verified ← liftM (verify keys.2 run.1.1)
      pure (win run.1.1 run.2 verified, run.1.2, run.2.length))),
    ∃ r' ∈ support (countedRun f (do
      let seed ← liftM seeds
      let keys ← liftM (keygen seed)
      let run ← runOf (signer keys.1) (main keys.2)
      let verified ← liftM (verify keys.2 run.1.1)
      pure (win run.1.1 run.2 verified, run.1.2, run.2.length))),
      r.2 ≤ r'.1.2.1 + K + r'.1.2.2 * C + L + V := by
  intro r hr
  rw [mem_support_countedRun_bind, countedRun_liftM_coins, support_map] at hr
  obtain ⟨x, ⟨seed, hseed, rfl⟩, y, hy, rfl⟩ := hr
  rw [mem_support_countedRun_liftM_bind] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [mem_support_countedRun_bind] at hz
  obtain ⟨w, hw, v, hv, rfl⟩ := hz
  rw [mem_support_countedRun_liftM_bind, countedRun_pure, support_pure] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [Set.mem_singleton_iff] at hu
  subst hu
  rw [StateT.run'_eq, SphincsSecurity.QueryCap.counted_map, simulateQ_map, WriterT.run_map,
    countedRun_map, support_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  dsimp only
  generalize hkp : evalWithAnswerFn f (keygen seed) = kp at hw'
  obtain ⟨x, hx, h₁, h₂, h₃⟩ := runOf_capRun_false f (signer kp.1) T C L (hbelow kp.1)
    (hall kp.1) (main kp.2) w' hw'
  refine ⟨((win x.1.1.1 x.1.2 (evalWithAnswerFn f (verify kp.2 x.1.1.1)), x.1.1.2,
    x.1.2.length), 0 + (hashCalls f (keygen seed) + (x.2 + (hashCalls f (verify kp.2 x.1.1.1) +
      0)))), ?_, ?_⟩
  · rw [mem_support_countedRun_bind]
    refine ⟨(seed, 0), ?_, (_, hashCalls f (keygen seed) + (x.2 +
      (hashCalls f (verify kp.2 x.1.1.1) + 0))), ?_, rfl⟩
    · rw [countedRun_liftM_coins, support_map]
      exact ⟨seed, hseed, rfl⟩
    rw [mem_support_countedRun_liftM_bind]
    refine ⟨(_, x.2 + (hashCalls f (verify kp.2 x.1.1.1) + 0)), ?_, rfl⟩
    rw [hkp, mem_support_countedRun_bind]
    refine ⟨x, hx, (_, hashCalls f (verify kp.2 x.1.1.1) + 0), ?_, rfl⟩
    rw [mem_support_countedRun_liftM_bind]
    refine ⟨(_, 0), ?_, rfl⟩
    rw [countedRun_pure]
    exact Set.mem_singleton _
  · have hmul := Nat.mul_le_mul_right C h₂
    refine (Nat.add_le_add_left (Nat.add_le_add (hK seed) (Nat.add_le_add h₃
      (Nat.add_le_add_right (hV _ _) 0))) 0).trans ?_
    dsimp only
    omega

/-- A request answered with short searches makes at most `470595 + 3 T` calls. -/
theorem hashCalls_signerOf_le_of_searchesBelow (T : Nat) (sk : SecretKey) (msg : Message)
    (answer : Option Signature) (hanswer : evalWithAnswerFn f (signerOf sk msg) = answer)
    (hs : SearchesBelow T answer) :
    hashCalls f (signerOf sk msg) ≤ 470595 + 3 * T := by
  cases answer with
  | none => exact hs.elim
  | some sig => exact hashCalls_signerOf_le_of_below f T sk msg sig hanswer hs

/-- Any request makes at most `3 * 2^32` calls more than one with short searches. -/
theorem hashCalls_signerOf_le_add (T : Nat) (sk : SecretKey) (msg : Message) :
    hashCalls f (signerOf sk msg) ≤ 470595 + 3 * T + 3 * MAX_COUNTER_TRIALS :=
  (hashCalls_signerOf_le f sk msg).trans (by unfold signCalls; omega)

omit f in
/-- The wrapped adversary runs the adversary under the wrapper, from the state `false`. -/
theorem capSearches_main (T : Nat) (adversary : Adversary) (pk : PublicKey) :
    (capSearches T adversary).main pk = (simulateQ (capImpl T) (adversary.main pk)).run' false :=
  rfl

omit f in
/-- The game with the adversary's counter, its run counted and logged as one step. -/
theorem adversaryGameCore_eq_runOf (adversary : Adversary) :
    adversaryGameCore adversary = (do
      let seed ← liftM sampleSeed
      let keys ← liftM (keyGenWith H seed)
      let run ← runOf (signerOf keys.1) (adversary.main keys.2)
      let verified ← liftM (verifierOf keys.2 run.1.1)
      pure (verdictOf run.1.1 run.2 verified, run.1.2, run.2.length)) :=
  adversaryGameCore_eq adversary

omit f in
/-- The game of the wrapped adversary, its run counted and logged as one step. -/
theorem adversaryGameCore_capSearches_eq (T : Nat) (adversary : Adversary) :
    adversaryGameCore (capSearches T adversary) = (do
      let seed ← liftM sampleSeed
      let keys ← liftM (keyGenWith H seed)
      let run ← runOf (signerOf keys.1)
        ((simulateQ (capImpl T) (adversary.main keys.2)).run' false)
      let verified ← liftM (verifierOf keys.2 run.1.1)
      pure (verdictOf run.1.1 run.2 verified, run.1.2, run.2.length)) := by
  rw [adversaryGameCore_eq_runOf]
  simp only [capSearches_main]

/-- **The wrapped adversary's runs make at most `q + cappedCalls T r` hash calls in all.**

The adversary makes at most `q` hash calls of its own and `r` signing requests. -/
theorem hasHashQueryBound_capSearches (T : Nat) (adversary : Adversary) (q r : Nat)
    (h : HasAdversaryQueryBound adversary q r) :
    HasHashQueryBound (capSearches T adversary) (q + cappedCalls T r) := by
  intro result hr
  obtain ⟨f, hr⟩ := exists_countedRun_of_mem_support _ _ (experiment_eq _) result hr
  rw [gameCore_eq_map] at hr
  obtain ⟨run, hrun, rfl⟩ := mem_support_countedRun_map f _ _ result hr
  rw [adversaryGameCore_capSearches_eq] at hrun
  obtain ⟨run', hrun', hle⟩ := calls_capGame f sampleSeed (keyGenWith H) signerOf verifierOf
    verdictOf adversary.main T keyGenCalls (470595 + 3 * T) (3 * MAX_COUNTER_TRIALS) verifyCalls
    (fun seed => (Cost.hashCalls_keyGenWith_eq f H (hashCalls_queryH f) seed).le)
    (fun sk msg => hashCalls_signerOf_le_of_searchesBelow f T sk msg _ rfl)
    (hashCalls_signerOf_le_add f T)
    (fun _ _ => Cost.hashCalls_verifyWith_le f H isTotalQueryBound_H _ _ _) run hrun
  rw [← adversaryGameCore_eq_runOf] at hrun'
  -- The adversary's run is a run of its experiment, within its budget.
  obtain ⟨hq, hr⟩ := h run'.1 (mem_support_adversaryExperiment f adversary run' hrun')
  have hmul := Nat.mul_le_mul_right (470595 + 3 * T) hr
  unfold cappedCalls
  dsimp only
  omega

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
