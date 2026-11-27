module

public import EthLib.Cryptography.Proofs.SufCma.Simulate
public import EthLib.Cryptography.Proofs.RandomOracleWithCoins
public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.EvalDistEq
public import ToCslib.Data.Fin.MOfFn
public import ToMathlib.Control.Monad.Fold

/-!
# Proofs: strong unforgeability with many keys, by a hybrid over the keys

The game has `N` keys, and the adversary forges under one key of its choice.

It has no oracle that reveals a secret key.

For each key `j`, a single-key adversary makes the other keys and plays the game of `j`.

Summed over the keys, the many-key advantage is at most the `N` single-key advantages.

Moving key `j` first, which the sum needs, holds in the random-oracle model.
-/

@[expose] public section

namespace EthLib.Cryptography.SufCma

open OracleComp OracleSpec ENNReal

variable {ι : Type} {hs : OracleSpec ι}
  {Request Message PublicKey SecretKey Signature : Type} {N : ℕ}

/-! ## The game with many keys -/

/-- An adaptive adversary against `N` keys.

From the public keys, it samples coins, queries the hash and requests signatures under any key.

It returns a key's index and a forgery under that key. -/
structure MultiAdversary (hs : OracleSpec ι) (N : ℕ) (Request Message PublicKey Signature : Type)
    where
  main : (Fin N → PublicKey) →
    OracleComp ((unifSpec + hs) + SigningSpec (Fin N × Request) Signature)
      (Fin N × Forgery Message Signature)

variable (scheme : Scheme hs Request Message PublicKey SecretKey Signature)

/-- The signer of `N` keys answers a request with the key the request names.

That key alone moves on, and the request is logged with its answer. -/
def multiSigningOracle : QueryImpl (SigningSpec (Fin N × Request) Signature)
    (StateT (Fin N → SecretKey) (WriterT (QueryLog (SigningSpec (Fin N × Request) Signature))
      (OracleComp (unifSpec + hs)))) :=
  fun request => StateT.mk fun sks => WriterT.mk
    ((fun result => ((result.1, Function.update sks request.1 result.2), [⟨request, result.1⟩])) <$>
      scheme.sign (sks request.1) request.2)

/-- The requests to key `j`, with their answers, in order. -/
def keyLog (j : Fin N) (log : QueryLog (SigningSpec (Fin N × Request) Signature)) :
    QueryLog (SigningSpec Request Signature) :=
  log.filterMap fun entry => if entry.1.1 = j then some ⟨entry.1.2, entry.2⟩ else none

section Game

variable [DecidableEq Message] [DecidableEq Signature]

/-- The game once the keys exist: the adversary with its oracles, then the check of its forgery.

The forgery is checked as in the single-key game, against the key it names and its requests.

The game returns that key's index and whether the forgery wins. -/
def multiGameAfterKeys (adversary : MultiAdversary hs N Request Message PublicKey Signature)
    (keys : Fin N → PublicKey × SecretKey) : OracleComp (unifSpec + hs) (Fin N × Bool) :=
  ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
      (StateT (Fin N → SecretKey) (WriterT (QueryLog (SigningSpec (Fin N × Request) Signature))
        (OracleComp (unifSpec + hs)))) + multiSigningOracle (N := N) scheme)
      (adversary.main fun k => (keys k).1)).run fun k => (keys k).2).run >>= fun x =>
    (x.1.1.1, ·) <$> checkForgery scheme (keys x.1.1.1).1 (x.1.1.2, keyLog x.1.1.1 x.2)

/-- The game with `N` keys: key generation `N` times in index order, then the adversary. -/
def multiGame (adversary : MultiAdversary hs N Request Message PublicKey Signature) :
    OracleComp (unifSpec + hs) (Fin N × Bool) :=
  Fin.mOfFn N (fun _ => scheme.keyGen) >>= multiGameAfterKeys scheme adversary

/-- The probability that the adversary forges under one of the `N` keys against a model.

The bounds below hold for the random oracle model. -/
noncomputable def multiAdvantage (model : Model hs)
    (adversary : MultiAdversary hs N Request Message PublicKey Signature) : ℝ≥0∞ :=
  Pr{let x ← runIn model (multiGame scheme adversary)}[x.2 = true]

end Game

/-! ## The reduction to one key -/

/-- Key generation for every index but `j`, in index order; the slot of `j` stays empty. -/
def otherKeys (j : Fin N) : OracleComp (unifSpec + hs) (Fin N → Option (PublicKey × SecretKey)) :=
  Fin.mOfFn N fun k => if k = j then pure none else some <$> scheme.keyGen

/-- The reduction's oracles for the adversary of `N` keys.

Its state holds the secret keys it made, and nothing for the key of the single-key game. -/
def reductionImpl : QueryImpl ((unifSpec + hs) + SigningSpec (Fin N × Request) Signature)
    (StateT (Fin N → Option SecretKey)
      (OracleComp ((unifSpec + hs) + SigningSpec Request Signature)))
  -- A coin or a hash query passes through.
  | .inl t => liftM (((unifSpec + hs) + SigningSpec Request Signature).query (.inl t))
  | .inr request => StateT.mk fun sks =>
    match sks request.1 with
    -- A request to the empty slot goes to the single-key signer.
    | none => (·, sks) <$>
        liftM (((unifSpec + hs) + SigningSpec Request Signature).query (.inr request.2))
    -- A request to another key is signed by the reduction, which keeps the new key.
    | some sk => (fun result => (result.1, Function.update sks request.1 (some result.2))) <$>
        (scheme.sign sk request.2).liftComp ((unifSpec + hs) + SigningSpec Request Signature)

/-- The single-key adversary that plays the adversary of `N` keys with its key at index `j`.

It makes the other keys, then answers the adversary, and returns its forgery. -/
def reduction (adversary : MultiAdversary hs N Request Message PublicKey Signature)
    (j : Fin N) : Adversary hs Request Message PublicKey Signature where
  main pk := (otherKeys scheme j).liftComp ((unifSpec + hs) + SigningSpec Request Signature) >>=
    fun others => (fun y => y.2) <$> (simulateQ (reductionImpl scheme)
      (adversary.main fun k => ((others k).map Prod.fst).getD pk)).run'
        fun k => (others k).map Prod.snd

/-! ## The order of key generation -/

section Order

variable [DecidableEq ι] [∀ t, SampleableType (hs.Range t)]

/-- Two computations against the random oracle agree in law after a common first step. -/
theorem run_bind_evalDistEq {α β : Type} (X : OracleComp (unifSpec + hs) α)
    {F G : α → OracleComp (unifSpec + hs) β}
    (h : ∀ a c, (simulateQ hs.romImpl (F a)).run c =ᵈ (simulateQ hs.romImpl (G a)).run c)
    (c : hs.QueryCache) :
    (simulateQ hs.romImpl (X >>= F)).run c =ᵈ (simulateQ hs.romImpl (X >>= G)).run c := by
  simp only [simulateQ_bind, StateT.run_bind]
  exact EvalDistEq.bind_right _ fun w => h w.1 w.2

/-- **Any one of `n` independent key generations can run first.**

Against the random oracle, `n` runs of `K` in index order have the law of a run of `K` first.

Its output takes slot `j`, and the other slots are filled in index order after it. -/
theorem run_mOfFn_bind_evalDistEq {γ δ : Type} (K : OracleComp (unifSpec + hs) γ) :
    ∀ {n : ℕ} (j : Fin n) (W : (Fin n → γ) → OracleComp (unifSpec + hs) δ)
      (c : hs.QueryCache),
      (simulateQ hs.romImpl (Fin.mOfFn n (fun _ => K) >>= W)).run c =ᵈ
        (simulateQ hs.romImpl (K >>= fun x =>
          Fin.mOfFn n (fun k => if k = j then pure none else some <$> K) >>= fun g =>
            W fun k => (g k).getD x)).run c
  | 0, j, _, _ => j.elim0
  | n + 1, j, W, c => by
    induction j using Fin.cases with
    | zero =>
      -- The slot of the first key is the first one made.
      refine EvalDistEq.of_eq (congrArg (fun p => (simulateQ hs.romImpl p).run c) ?_)
      simp only [Fin.mOfFn_succ, ↓reduceIte, Fin.succ_ne_zero, bind_assoc, pure_bind,
        ← Fin.mOfFn_map, bind_map_left]
      refine bind_congr fun x => bind_congr fun g => congrArg W ?_
      funext k
      refine Fin.cases rfl (fun i => rfl) k
    | succ j =>
      -- The first key is made, then the key of slot `j + 1` moves in front of the others.
      simp only [Fin.mOfFn_succ, bind_assoc, pure_bind]
      refine (run_bind_evalDistEq K (fun a c' => run_mOfFn_bind_evalDistEq K j _ c') c).trans ?_
      refine (run_bind_bind_comm K K _ c).trans (EvalDistEq.of_eq ?_)
      simp only [(Fin.succ_ne_zero j).symm, ↓reduceIte, Fin.succ_inj, bind_map_left]
      refine congrArg (fun p => (simulateQ hs.romImpl p).run c)
        (bind_congr fun x => bind_congr fun a => bind_congr fun g => congrArg W ?_)
      funext k
      exact Fin.cases rfl (fun i => rfl) k

end Order

/-! ## The keys the reduction makes -/

/-- Each output of a family run in order is an output of its own computation. -/
theorem mem_support_mOfFn {ι' : Type} {spec : OracleSpec ι'} {α : Type} :
    ∀ {n : ℕ} {f : Fin n → OracleComp spec α} {g : Fin n → α},
      g ∈ support (Fin.mOfFn n f) → ∀ k, g k ∈ support (f k)
  | 0, _, _, _, k => k.elim0
  | n + 1, f, g, hg, k => by
    rw [Fin.mOfFn_succ] at hg
    obtain ⟨a, ha, hg⟩ := (mem_support_bind_iff _ _ _).1 hg
    obtain ⟨rest, hrest, hg⟩ := (mem_support_bind_iff _ _ _).1 hg
    rw [mem_support_pure_iff] at hg
    subst hg
    induction k using Fin.cases with
    | zero => simpa using ha
    | succ k => simpa using mem_support_mOfFn hrest k

/-- The keys the reduction makes leave exactly the slot of `j` empty. -/
theorem eq_none_iff_of_mem_support_otherKeys {j : Fin N}
    {others : Fin N → Option (PublicKey × SecretKey)}
    (h : others ∈ support (otherKeys scheme j)) (k : Fin N) : others k = none ↔ k = j := by
  have hk := mem_support_mOfFn h k
  by_cases hkj : k = j
  · subst hkj
    simp only [↓reduceIte, mem_support_pure_iff] at hk
    simp [hk]
  · simp only [hkj, ↓reduceIte] at hk
    rw [support_map] at hk
    obtain ⟨x, _, hx⟩ := hk
    simp [← hx, hkj]

/-! ## The reduction signs as the signer of `N` keys -/

/-- The reduction's state: the slot of `j` is empty, and every other slot holds its key. -/
def blankSlot (j : Fin N) (m : Fin N → SecretKey) : Fin N → Option SecretKey :=
  fun k => if k = j then none else some (m k)

/-- Moving the key of `j` leaves the reduction's state as it was. -/
theorem blankSlot_update_self (j : Fin N) (m : Fin N → SecretKey) (s : SecretKey) :
    blankSlot j (Function.update m j s) = blankSlot j m :=
  funext fun k => by by_cases h : k = j <;> simp [blankSlot, h]

/-- Moving another key moves it in the reduction's state. -/
theorem blankSlot_update_of_ne {i j : Fin N} (h : i ≠ j) (m : Fin N → SecretKey)
    (s : SecretKey) :
    blankSlot j (Function.update m i s) = Function.update (blankSlot j m) i (some s) :=
  funext fun k => by
    by_cases hk : k = i
    · subst hk
      simp [blankSlot, h]
    · simp [blankSlot, hk]

/-- A request to `j` stays in the log of `j`, without its index. -/
@[simp] theorem keyLog_cons_self (j : Fin N) (request : Request) (answer : Option Signature)
    (log : QueryLog (SigningSpec (Fin N × Request) Signature)) :
    keyLog j (⟨(j, request), answer⟩ :: log) = ⟨request, answer⟩ :: keyLog j log := by
  simp [keyLog]

/-- A request to another key leaves the log of `j`. -/
@[simp] theorem keyLog_cons_of_ne {i j : Fin N} (h : i ≠ j) (request : Request)
    (answer : Option Signature) (log : QueryLog (SigningSpec (Fin N × Request) Signature)) :
    keyLog j (⟨(i, request), answer⟩ :: log) = keyLog j log := by
  simp [keyLog, h]

/-- **The reduction, under the single-key signer, answers as the signer of `N` keys.**

The single-key signer holds the key of `j`, and the reduction every other key.

Both runs have the same output, and the requests to `j` are the single-key signer's log. -/
theorem run_simulateQ_reductionImpl (j : Fin N) {α : Type} :
    ∀ (oa : OracleComp ((unifSpec + hs) + SigningSpec (Fin N × Request) Signature) α)
      (m : Fin N → SecretKey),
      (fun z => (z.1.1.1, z.2)) <$> ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
          (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
            (OracleComp (unifSpec + hs)))) + signingOracle scheme)
          ((simulateQ (reductionImpl scheme) oa).run (blankSlot j m))).run (m j)).run =
        (fun z => (z.1.1, keyLog j z.2)) <$> ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
          (StateT (Fin N → SecretKey)
            (WriterT (QueryLog (SigningSpec (Fin N × Request) Signature))
              (OracleComp (unifSpec + hs)))) + multiSigningOracle (N := N) scheme)
            oa).run m).run := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro m; simp [keyLog]
  | query_bind t k ih =>
    intro m
    rcases t with t | ⟨i, request⟩
    · -- A coin or a hash query passes through both signers, and no key moves.
      simp [simulateQ_bind, reductionImpl, StateT.run_bind, WriterT.run_bind, Functor.map_map]
      erw [WriterT.run_monadLift']
      simp only [bind_map_left, List.empty_eq, List.nil_append]
      exact bind_congr fun u => ih u m
    · simp [simulateQ_bind, reductionImpl, StateT.run_bind, WriterT.run_bind, Functor.map_map]
      by_cases hij : i = j
      · -- A request to `j` goes to the single-key signer, which holds the key of `j`.
        subst hij
        rw [show blankSlot i m i = none by simp [blankSlot]]
        simp [signingOracle, multiSigningOracle, Functor.map_map]
        refine bind_congr fun r => ?_
        have h := congrArg (fun z => (fun p => (p.1, ⟨request, r.1⟩ :: p.2)) <$> z)
          (ih r.1 (Function.update m i r.2))
        simpa [blankSlot_update_self, Functor.map_map] using h
      · -- A request to another key is signed by the reduction with that key.
        rw [show blankSlot j m i = some (m i) by simp [blankSlot, hij]]
        simp [multiSigningOracle, run_simulateQ_adversaryOracles_liftM, Functor.map_map]
        refine bind_congr fun r => ?_
        have h := ih r.1 (Function.update m i r.2)
        simpa [blankSlot_update_of_ne hij, Function.update_of_ne (Ne.symm hij), hij,
          Functor.map_map] using h

/-! ## The game of the reduction -/

/-- Coin and hash queries first, run with the signer, keep the key and log nothing of their own. -/
theorem run_simulateQ_signing_liftComp_bind {β γ : Type} (oa : OracleComp (unifSpec + hs) β)
    (f : β → OracleComp ((unifSpec + hs) + SigningSpec Request Signature) γ) (sk : SecretKey) :
    ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
      (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
        (OracleComp (unifSpec + hs)))) + signingOracle scheme)
      (oa.liftComp ((unifSpec + hs) + SigningSpec Request Signature) >>= f)).run sk).run =
      oa >>= fun b => ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
        (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
          (OracleComp (unifSpec + hs)))) + signingOracle scheme) (f b)).run sk).run := by
  simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind,
    run_simulateQ_adversaryOracles_liftM, bind_map_left]
  exact bind_congr fun b => by simp

variable [DecidableEq Message] [DecidableEq Signature]

/-- The reduction's game, once key `j` exists: the other keys, then the adversary of `N` keys.

The reduction's signing goes through the signer of `N` keys, which holds key `j` in its slot. -/
theorem gameAfterKeys_reduction
    (adversary : MultiAdversary hs N Request Message PublicKey Signature) (j : Fin N)
    (pk : PublicKey) (sk : SecretKey) :
    gameAfterKeys scheme (reduction scheme adversary j) pk sk =
      otherKeys scheme j >>= fun others =>
        ((fun z => ((z.1.1.1.2, z.1.2), z.2)) <$> ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
          (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
            (OracleComp (unifSpec + hs)))) + signingOracle scheme)
          ((simulateQ (reductionImpl scheme)
            (adversary.main fun k => ((others k).map Prod.fst).getD pk)).run
              fun k => (others k).map Prod.snd)).run sk).run) >>= fun x =>
          checkForgery scheme pk (x.1.1, x.2) := by
  unfold gameAfterKeys reduction
  simp only [run_simulateQ_signing_liftComp_bind, bind_assoc]
  refine bind_congr fun others => ?_
  simp [StateT.run'_eq, simulateQ_map, Functor.map_map, bind_map_left]

/-- **The reduction's game, once key `j` exists, is the game of `N` keys with `j` in its slot.**

The other keys are those the reduction makes, and the forgery is checked against key `j`. -/
theorem gameAfterKeys_reduction_eq
    (adversary : MultiAdversary hs N Request Message PublicKey Signature) (j : Fin N)
    (pk : PublicKey) (sk : SecretKey) :
    gameAfterKeys scheme (reduction scheme adversary j) pk sk =
      otherKeys scheme j >>= fun others =>
        ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
            (StateT (Fin N → SecretKey)
              (WriterT (QueryLog (SigningSpec (Fin N × Request) Signature))
                (OracleComp (unifSpec + hs)))) + multiSigningOracle (N := N) scheme)
            (adversary.main fun k => ((others k).getD (pk, sk)).1)).run
              fun k => ((others k).getD (pk, sk)).2).run >>= fun y =>
          checkForgery scheme pk (y.1.1.2, keyLog j y.2) := by
  rw [gameAfterKeys_reduction]
  refine bind_congr_of_forall_mem_support _ fun others hothers => ?_
  have hnone := eq_none_iff_of_mem_support_otherKeys scheme hothers
  -- The keys of the game, with key `j` in its slot.
  set filled : Fin N → PublicKey × SecretKey := fun k => (others k).getD (pk, sk)
  have hpk : (fun k => ((others k).map Prod.fst).getD pk) = fun k => (filled k).1 :=
    funext fun k => by cases h : others k <;> simp [filled, h]
  have hstate : (fun k => (others k).map Prod.snd) = blankSlot j fun k => (filled k).2 :=
    funext fun k => by
      by_cases hk : k = j
      · subst hk
        simp [blankSlot, (hnone k).2 rfl]
      · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (mt (hnone k).1 hk)
        simp [blankSlot, hk, filled, hx]
  have hj : filled j = (pk, sk) := by simp [filled, (hnone j).2 rfl]
  -- The reduction signs as the signer of `N` keys.
  have hsim := run_simulateQ_reductionImpl scheme j (adversary.main fun k => (filled k).1)
    fun k => (filled k).2
  rw [hj] at hsim
  rw [hpk, hstate]
  have hB := congrArg (fun z => z >>= fun w => checkForgery scheme pk (w.1.2, w.2)) hsim
  simp only [bind_map_left] at hB ⊢
  exact hB

/-! ## The hybrid over the keys -/

section Hybrid

variable [DecidableEq ι] [∀ t, SampleableType (hs.Range t)]

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Two runs that share a first step compare as their rests compare after each of its outputs. -/
theorem prEvent_run'_bind_mono {α β γ : Type} (oa : OracleComp (unifSpec + hs) α)
    {f : α → OracleComp (unifSpec + hs) β} {g : α → OracleComp (unifSpec + hs) γ}
    {E : β → Prop} {F : γ → Prop} (c : hs.QueryCache)
    (h : ∀ a ∈ support oa, ∀ c', Pr{let y ← (simulateQ hs.romImpl (f a)).run' c'}[E y] ≤
      Pr{let y ← (simulateQ hs.romImpl (g a)).run' c'}[F y]) :
    Pr{let y ← (simulateQ hs.romImpl (oa >>= f)).run' c}[E y] ≤
      Pr{let y ← (simulateQ hs.romImpl (oa >>= g)).run' c}[F y] := by
  rw [run'_simulateQ_romImpl_bind, run'_simulateQ_romImpl_bind, map_bind, map_bind]
  exact prEvent_bind_mono_of_support _ _ _ fun z hz =>
    h z.1 (fst_mem_support_of_mem_support_run_romImpl hz) z.2

/-- **Forgeries under key `j` win at most as often as the reduction of `j`.** -/
theorem prEvent_multiGame_le_advantage
    (adversary : MultiAdversary hs N Request Message PublicKey Signature) (j : Fin N) :
    Pr{let x ← runIn (randomOracleModel hs) (multiGame scheme adversary)}[x.1 = j ∧ x.2 = true] ≤
      advantage scheme (randomOracleModel hs) (reduction scheme adversary j) := by
  rw [runIn_randomOracleModel, advantage, runIn_randomOracleModel]
  -- Key `j` is made first, and the other keys after it, in index order.
  rw [multiGame, StateT.run'_eq, ((run_mOfFn_bind_evalDistEq scheme.keyGen j
    (multiGameAfterKeys scheme adversary) ∅).map Prod.fst).prEvent_eq, ← StateT.run'_eq]
  unfold game
  refine prEvent_run'_bind_mono _ _ fun keys _ c => ?_
  rw [gameAfterKeys_reduction_eq]
  refine prEvent_run'_bind_mono _ _ fun others hothers c' => ?_
  have hj : (others j).getD (keys.1, keys.2) = keys := by
    simp [(eq_none_iff_of_mem_support_otherKeys scheme hothers j).2 rfl]
  unfold multiGameAfterKeys
  simp only [Prod.mk.eta]
  refine prEvent_run'_bind_mono _ _ fun y _ c'' => ?_
  by_cases hy : y.1.1.1 = j
  · -- A forgery under key `j` is checked as the reduction's.
    simp only [hy, hj]
    simp [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  · -- A forgery under another key is not counted.
    simp [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, hy]

/-- **The many-key advantage is at most the sum of the advantages of the `N` reductions.** -/
theorem multiAdvantage_le_sum
    (adversary : MultiAdversary hs N Request Message PublicKey Signature) :
    multiAdvantage scheme (randomOracleModel hs) adversary ≤
      ∑ j, advantage scheme (randomOracleModel hs) (reduction scheme adversary j) := by
  unfold multiAdvantage
  calc Pr{let x ← runIn (randomOracleModel hs) (multiGame scheme adversary)}[x.2 = true]
      = Pr{let x ← runIn (randomOracleModel hs) (multiGame scheme adversary)}[
          ∃ j, x.1 = j ∧ x.2 = true] :=
        -- A forgery wins under the key it names.
        prEvent_congr _ _ _ fun x => ⟨fun h => ⟨x.1, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
    _ ≤ ∑ j, Pr{let x ← runIn (randomOracleModel hs) (multiGame scheme adversary)}[
          x.1 = j ∧ x.2 = true] := prEvent_exists_le _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => prEvent_multiGame_le_advantage scheme adversary j

/-- **A bound `ε` on every reduction gives `N * ε` with `N` keys.** -/
theorem multiAdvantage_le_card_mul
    (adversary : MultiAdversary hs N Request Message PublicKey Signature) {ε : ℝ≥0∞}
    (h : ∀ j, advantage scheme (randomOracleModel hs) (reduction scheme adversary j) ≤ ε) :
    multiAdvantage scheme (randomOracleModel hs) adversary ≤ N * ε :=
  (multiAdvantage_le_sum scheme adversary).trans
    (by simpa using Finset.sum_le_card_nsmul Finset.univ _ ε fun j _ => h j)

end Hybrid

/-! ## The calls of the reduction's game

A bound on the charge holds on every run: the costs `c` of the run's queries sum to at most it.
-/

section Charge

open PFunctor.FreeM (IsChargeBound isChargeBound_pure isChargeBound_map_iff' isChargeBound_lift_iff)

omit [DecidableEq Message] [DecidableEq Signature] in
/-- A family run in index order is charged the sum of its members' bounds. -/
theorem isChargeBound_mOfFn {α : Type} (c : (unifSpec + hs).Domain → ℕ) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (unifSpec + hs) α) (b : Fin n → ℕ),
      (∀ k, IsChargeBound (f k) c (b k)) → IsChargeBound (Fin.mOfFn n f) c (∑ k, b k)
  | 0, _, _, _ => by
    rw [Fin.mOfFn_zero]
    exact isChargeBound_pure _
  | n + 1, f, b, h => by
    rw [Fin.mOfFn_succ, Fin.sum_univ_succ]
    have h' := (h 0).bind fun a =>
      (isChargeBound_mOfFn c (fun i => f i.succ) (fun i => b i.succ) fun i => h i.succ).bind
        fun rest => isChargeBound_pure (B := 0) (Fin.cons a rest : Fin (n + 1) → α)
    rwa [add_zero] at h'

omit [DecidableEq Message] [DecidableEq Signature] in
/-- The reduction makes `N - 1` keys. -/
theorem isChargeBound_otherKeys (c : (unifSpec + hs).Domain → ℕ) {K : ℕ}
    (hK : IsChargeBound scheme.keyGen c K) (j : Fin N) :
    IsChargeBound (otherKeys scheme j) c ((N - 1) * K) := by
  have h := isChargeBound_mOfFn c
    (fun k => if k = j then pure none else some <$> scheme.keyGen)
    (fun k => if k = j then 0 else K) fun k => by
    by_cases hk : k = j
    · simp only [hk, ↓reduceIte]
      exact isChargeBound_pure _
    · simp only [hk, ↓reduceIte]
      exact (isChargeBound_map_iff' _ _).2 hK
  refine h.mono (le_of_eq ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]

omit [DecidableEq Message] [DecidableEq Signature] in
/-- The adversary's phase with `N` keys is charged its own queries, and `S` per request. -/
theorem isChargeBound_multiPhase (c : (unifSpec + hs).Domain → ℕ) {S q n : ℕ}
    (hS : ∀ sk request, IsChargeBound (scheme.sign sk request) c S) {α : Type}
    (oa : OracleComp ((unifSpec + hs) + SigningSpec (Fin N × Request) Signature) α)
    (hq : IsChargeBound oa (adversaryCharge (Request := Fin N × Request) (Signature := Signature) c)
      q)
    (hn : IsQueryBoundP oa (IsAdversaryRequest hs (Fin N × Request) Signature) n)
    (sks : Fin N → SecretKey) :
    IsChargeBound ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
      (StateT (Fin N → SecretKey) (WriterT (QueryLog (SigningSpec (Fin N × Request) Signature))
        (OracleComp (unifSpec + hs)))) + multiSigningOracle (N := N) scheme) oa).run sks).run c
      (q + n * S) := by
  have h := hq.add_mul ((isQueryBoundP_iff_isChargeBound _ _ _).1 hn) S
  rw [zero_mul, add_zero] at h
  refine isChargeBound_run_simulateQ _ (fun t sks => ?_) h sks
  rcases t with t | request
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply, StateT.run_monadLift,
      adversaryCharge, SignatureAlg.IsSignQuery, ↓reduceIte, zero_mul, add_zero]
    exact (isChargeBound_lift_iff (P := (unifSpec + hs).toPFunctor) t).2 (by rw [zero_add])
  · simp only [QueryImpl.add_apply_inr, multiSigningOracle, StateT.run_mk, WriterT.run_mk,
      isChargeBound_map_iff', adversaryCharge, SignatureAlg.IsSignQuery, ↓reduceIte, one_mul,
      zero_add]
    exact hS _ _

/-- **The charge of the reduction's game is at most `N * K + (q + n * S) + V` on every run.**

Key generation costs `K`, for the game's key and the `N - 1` keys the reduction makes.

The adversary's own queries cost `q`, each of its at most `n` requests `S`, and verification `V`.

Whether the reduction or the signer signs a request, it costs the signer's bound `S`. -/
theorem isChargeBound_game_reduction (c : (unifSpec + hs).Domain → ℕ) {K S V q n : ℕ}
    (adversary : MultiAdversary hs N Request Message PublicKey Signature) (j : Fin N)
    (hK : IsChargeBound scheme.keyGen c K)
    (hS : ∀ sk request, IsChargeBound (scheme.sign sk request) c S)
    (hV : ∀ pk message signature, IsChargeBound (scheme.verify pk message signature) c V)
    (hq : ∀ pks, IsChargeBound (adversary.main pks)
      (adversaryCharge (Request := Fin N × Request) (Signature := Signature) c) q)
    (hn : ∀ pks, IsQueryBoundP (adversary.main pks)
      (IsAdversaryRequest hs (Fin N × Request) Signature) n) :
    IsChargeBound (game scheme (reduction scheme adversary j)) c (N * K + (q + n * S) + V) := by
  -- Key `j` exists, so there is at least one key.
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := j.pos; omega⟩
  rw [show (M + 1) * K + (q + n * S) + V = K + ((M + 1 - 1) * K + ((q + n * S) + (V + 0))) by
    simp only [add_tsub_cancel_right, add_zero]
    ring]
  refine hK.bind fun keys => ?_
  rw [gameAfterKeys_reduction_eq]
  refine (isChargeBound_otherKeys scheme c hK j).bind fun others => ?_
  refine (isChargeBound_multiPhase scheme c hS _ (hq _) (hn _) _).bind fun y => ?_
  exact (hV _ _ _).bind fun _ => isChargeBound_pure _

end Charge

end EthLib.Cryptography.SufCma
