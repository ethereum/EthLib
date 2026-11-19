module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SeedHops

/-!
# Proofs: the bound for a budget of the adversary's own calls

The theorem's budget `q` counts every hash call of the game, the signer's included.

Here the budget is the adversary's own: at most `qH` calls of `H` and `r` signing requests.

Key generation, each request and the final verification make at most a fixed number of calls.

The bounds are `205 * 2^16 + 1`, `2^33 + 410 * 2^16 + 204` and `384`.

So the game makes at most `Q = 205 * 2^16 + 1 + qH + r (2^33 + 410 * 2^16 + 204) + 384` calls.

The theorem then bounds a forgery by `Q / 2^127`.

A key has `2^32` leaf indices.

With at most `2^32` requests, `Q <= qH + 2^65 + 410 * 2^48 + 204 * 2^32 + 205 * 2^16 + 385`.

A request's bound includes two searches of `2^32` trials each, and the theorem charges all of it.

So the bound is above `2^-62` for an adversary that requests every leaf.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants (LOG_LIFETIME LAYER_HEIGHT)
open XmssSecurity (OracleWorld HashSpec HashQueryBound simulateQ_countHashQueries
  countHashQueries_pure countHashQueries_query_bind)

/-- A query of the game's hash, as opposed to a coin. -/
def IsHashCall (t : OracleWorld.Domain) : Prop :=
  t.isRight = true

instance : DecidablePred IsHashCall := fun t =>
  inferInstanceAs (Decidable (t.isRight = true))

/-- On every public key and every run, the adversary makes at most `qH` calls of `H`.

It makes at most `r` signing requests too; the calls that answer them are not counted. -/
def HasAdversaryBudget (adversary : Adversary) (qH r : Nat) : Prop :=
  ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH ∧
    IsQueryBoundP (adversary.main pk) IsAdversaryRequest r

/-! ## The calls of the game -/

/-- Coins make no hash call. -/
theorem isQueryBoundP_liftM_prob {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp OracleWorld α) IsHashCall 0 :=
  isQueryBoundP_liftM_isRight oa

/-- A computation of at most `n` hash queries makes at most `n` hash calls among the game's. -/
theorem isQueryBoundP_liftM_hash {α : Type} {n : Nat} :
    ∀ (oa : OracleComp HashSpec α), IsQueryBoundP oa (fun _ => True) n →
      IsQueryBoundP (liftM oa : OracleComp OracleWorld α) IsHashCall n := by
  intro oa h
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [liftM_bind]
    refine (isQueryBoundP_bind (n := 1) ?_ fun u _ => ih u (h.2 u)).mono ?_
    · exact (isQueryBoundP_query_iff (spec := OracleWorld) _ (.inr t) 1).2 fun _ => Nat.one_pos
    · have := h.1.resolve_left (not_not_intro trivial)
      simp only [ite_true]
      omega

/-- `H` is one hash query. -/
theorem isQueryBoundP_H (x : ByteArray) : IsQueryBoundP (H x) (fun _ => True) 1 :=
  (isQueryBoundP_map_iff _ _ _).2
    ((isQueryBoundP_query_iff (spec := HashSpec) _ _ 1).2 fun _ => Nat.one_pos)

/-- A derivation is one hash query. -/
theorem isQueryBoundP_seedPrf (s : Seed) (pp : PublicParam) (a : Address) (suffix : ByteArray) :
    IsQueryBoundP (seedPrf H s pp a suffix) (fun _ => True) 1 :=
  isQueryBoundP_H _

/-- Key generation: the scheme seed, then the public key. -/
theorem isQueryBoundP_keyGenWith (seed : Seed) :
    IsQueryBoundP (keyGenWith H seed) (fun _ => True) keyGenQueries := by
  unfold keyGenWith
  refine (isQueryBoundP_bind (isQueryBoundP_H _) fun s _ =>
    isQueryBoundP_bind (m := 0) (isQueryBoundP_publicKeyOf isQueryBoundP_H
      (isQueryBoundP_seedPrf s)) fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  simp only [keyGenQueries]
  omega

/-- A signature: the scheme seed, the parameter, then the signature from the derivations. -/
theorem isQueryBoundP_signWith (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    IsQueryBoundP (signWith H sk idx msg) (fun _ => True) requestQueries := by
  unfold signWith
  refine (isQueryBoundP_bind (isQueryBoundP_H _) fun s _ =>
    isQueryBoundP_bind (isQueryBoundP_publicParamOf (isQueryBoundP_seedPrf s)) fun pp _ =>
      isQueryBoundP_signDerived isQueryBoundP_H (isQueryBoundP_seedPrf s) pp idx msg).mono ?_
  simp only [requestQueries]
  omega

/-- The adversary's run costs a call per hash query and a request's bound per request. -/
theorem isQueryBoundP_run_signingOracle (sk : SecretKey) {α : Type}
    (oa : OracleComp (OracleWorld + SigningSpec) α) {qH r : Nat}
    (hh : IsQueryBoundP oa IsAdversaryHash qH) (hr : IsQueryBoundP oa IsAdversaryRequest r) :
    IsQueryBoundP (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk) oa).run
      IsHashCall (qH + r * requestQueries) := by
  induction oa using OracleComp.inductionOn generalizing qH r with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hh hr
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind']
    rcases t with (n | x) | request
    · simp only [IsAdversaryHash, IsAdversaryRequest, ite_false] at hh hr
      refine (isQueryBoundP_bind (n := 0) ?_ fun u _ =>
        (isQueryBoundP_map_iff _ _ _).2 (ih u.1 (hh.2 u.1) (hr.2 u.1))).mono (by omega)
      exact (isQueryBoundP_query_iff (spec := OracleWorld) _ (.inl n) 0).2 fun h => by
        simp [IsHashCall] at h
    · simp only [IsAdversaryHash, IsAdversaryRequest, ite_true, ite_false] at hh hr
      have : 0 < qH := by simpa using hh.1
      refine (isQueryBoundP_bind (n := 1) ?_ fun u _ =>
        (isQueryBoundP_map_iff _ _ _).2 (ih u.1 (hh.2 u.1) (hr.2 u.1))).mono (by omega)
      exact (isQueryBoundP_query_iff (spec := OracleWorld) _ (.inr x) 1).2 fun _ => Nat.one_pos
    · simp only [IsAdversaryHash, IsAdversaryRequest, ite_true, ite_false] at hh hr
      have : 0 < r := by simpa using hr.1
      refine (isQueryBoundP_bind (n := requestQueries) ?_ fun u _ =>
        (isQueryBoundP_map_iff _ _ _).2 (ih u.1 (hh.2 u.1) (hr.2 u.1))).mono ?_
      · simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply]
        exact isQueryBoundP_bind (m := 0) (n := requestQueries)
          (isQueryBoundP_liftM_hash (Except.toOption <$> signWith H sk request.leafIndex
            request.message) ((isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_signWith sk _ _)))
          fun _ _ => isQueryBoundP_pure _ _ 0
      · have : (r - 1) * requestQueries + requestQueries = r * requestQueries := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this]
        omega

/-- The game makes at most `Q` hash calls, for the adversary's `qH` calls and `r` requests. -/
theorem isQueryBoundP_gameCore (adversary : Adversary) {qH r : Nat}
    (hbudget : HasAdversaryBudget adversary qH r) :
    IsQueryBoundP (gameCore adversary) IsHashCall (gameQueries qH r) := by
  unfold gameCore
  refine (isQueryBoundP_bind (isQueryBoundP_liftM_prob sampleSeed) fun seed _ =>
    isQueryBoundP_bind (isQueryBoundP_liftM_hash _ (isQueryBoundP_keyGenWith seed)) fun keys _ =>
      isQueryBoundP_bind (isQueryBoundP_run_signingOracle keys.1 (adversary.main keys.2)
        (hbudget keys.2).1 (hbudget keys.2).2) fun z _ =>
        isQueryBoundP_bind (m := 0) (isQueryBoundP_liftM_hash _
          (isQueryBoundP_verifyWith isQueryBoundP_H _ _ _)) fun _ _ =>
          isQueryBoundP_pure _ _ 0).mono ?_
  simp only [gameQueries, verifyQueries]
  omega

/-! ## From the calls of the game to its counted experiment -/

/-- A computation of at most `n` hash calls makes at most `n` counted calls, from any cache. -/
theorem hashQueryBound_of_isQueryBoundP {α : Type} {n : Nat} :
    ∀ (oa : OracleComp OracleWorld α), IsQueryBoundP oa IsHashCall n →
      ∀ cache, HashQueryBound oa cache n := by
  intro oa h
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a =>
    intro cache result hresult
    simp [countHashQueries_pure] at hresult
    simp [hresult]
  | query_bind t k ih =>
    intro cache result hresult
    rw [isQueryBoundP_query_bind_iff] at h
    rw [countHashQueries_query_bind] at hresult
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run'_eq,
      StateT.run_bind, support_map, support_bind, Set.mem_image, Set.mem_iUnion] at hresult
    obtain ⟨w, ⟨u, hu, v, hv, hw⟩, rfl⟩ := hresult
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    have hk := ih u.1 (h.2 u.1) u.2 (v.1) (by
      simp only [StateT.run'_eq, support_map]
      exact ⟨v, hv, rfl⟩)
    rcases t with n' | x
    · simp only [IsHashCall, Sum.isRight_inl, Bool.false_eq_true, ite_false] at h hk ⊢
      simpa using hk
    · simp only [IsHashCall, Sum.isRight_inr, ite_true] at h hk ⊢
      have := h.1.resolve_left (not_not_intro trivial)
      omega

/-- The game's counted experiment makes at most `Q` calls, for a budget of `qH` and `r`. -/
theorem hasHashQueryBound_of_budget (adversary : Adversary) {qH r : Nat}
    (hbudget : HasAdversaryBudget adversary qH r) :
    HasHashQueryBound adversary (gameQueries qH r) := by
  have h := hashQueryBound_of_isQueryBoundP _ (isQueryBoundP_gameCore adversary hbudget) ∅
  simp only [HashQueryBound, simulateQ_countHashQueries] at h
  exact h

/-! ## The bounds -/

/-- With at most `qH` calls of `H` and `r` requests, a forgery has chance `<= Q / 2^127`.

`Q = 205 * 2^16 + 1 + qH + r (2^33 + 410 * 2^16 + 204) + 384` counts the game's calls. -/
theorem forgeAdvantage_le_adversaryBudget (adversary : Adversary) {qH r : Nat}
    (hbudget : HasAdversaryBudget adversary qH r) :
    forgeAdvantage adversary ≤ (gameQueries qH r : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
  unforgeable _ (by simp only [gameQueries, keyGenQueries]; omega) adversary
    (hasHashQueryBound_of_budget adversary hbudget)

/-- An upper bound on the calls of key generation, `2^32` requests and the final verification. -/
def lifetimeQueries : Nat := gameQueries 0 (2 ^ LOG_LIFETIME)

/-- With at most `qH` calls of `H` and `2^32` requests, a forgery has chance `<= (qH + C) / 2^127`.

`C = 2^65 + 410 * 2^48 + 204 * 2^32 + 205 * 2^16 + 385`.

It covers key generation, the signer and the verifier. -/
theorem forgeAdvantage_le_lifetime (adversary : Adversary) {qH r : Nat}
    (hbudget : HasAdversaryBudget adversary qH r) (hr : r ≤ 2 ^ LOG_LIFETIME) :
    forgeAdvantage adversary ≤
      ((qH + lifetimeQueries : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  refine (forgeAdvantage_le_adversaryBudget adversary hbudget).trans
    (ENNReal.div_le_div (Nat.cast_le.2 ?_) le_rfl)
  simp only [lifetimeQueries, gameQueries]
  have := Nat.mul_le_mul_right requestQueries hr
  omega

/-- The constant of the lifetime bound is `2^65 + 410 * 2^48 + 204 * 2^32 + 205 * 2^16 + 385`. -/
theorem lifetimeQueries_eq :
    lifetimeQueries = 2 ^ 65 + 410 * 2 ^ 48 + 204 * 2 ^ 32 + 205 * 2 ^ 16 + 385 := by
  simp only [lifetimeQueries, gameQueries, keyGenQueries, requestQueries, verifyQueries,
    LOG_LIFETIME, LAYER_HEIGHT]
  norm_num

end EthLib.Cryptography.Xmss.Unforgeability
