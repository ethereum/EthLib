module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SeedHops

/-!
# Proofs: the bound for a budget of the adversary's own calls

The theorem's budget `q` counts every hash call of the game.

Here the budget is the adversary's own: at most `qH` calls of `H` and `r` signing requests.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants (LOG_LIFETIME LAYER_HEIGHT)
open XmssSecurity (OracleWorld HashSpec HashQueryBound simulateQ_countHashQueries
  countHashQueries_pure countHashQueries_query_bind)

/-! ## The calls of the game

Key generation, each request and the final verification make at most a fixed number of calls.

The bounds are `205 * 2^16 + 1`, `2^33 + 205 * 2^16 + 407` and `384`.
-/

/-- Coins make no hash call. -/
theorem isQueryBoundP_liftM_prob {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp OracleWorld α) (SufCma.IsHashCall HashSpec) 0 :=
  isQueryBoundP_liftM_isRight oa

/-- A computation of at most `n` hash queries makes at most `n` hash calls among the game's. -/
theorem isQueryBoundP_liftM_hash {α : Type} {n : Nat} :
    ∀ (oa : OracleComp HashSpec α), IsQueryBoundP oa (fun _ => True) n →
      IsQueryBoundP (liftM oa : OracleComp OracleWorld α) (SufCma.IsHashCall HashSpec) n :=
  fun oa h => XmssSecurity.isQueryBoundP_liftM_hashSpec oa
    -- Every hash query is a hash call of the game.
    ((isQueryBoundP_iff_isChargeBound _ _ _).2
      (((isQueryBoundP_iff_isChargeBound _ _ _).1 h).mono_charge fun _ => by
        simp [SufCma.IsHashCall]))

/-- `H` is one hash query. -/
theorem isQueryBoundP_H (x : Array UInt64) : IsQueryBoundP (H x) (fun _ => True) 1 :=
  (isQueryBoundP_map_iff _ _ _).2
    ((isQueryBoundP_query_iff (spec := HashSpec) _ _ 1).2 fun _ => Nat.one_pos)

/-- Key generation: the scheme seed, the parameter and the top tree. -/
theorem isQueryBoundP_keyGenWith_keyGenQueries (seed : Seed) :
    IsQueryBoundP (keyGenWith H seed) (fun _ => True) keyGenQueries := by
  refine (Cost.isQueryBoundP_keyGenWith isQueryBoundP_H seed).mono ?_
  simp [keyGenQueries, LAYER_HEIGHT]

/-- A signature: the bottom search, then at most one bottom tree and the top search. -/
theorem isQueryBoundP_signWith_requestQueries (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    IsQueryBoundP (signWith H sk idx msg) (fun _ => True) requestQueries := by
  refine (Cost.isQueryBoundP_signWith isQueryBoundP_H sk idx msg).mono ?_
  simp [requestQueries, Constants.MAX_RANDOMIZER_TRIALS, LAYER_HEIGHT]

/-- The adversary's run costs a call per hash query and a request's bound per request.

Each request signs with the key the request before it returned. -/
theorem isQueryBoundP_run_signingOracle {α : Type}
    (oa : OracleComp (OracleWorld + SigningSpec) α) {qH r : Nat}
    (hh : IsQueryBoundP oa IsAdversaryHash qH) (hr : IsQueryBoundP oa IsAdversaryRequest r)
    (sk : SecretKey) :
    IsQueryBoundP ((simulateQ (QueryImpl.ofLift OracleWorld
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) +
        SufCma.signingOracle scheme) oa).run sk).run (SufCma.IsHashCall HashSpec)
      (qH + r * requestQueries) := by
  refine isQueryBoundP_run_keyed _ (fun n sk => ?_) (fun x sk => ?_) (fun request sk => ?_) oa
    hh hr sk
  · rw [XmssSecurity.Bridge.run_keyedOracles_inl]
    exact (isQueryBoundP_map_iff _ _ _).2
      ((isQueryBoundP_query_iff (spec := OracleWorld) _ (.inl n) 0).2 fun h => by
        simp [SufCma.IsHashCall] at h)
  · rw [XmssSecurity.Bridge.run_keyedOracles_inl]
    exact (isQueryBoundP_map_iff _ _ _).2
      ((isQueryBoundP_query_iff (spec := OracleWorld) _ (.inr x) 1).2 fun _ => Nat.one_pos)
  · rw [XmssSecurity.Bridge.run_keyedOracles_inr]
    exact (isQueryBoundP_map_iff _ _ _).2
      (isQueryBoundP_liftM_hash _ (isQueryBoundP_signWith_requestQueries sk _ _))

/-- The game makes at most `Q` hash calls, for `qH` calls of `H` and `r` requests. -/
theorem isQueryBoundP_game (adversary : Adversary) {qH r : Nat}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    IsQueryBoundP (SufCma.game scheme adversary) (SufCma.IsHashCall HashSpec)
      (gameQueries qH r) := by
  rw [game_eq]
  unfold SufCma.gameAfterKeys SufCma.checkForgery
  refine (isQueryBoundP_bind (isQueryBoundP_liftM_prob sampleSeed) fun seed _ =>
    isQueryBoundP_bind
      (isQueryBoundP_liftM_hash _ (isQueryBoundP_keyGenWith_keyGenQueries seed))
      fun keys _ =>
      isQueryBoundP_bind (isQueryBoundP_run_signingOracle (adversary.main keys.1)
        (hh keys.1) (hr keys.1) keys.2) fun z _ =>
        isQueryBoundP_bind (m := 0) (isQueryBoundP_liftM_hash _
          (isQueryBoundP_verifyWith isQueryBoundP_H _ _ _)) fun _ _ =>
          isQueryBoundP_pure _ _ 0).mono ?_
  -- Sum the bounds of key generation, the requests and the verification.
  simp only [gameQueries, verifyQueries]
  omega

/-! ## From the calls of the game to its counted run -/

/-- The counted run makes at most `Q` calls, for `qH` calls of `H` and `r` requests. -/
theorem isGameQueryBound_of_budget (adversary : Adversary) {qH r : Nat}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    SufCma.IsGameQueryBound scheme (SufCma.randomOracleModel HashSpec) adversary
      (gameQueries qH r) :=
  (hashQueryBound_iff_counted _).1
    (XmssSecurity.hashQueryBound_of_isQueryBoundP _ (isQueryBoundP_game adversary hh hr) ∅)

/-! ## The bounds -/

/-- With at most `qH` calls of `H` and `r` requests, a forgery has chance `<= Q / 2^127`.

`Q = 205 * 2^16 + 1 + qH + r (2^33 + 205 * 2^16 + 407) + 384` bounds the calls of the game. -/
theorem advantage_le_adversaryBudget (adversary : Adversary) {qH r : Nat}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    SufCma.advantage scheme (SufCma.randomOracleModel HashSpec) adversary ≤
      (gameQueries qH r : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 127 :=
  unforgeable _ (by simp only [gameQueries, keyGenQueries]; omega) adversary
    (isGameQueryBound_of_budget adversary hh hr)

/-- An upper bound on the calls of key generation, `2^32` requests and the final verification. -/
def lifetimeQueries : Nat := gameQueries 0 (2 ^ LOG_LIFETIME)

/-- With at most `qH` calls of `H` and `2^32` requests, a forgery has chance `<= (qH + C) / 2^127`.

`C = 2^65 + 205 * 2^48 + 407 * 2^32 + 205 * 2^16 + 385`.

It covers key generation, the signer and the verifier. -/
theorem advantage_le_lifetime (adversary : Adversary) {qH r : Nat}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hreq : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r)
    (hr : r ≤ 2 ^ LOG_LIFETIME) :
    SufCma.advantage scheme (SufCma.randomOracleModel HashSpec) adversary ≤
      ((qH + lifetimeQueries : Nat) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 127 := by
  refine (advantage_le_adversaryBudget adversary hh hreq).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 ?_) (by positivity))
  simp only [lifetimeQueries, gameQueries]
  -- A key has `2^32` leaf indices, so it signs at most `2^32` requests.
  --
  -- A request's bound has two searches of `2^32` trials each, and the theorem charges all of it.
  --
  -- So the bound is above `2^-62` for every adversary.
  have := Nat.mul_le_mul_right requestQueries hr
  omega

/-- The constant of the lifetime bound is `2^65 + 205 * 2^48 + 407 * 2^32 + 205 * 2^16 + 385`. -/
theorem lifetimeQueries_eq :
    lifetimeQueries = 2 ^ 65 + 205 * 2 ^ 48 + 407 * 2 ^ 32 + 205 * 2 ^ 16 + 385 := by
  simp only [lifetimeQueries, gameQueries, keyGenQueries, requestQueries, verifyQueries,
    LOG_LIFETIME, LAYER_HEIGHT]
  norm_num

/-! ## The bound for the adversary's own hash calls -/

open XmssSecurity.Ghost (IsAdvHash) in
/-- The model's run of the adversary makes its hash calls, one query each, and nothing more. -/
theorem isQueryBoundP_simulateQ_adversaryImpl {α : Type} :
    ∀ (oa : OracleComp (OracleWorld + SigningSpec) α) (n : Nat),
      IsQueryBoundP oa IsAdversaryHash n →
        IsQueryBoundP (simulateQ adversaryImpl oa) IsAdvHash n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_query_bind]
    rcases t with world | request
    · -- A world query is the same query of the model, a hash call exactly when it was one.
      have hiff : IsAdvHash (.inl world) ↔ IsAdversaryHash (.inl world) := by
        rcases world with _ | _ <;> exact Iff.rfl
      refine (isQueryBoundP_bind (n := if IsAdvHash (.inl world) then 1 else 0) ?_
        fun u _ => ih u _ (h.2 u)).mono ?_
      · exact (isQueryBoundP_query_iff (spec := XmssSecurity.OracleWorld + XmssSecurity.SigningSpec)
          _ (.inl world) _).2 fun hp => by simp [hp]
      · by_cases hw : IsAdvHash (.inl world)
        · have := h.1.resolve_left (not_not.2 (hiff.1 hw))
          rw [ite_eq_left hw, ite_eq_left (hiff.1 hw)]
          omega
        · rw [ite_eq_right hw, ite_eq_right (fun hh => hw (hiff.2 hh))]
          omega
    · -- A request is one request of the model, which is no hash call.
      refine (isQueryBoundP_bind (p := IsAdvHash) (n := 0) (m := n) ?_ fun u _ => ?_).mono
        (by omega)
      · exact (isQueryBoundP_map_iff _ _ _).2
          ((isQueryBoundP_query_iff (spec := XmssSecurity.OracleWorld + XmssSecurity.SigningSpec)
            _ (.inr _) 0).2 fun hp => hp.elim)
      · have hk := h.2 u
        rw [ite_eq_right (show ¬IsAdversaryHash (.inr request) from id)] at hk
        exact ih u n hk

open XmssSecurity.Ghost (IsAdvHash) in
/-- Memoizing the signing requests keeps every hash call and adds none. -/
theorem isQueryBoundP_memoize {α : Type} :
    ∀ (oa : OracleComp (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec) α)
      (cache : QueryCache XmssSecurity.SigningSpec) (n : Nat),
      IsQueryBoundP oa IsAdvHash n →
        IsQueryBoundP (DeterministicSigning.memoize oa cache) IsAdvHash n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache n _; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    intro cache n h
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with world | request
    · rw [DeterministicSigning.memoize_base]
      refine (isQueryBoundP_bind (n := if IsAdvHash (.inl world) then 1 else 0) ?_
        fun u _ => ih u cache _ (h.2 u)).mono ?_
      · exact (isQueryBoundP_query_iff (spec := XmssSecurity.OracleWorld + XmssSecurity.SigningSpec)
          _ (.inl world) _).2 fun hp => by simp [hp]
      · by_cases hw : IsAdvHash (.inl world)
        · have := h.1.resolve_left (not_not.2 hw)
          rw [ite_eq_left hw, ite_eq_left hw]
          omega
        · rw [ite_eq_right hw, ite_eq_right hw]
          omega
    · have hnext : ∀ u, IsQueryBoundP (k u) IsAdvHash n := fun u => by
        simpa [ite_eq_right (show ¬IsAdvHash (.inr request) from id)] using h.2 u
      rw [DeterministicSigning.memoize_request]
      cases hc : cache request with
      | some answer => exact ih answer cache n (hnext answer)
      | none =>
        dsimp only
        refine (isQueryBoundP_bind (p := IsAdvHash) (n := 0) (m := n) ?_
          fun u _ => ih u _ n (hnext u)).mono (by omega)
        exact (isQueryBoundP_query_iff (spec := XmssSecurity.OracleWorld + XmssSecurity.SigningSpec)
          _ (.inr request) 0).2 fun hp => hp.elim

open XmssSecurity.Ghost (IsAdvHash) in
/-- The model's adversary makes the hash calls of the adversary, on every public key. -/
theorem isQueryBoundP_modelAdversary (adversary : Adversary) {qH : Nat}
    (h : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (pk : XmssSecurity.PublicKey) :
    IsQueryBoundP ((XmssSecurity.Bridge.modelAdversary adversary).main pk) IsAdvHash qH :=
  isQueryBoundP_memoize _ ∅ qH
    ((isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_simulateQ_adversaryImpl _ qH (h _)))

/-- **leanXMSS as EthLib computes it is strongly unforgeable, for the adversary's own calls.**

The adversary itself makes at most `q` calls of `H` and `2^32` requests.

It forges with probability at most `(q + 530) * 2^-127`.

Key generation, the signer and the final verification are not charged to `q`. -/
theorem stronglyUnforgeable :
    SufCma.StronglyUnforgeable scheme (SufCma.randomOracleModel HashSpec) (2 ^ LOG_LIFETIME)
      530 127 := by
  intro qH adversary hh hreq
  rw [SufCma.mul_inv_two_pow, ← Nat.cast_add]
  -- The request budget `r` is the key's lifetime.
  obtain ⟨r, hr, hreq⟩ : ∃ r, r ≤ 2 ^ LOG_LIFETIME ∧
      ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r :=
    ⟨_, le_rfl, hreq⟩
  by_cases hbig : 2 ^ 127 ≤ qH + 530
  · -- From there on, the bound is at least one.
    refine (prEvent_le_one _).trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _)),
      one_mul]
    exact_mod_cast hbig
  -- The game's calls are at most `2^128`, so each seed guess term costs at most `2^-128`.
  have hq : gameQueries qH r ≤ 2 ^ 128 := by
    have := Nat.mul_le_mul_right requestQueries hr
    norm_num [gameQueries, keyGenQueries, requestQueries, verifyQueries, LOG_LIFETIME,
      LAYER_HEIGHT] at this hbig ⊢
    omega
  have hmodel := XmssSecurity.CappedChain.capped_forgeAdvantage_le_of_adversaryBound qH
    (XmssSecurity.Bridge.modelAdversary adversary)
    (isQueryBoundP_modelAdversary adversary hh)
  refine (advantage_eq adversary).trans_le
    ((XmssSecurity.Bridge.realGame_le_model (gameQueries qH r) (by omega) adversary
      (hashQueryBound_realGame adversary _ (isGameQueryBound_of_budget adversary hh hreq))).trans
      ((add_le_add (add_le_add hmodel (XmssSecurity.Bridge.guesses_le (by omega)))
        (XmssSecurity.Bridge.guesses_le (by omega))).trans ?_))
  -- The model's bound is `(2 qH + 1058) / 2^128`, and the two guesses add `2 / 2^128`.
  rw [← ENNReal.add_div, ← ENNReal.add_div]
  rw [show ((2 ^ 128 : Nat) : ℝ≥0∞) = 2 * ((2 ^ 127 : Nat) : ℝ≥0∞) by norm_num]
  rw [show ((2 * qH + 1058 : Nat) : ℝ≥0∞) + 1 + 1 = 2 * ((qH + 530 : Nat) : ℝ≥0∞) by
    push_cast; ring]
  exact (ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)).le

end EthLib.Cryptography.Xmss.Unforgeability
