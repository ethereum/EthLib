module

public import EthLib.Cryptography.Proofs.LazyPermutation
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.MapLens
import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Proofs: indifferentiability from a random oracle

A hash `H` built on a permutation `π` is compared with a random oracle.

This is Definition 1 of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §2.

Their §2 quotes it from their reference [7].

A game here is a functionality-respecting single-stage game.

Such games are those of [Ristenpart, Shacham, Shrimpton][rss], §3.

For such a game, the composition below is their Theorem 3.1.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
[rss]: https://hovav.net/ucsd/dist/revindiff.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Indifferentiability

open OracleComp OracleSpec ENNReal LazyPermutation

variable {A Msg Dg σ : Type}

/-! ## The two worlds

A game asks two oracles, the hash and the permutation in both directions, and returns a bit.
-/

/-- The oracles of the ideal world: coins and the random oracle of messages. -/
abbrev RomSpec (Msg Dg : Type) := unifSpec + (Msg →ₒ Dg)

/-- The oracles of a game: coins, the permutation in both directions, and the hash. -/
abbrev GameSpec (A Msg Dg : Type) := (unifSpec + PermSpec A) + (Msg →ₒ Dg)

/-- The real world: the permutation `π` in both directions, and the hash `H` built on `π`. -/
def realImpl (H : (A → A) → Msg → Dg) (π : Equiv.Perm A) :
    QueryImpl (GameSpec A Msg Dg) ProbComp :=
  permImpl π + fun m => (pure (H π m) : ProbComp Dg)

/-- The ideal world: coins and hash calls go to the random oracle.

The simulator answers the permutation. -/
def idealImpl (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))) :
    QueryImpl (GameSpec A Msg Dg) (StateT σ (OracleComp (RomSpec Msg Dg)))
  | .inl (.inl n) =>
    (liftM ((RomSpec Msg Dg).query (.inl n)) : OracleComp (RomSpec Msg Dg) (Fin (n + 1)))
  -- The simulator keeps a state, flips coins and asks the random oracle, but sees no hash call.
  | .inl (.inr q) => S q
  | .inr m => (liftM ((RomSpec Msg Dg).query (.inr m)) : OracleComp (RomSpec Msg Dg) Dg)

/-- The game in the random-oracle model whose permutation calls the simulator answers.

The simulator starts in the state `s₀`. -/
def romGame (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))) (s₀ : σ)
    (game : OracleComp (GameSpec A Msg Dg) Bool) : OracleComp (RomSpec Msg Dg) Bool :=
  (simulateQ (idealImpl S) game).run' s₀

/-- The chance that a game returns `true` in the real world. -/
noncomputable def realProb [FinEnum A] (H : (A → A) → Msg → Dg)
    (game : OracleComp (GameSpec A Msg Dg) Bool) : ℝ≥0∞ :=
  -- In the real world the permutation is uniform.
  Pr{let π ← $ᵗ (Equiv.Perm A); let b ← simulateQ (realImpl H π) game}[b = true]

/-- The chance that a game in the random-oracle model returns `true`.

The random oracle starts with no answer. -/
noncomputable def romProb [DecidableEq Msg] [SampleableType Dg]
    (game : OracleComp (RomSpec Msg Dg) Bool) : ℝ≥0∞ :=
  Pr{let b ← (simulateQ (Msg →ₒ Dg).romImpl game).run' ∅}[b = true]

/-! ## The cost of a game

The cost of Bertoni et al., §3.5, replaces the query count.
-/

/-- The cost of a call: nothing for coins, 1 for the permutation, and `hashCost m` for a hash. -/
def queryCost (hashCost : Msg → ℕ) : (ℕ ⊕ (A ⊕ A)) ⊕ Msg → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr m => hashCost m

/-- A game whose calls cost at most `N` in total, on every run. -/
def WithinCost (hashCost : Msg → ℕ) {α : Type} (game : OracleComp (GameSpec A Msg Dg) α)
    (N : ℕ) : Prop :=
  IsQueryBound game N (fun t n => queryCost hashCost t ≤ n) fun t n => n - queryCost hashCost t

/-! ## Indifferentiability -/

/-- A simulator that asks the random oracle at most once for each call to it, from every state.

Its coins are free.

The simulator of Bertoni et al., §4.3, Algorithm 3, asks its oracle at most once per call.

Their oracle returns outputs of any length, and this one returns outputs of one fixed type `Dg`.

A version of their simulator that draws the other output bits itself is such a simulator. -/
def AsksOnce (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))) : Prop :=
  ∀ t s, IsQueryBoundP ((S t).run s) (·.isRight = true) 1

/-- **Indifferentiability from a random oracle, with bound `ε` on the cost.**

One simulator, with one start state, serves every game.

It asks the random oracle at most once per call.

A game that costs at most `N` returns `true` with chances in the two worlds at most `ε N` apart.

The definition is Definition 1 of Bertoni et al., §2, without the bounds on running times.

Definition 1 also bounds the running times of the game and the simulator. -/
def Indifferentiable [FinEnum A] [DecidableEq Msg] [SampleableType Dg]
    (H : (A → A) → Msg → Dg) (hashCost : Msg → ℕ) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ (σ : Type) (s₀ : σ) (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))),
    AsksOnce S ∧
    ∀ (game : OracleComp (GameSpec A Msg Dg) Bool) (N : ℕ), WithinCost hashCost game N →
      realProb H game ≤ romProb (romGame S s₀ game) + ε N ∧
        romProb (romGame S s₀ game) ≤ realProb H game + ε N

/-- A larger bound keeps indifferentiability. -/
theorem Indifferentiable.mono [FinEnum A] [DecidableEq Msg] [SampleableType Dg]
    {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ} {ε ε' : ℕ → ℝ≥0∞}
    (h : Indifferentiable H hashCost ε) (hε : ∀ N, ε N ≤ ε' N) :
    Indifferentiable H hashCost ε' := by
  obtain ⟨σ, s₀, S, hS, hgame⟩ := h
  exact ⟨σ, s₀, S, hS, fun game N hN => ⟨(hgame game N hN).1.trans (add_le_add le_rfl (hε N)),
    (hgame game N hN).2.trans (add_le_add le_rfl (hε N))⟩⟩

/-- The exact term of Bertoni et al., §4.3, Lemma 5, for rate `r`, capacity `c` and a cost `N`.

It is `1 - prod_{i < N} (1 - (i + 1) / 2^c) / (1 - i / (2^r 2^c))`, computed in the reals.

Their Lemma 5 bounds the advantage by this term for `N` below `2^c`.

Their Theorem 2 rests on that lemma.

From `N = 2^c` on, a factor of the product is zero, so the term is 1. -/
noncomputable def spongeExact (r c N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - ∏ i ∈ Finset.range N,
    (1 - ((i : ℝ) + 1) / 2 ^ c) / (1 - (i : ℝ) / (2 ^ r * 2 ^ c)))

/-- The closed form of Bertoni et al., §4.3, equation (6), for rate `r` and capacity `c`.

It is `x = ((1 - 2^-r) N^2 + (1 + 2^-r) N) / 2^(c + 1)`, for a cost `N`.

For `N` well below `2^c`, equation (6) approximates the exact term by `1 - e^-x`.

Equation (6) then notes that `1 - e^-x` is below `x`.

EthLib proves that `x` bounds the exact term, for every `N`.

For `N` at least `2^c` the closed form is at least 1, so their condition `N < 2^c` costs nothing. -/
noncomputable def spongeBound (r c N : ℕ) : ℝ≥0∞ :=
  ((1 - 2⁻¹ ^ r) * (N : ℝ≥0∞) ^ 2 + (1 + 2⁻¹ ^ r) * N) / 2 ^ (c + 1)

/-! ## The closed form and the exact term -/

/-- One factor of the exact term, in the reals.

It needs `a` positive, `b` at least 1, `n` nonnegative and `n + 1` at most `a`.

It needs the product `P` before the factor nonnegative and at most `1 - n / a`.

Then the product with the factor is nonnegative and at most `1 - (n + 1) / a`.

One minus the product grows by at most `(n + 1) / a - n / (b a)`. -/
private theorem spongeFactor_bounds {a b n P S : ℝ} (ha : 0 < a) (hb : 1 ≤ b) (hn : 0 ≤ n)
    (hna : n + 1 ≤ a) (h0 : 0 ≤ P) (h1 : P ≤ 1 - n / a) (h2 : 1 - P ≤ S) :
    0 ≤ P * ((1 - (n + 1) / a) / (1 - n / (b * a))) ∧
      P * ((1 - (n + 1) / a) / (1 - n / (b * a))) ≤ 1 - (n + 1) / a ∧
      1 - P * ((1 - (n + 1) / a) / (1 - n / (b * a))) ≤ S + ((n + 1) / a - n / (b * a)) := by
  have hba : n / (b * a) ≤ n / a :=
    div_le_div_of_nonneg_left hn ha (le_mul_of_one_le_left ha.le hb)
  have hna' : n / a < 1 := (div_lt_one ha).2 (by linarith)
  have hd : 0 < 1 - n / (b * a) := by linarith
  have hnum : 0 ≤ 1 - (n + 1) / a := sub_nonneg.2 ((div_le_one ha).2 hna)
  have hgap : 0 ≤ (n + 1) / a - n / (b * a) := by
    have : n / a ≤ (n + 1) / a := div_le_div_of_nonneg_right (by linarith) ha.le
    linarith
  have hPd : P ≤ 1 - n / (b * a) := h1.trans (by linarith)
  have hy : 0 ≤ (1 - (n + 1) / a) / (1 - n / (b * a)) := div_nonneg hnum hd.le
  have hdy : (1 - n / (b * a)) * ((1 - (n + 1) / a) / (1 - n / (b * a))) = 1 - (n + 1) / a :=
    mul_div_cancel₀ _ hd.ne'
  have hle : P * ((1 - (n + 1) / a) / (1 - n / (b * a))) ≤ 1 - (n + 1) / a :=
    (mul_le_mul_of_nonneg_right hPd hy).trans hdy.le
  refine ⟨mul_nonneg h0 hy, hle, ?_⟩
  have hstep : P * (1 - (1 - (n + 1) / a) / (1 - n / (b * a))) ≤ (n + 1) / a - n / (b * a) := by
    have hy1 : 1 - (1 - (n + 1) / a) / (1 - n / (b * a))
        = ((n + 1) / a - n / (b * a)) / (1 - n / (b * a)) := by
      rw [one_sub_div hd.ne']
      congr 1
      ring
    rw [hy1]
    calc P * (((n + 1) / a - n / (b * a)) / (1 - n / (b * a)))
        ≤ (1 - n / (b * a)) * (((n + 1) / a - n / (b * a)) / (1 - n / (b * a))) :=
          mul_le_mul_of_nonneg_right hPd (div_nonneg hgap hd.le)
      _ = (n + 1) / a - n / (b * a) := mul_div_cancel₀ _ hd.ne'
  nlinarith

/-- The closed form in the reals grows by `(N + 1) / 2^c - N / (2^r 2^c)` from `N` to `N + 1`. -/
private theorem closedForm_succ (r c N : ℕ) :
    ((1 - 2⁻¹ ^ r) * ((N + 1 : ℕ) : ℝ) ^ 2 + (1 + 2⁻¹ ^ r) * ((N + 1 : ℕ) : ℝ)) / 2 ^ (c + 1)
      = ((1 - 2⁻¹ ^ r) * (N : ℝ) ^ 2 + (1 + 2⁻¹ ^ r) * N) / 2 ^ (c + 1)
        + (((N : ℝ) + 1) / 2 ^ c - N / (2 ^ r * 2 ^ c)) := by
  rw [inv_pow]
  push_cast
  field_simp
  ring

/-- The product of the exact term in the reals, up to a cost `N` of at most `2^c`.

It is nonnegative and at most `1 - N / 2^c`, and one minus it is at most the closed form. -/
private theorem spongeProduct_bounds (r c : ℕ) {N : ℕ} (hN : N ≤ 2 ^ c) :
    0 ≤ ∏ i ∈ Finset.range N, (1 - ((i : ℝ) + 1) / 2 ^ c) / (1 - (i : ℝ) / (2 ^ r * 2 ^ c)) ∧
      ∏ i ∈ Finset.range N, (1 - ((i : ℝ) + 1) / 2 ^ c) / (1 - (i : ℝ) / (2 ^ r * 2 ^ c))
        ≤ 1 - (N : ℝ) / 2 ^ c ∧
      1 - ∏ i ∈ Finset.range N, (1 - ((i : ℝ) + 1) / 2 ^ c) / (1 - (i : ℝ) / (2 ^ r * 2 ^ c))
        ≤ ((1 - 2⁻¹ ^ r) * (N : ℝ) ^ 2 + (1 + 2⁻¹ ^ r) * N) / 2 ^ (c + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih (by omega)
    have hna : (n : ℝ) + 1 ≤ 2 ^ c := by exact_mod_cast hN
    have hb : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    obtain ⟨k0, k1, k2⟩ := spongeFactor_bounds (by positivity) hb (Nat.cast_nonneg n) hna h0 h1 h2
    rw [Finset.prod_range_succ, closedForm_succ]
    push_cast
    exact ⟨k0, k1, k2⟩

/-- The closed form in the extended reals is the one in the reals. -/
private theorem spongeBound_eq_ofReal (r c N : ℕ) :
    spongeBound r c N
      = ENNReal.ofReal (((1 - 2⁻¹ ^ r) * (N : ℝ) ^ 2 + (1 + 2⁻¹ ^ r) * N) / 2 ^ (c + 1)) := by
  have hq : (0 : ℝ) ≤ 2⁻¹ ^ r := by positivity
  have hq1 : (0 : ℝ) ≤ 1 - 2⁻¹ ^ r := sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_add (by positivity)
    (by positivity), ENNReal.ofReal_mul hq1, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sub _ hq, ENNReal.ofReal_add zero_le_one hq]
  simp [spongeBound, ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, inv_pow, ENNReal.inv_pow]

/-- **The closed form of equation (6) bounds the exact term of Lemma 5.**

This holds for every rate, capacity and cost.

From `N = 2^c` on, the exact term is 1 and the closed form is at least 1. -/
theorem spongeExact_le_spongeBound (r c N : ℕ) : spongeExact r c N ≤ spongeBound r c N := by
  rw [spongeExact, spongeBound_eq_ofReal]
  rcases le_or_gt N (2 ^ c) with hN | hN
  · exact ENNReal.ofReal_le_ofReal (spongeProduct_bounds r c hN).2.2
  · obtain ⟨h0, h1, h2⟩ := spongeProduct_bounds r c (le_refl (2 ^ c))
    have hzero : ∏ i ∈ Finset.range (2 ^ c),
        (1 - ((i : ℝ) + 1) / 2 ^ c) / (1 - (i : ℝ) / (2 ^ r * 2 ^ c)) = 0 := by
      refine le_antisymm (h1.trans ?_) h0
      push_cast
      rw [div_self (by positivity), sub_self]
    rw [← Finset.prod_range_mul_prod_Ico _ hN.le, hzero, zero_mul, sub_zero]
    rw [hzero, sub_zero] at h2
    refine ENNReal.ofReal_le_ofReal (h2.trans ?_)
    have hc : ((2 ^ c : ℕ) : ℝ) ≤ N := by exact_mod_cast hN.le
    have hq1 : (0 : ℝ) ≤ 1 - 2⁻¹ ^ r := sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
    gcongr

/-- Indifferentiability with the exact term gives indifferentiability with the closed form. -/
theorem indifferentiable_spongeBound [FinEnum A] [DecidableEq Msg] [SampleableType Dg]
    {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ} {r c : ℕ}
    (h : Indifferentiable H hashCost (spongeExact r c)) :
    Indifferentiable H hashCost (spongeBound r c) :=
  h.mono (spongeExact_le_spongeBound r c)

/-! ## The calls of the image -/

/-- A lifted call keeps the bound on the random-oracle calls of the computation. -/
private theorem isQueryBoundP_liftM_run {α : Type} (oa : OracleComp (RomSpec Msg Dg) α) (s : σ)
    {n : ℕ} (h : IsQueryBoundP oa (·.isRight = true) n) :
    IsQueryBoundP ((liftM oa : StateT σ (OracleComp (RomSpec Msg Dg)) α).run s)
      (·.isRight = true) n := by
  rw [OracleComp.liftM_run_StateT]
  have := isQueryBoundP_bind (m := 0) (ob := fun a => (pure (a, s) : OracleComp _ _)) h
    fun _ _ => isQueryBoundP_pure _ _ _
  rwa [Nat.add_zero] at this

/-- The image of a game that costs at most `N` asks the random oracle at most `N` times.

Each hash call costs at least 1, and the simulator asks at most once per permutation call. -/
theorem isQueryBoundP_romGame_run {S : QueryImpl (PermSpec A)
    (StateT σ (OracleComp (RomSpec Msg Dg)))} (hS : AsksOnce S) {hashCost : Msg → ℕ}
    (hcost : ∀ m, 1 ≤ hashCost m) {α : Type} {game : OracleComp (GameSpec A Msg Dg) α} {N : ℕ}
    (hN : WithinCost hashCost game N) (s : σ) :
    IsQueryBoundP ((simulateQ (idealImpl S) game).run s) (·.isRight = true) N := by
  induction game using OracleComp.inductionOn generalizing N s with
  | pure x => simp
  | query_bind t k ih =>
    rw [WithinCost, isQueryBound_query_bind_iff] at hN
    obtain ⟨hle, hk⟩ := hN
    rw [simulateQ_query_bind, StateT.run_bind]
    have hstep : IsQueryBoundP ((idealImpl S t).run s) (·.isRight = true)
        (queryCost hashCost t) := by
      rcases t with (n | q) | m
      · exact isQueryBoundP_liftM_run _ s ((isQueryBoundP_query_iff _ _ _).2 (by simp))
      · exact hS q s
      · exact isQueryBoundP_liftM_run _ s ((isQueryBoundP_query_iff _ _ _).2 fun _ => hcost m)
    have := isQueryBoundP_bind (by simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift]
      using hstep) fun (p : (GameSpec A Msg Dg).Range t × σ) _ => ih p.1 (hk p.1) p.2
    rwa [Nat.add_sub_cancel' hle] at this

/-- The image of a game that costs at most `N` asks the random oracle at most `N` times. -/
theorem isQueryBoundP_romGame {S : QueryImpl (PermSpec A)
    (StateT σ (OracleComp (RomSpec Msg Dg)))} (hS : AsksOnce S) {hashCost : Msg → ℕ}
    (hcost : ∀ m, 1 ≤ hashCost m) (s₀ : σ) {game : OracleComp (GameSpec A Msg Dg) Bool} {N : ℕ}
    (hN : WithinCost hashCost game N) :
    IsQueryBoundP (romGame S s₀ game) (·.isRight = true) N := by
  rw [romGame, StateT.run'_eq, map_eq_bind_pure_comp]
  have := isQueryBoundP_bind (m := 0) (ob := pure ∘ fun x => x.1)
    (isQueryBoundP_romGame_run hS hcost hN s₀) fun _ _ => isQueryBoundP_pure _ _ _
  rwa [Nat.add_zero] at this

/-! ## Composition for single-stage games

A game here is one computation, so all its parts share their state.

Ristenpart et al., §4, show that composition fails for games with stages that share no state.
-/

/-- **Composition for single-stage games.**

Let `H` be indifferentiable from a random oracle with bound `ε`.

Then one simulator turns every game into a game in the random-oracle model.

It asks the random oracle at most once per call.

A game that costs at most `N` wins in the real world at most `ε N` more often than its image.

When only the adversary calls the permutation, the image runs it with the simulator in its place.

This is the advantage part of Theorem 3.1 of Ristenpart, Shacham and Shrimpton.

The bound on the calls of the image, their other part, is the theorem above. -/
theorem realProb_le_romProb_add [FinEnum A] [DecidableEq Msg] [SampleableType Dg]
    {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ} {ε : ℕ → ℝ≥0∞}
    (h : Indifferentiable H hashCost ε) :
    ∃ (σ : Type) (s₀ : σ) (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))),
      AsksOnce S ∧
      -- The adversary of a game is the part that calls the permutation.
      --
      -- The game's own procedures call the hash.
      ∀ (game : OracleComp (GameSpec A Msg Dg) Bool) (N : ℕ), WithinCost hashCost game N →
        realProb H game ≤ romProb (romGame S s₀ game) + ε N := by
  obtain ⟨σ, s₀, S, hS, hgame⟩ := h
  exact ⟨σ, s₀, S, hS, fun game N hN => (hgame game N hN).1⟩

/-- **A random-oracle bound carries over to the real world.**

Let `H` be indifferentiable from a random oracle with bound `ε`.

Take a game that costs at most `N`.

Let `δ` bound its image under every simulator that asks the random oracle at most once per call.

Then the game wins in the real world with chance at most `δ + ε N`.

Let each hash call cost at least 1.

The theorem on the calls of the image then bounds its random-oracle calls by `N`. -/
theorem realProb_le_of_romProb_le [FinEnum A] [DecidableEq Msg] [SampleableType Dg]
    {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ} {ε : ℕ → ℝ≥0∞}
    (h : Indifferentiable H hashCost ε) {game : OracleComp (GameSpec A Msg Dg) Bool} {N : ℕ}
    (hN : WithinCost hashCost game N) {δ : ℝ≥0∞}
    (hδ : ∀ (σ : Type) (s₀ : σ)
      (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))),
      AsksOnce S → romProb (romGame S s₀ game) ≤ δ) :
    realProb H game ≤ δ + ε N := by
  obtain ⟨σ, s₀, S, hS, hgame⟩ := realProb_le_romProb_add h
  exact (hgame game N hN).trans (add_le_add (hδ σ s₀ S hS) le_rfl)

/-! ## Relabelling the states, the digests and the messages

Indifferentiability does not depend on the names of the states, the digests or the messages.

A bijection of states maps a uniform permutation to a uniform permutation.

A bijection of digests maps a random oracle to a random oracle.

A bijection of messages maps a random oracle to a random oracle, and keeps the cost of each call.
-/

section Relabel

variable {A' Msg' Dg' : Type}

/-- A transport of a game that keeps the cost of each call keeps the cost of the game. -/
private theorem withinCost_mapLens {hashCost : Msg → ℕ} {hashCost' : Msg' → ℕ}
    (l : PFunctor.Lens (GameSpec A' Msg' Dg').toPFunctor (GameSpec A Msg Dg).toPFunctor)
    (hl : ∀ t, queryCost hashCost (l.toFunA t) = queryCost hashCost' t)
    {α : Type} {game : OracleComp (GameSpec A' Msg' Dg') α} {N : ℕ}
    (hN : WithinCost hashCost' game N) : WithinCost hashCost (game.mapLens l) N :=
  IsQueryBound.mapLens l (by simpa only [WithinCost, hl] using hN)

/-- The calls of a game over the states `A'`, asked over the states `A` through the bijection. -/
private def stateLens (e : A ≃ A') :
    PFunctor.Lens (GameSpec A' Msg Dg).toPFunctor (GameSpec A Msg Dg).toPFunctor where
  toFunA
    | .inl (.inl n) => .inl (.inl n)
    | .inl (.inr (.inl x)) => .inl (.inr (.inl (e.symm x)))
    | .inl (.inr (.inr y)) => .inl (.inr (.inr (e.symm y)))
    | .inr m => .inr m
  toFunB
    | .inl (.inl _) => id
    | .inl (.inr (.inl _)) => e
    | .inl (.inr (.inr _)) => e
    | .inr _ => id

/-- A simulator over the states `A`, run over the states `A'` through the bijection `e`. -/
private def stateSim {M : Type → Type} [Functor M] (e : A ≃ A') (S : QueryImpl (PermSpec A) M) :
    QueryImpl (PermSpec A') M
  | .inl x => e <$> S (.inl (e.symm x))
  | .inr y => e <$> S (.inr (e.symm y))

/-- The relabelled simulator asks the random oracle at most once per call. -/
private theorem asksOnce_stateSim {σ : Type} (e : A ≃ A')
    {S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))} (hS : AsksOnce S) :
    AsksOnce (stateSim e S) := by
  rintro (x | y) s
  · simpa [stateSim, StateT.run_map] using hS (.inl (e.symm x)) s
  · simpa [stateSim, StateT.run_map] using hS (.inr (e.symm y)) s

/-- The relabelled simulator on the game is the simulator on the relabelled game. -/
private theorem romGame_stateSim {σ : Type} (e : A ≃ A')
    (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))) (s₀ : σ)
    (game : OracleComp (GameSpec A' Msg Dg) Bool) :
    romGame (stateSim e S) s₀ game = romGame S s₀ (game.mapLens (stateLens e)) := by
  rw [romGame, romGame, OracleComp.simulateQ_mapLens]
  congr 2
  funext t
  rcases t with ((n | x | y) | m) <;> simp [stateLens, idealImpl, stateSim]

/-- The real world of the relabelled hash is the real world of the relabelled game. -/
private theorem realProb_stateLens [FinEnum A] [FinEnum A'] (e : A ≃ A') (H : (A → A) → Msg → Dg)
    (game : OracleComp (GameSpec A' Msg Dg) Bool) :
    realProb (fun π msg => H (fun a => e.symm (π (e a))) msg) game =
      realProb H (game.mapLens (stateLens e)) := by
  have hrun : ∀ π : Equiv.Perm A,
      simulateQ (realImpl (fun π msg => H (fun a => e.symm (π (e a))) msg) (e.permCongr π)) game =
        simulateQ (realImpl H π) (game.mapLens (stateLens e)) := by
    intro π
    have hH : (fun a => e.symm (e.permCongr π (e a))) = π := by
      funext a
      simp [Equiv.permCongr_apply]
    rw [OracleComp.simulateQ_mapLens]
    congr 1
    funext t
    rcases t with ((n | x | y) | m)
    · exact (id_map _).symm
    · change (pure _ : ProbComp A') = e <$> (pure _ : ProbComp A)
      rw [map_pure]
      rfl
    · change (pure _ : ProbComp A') = e <$> (pure _ : ProbComp A)
      rw [map_pure]
      rfl
    · change (pure (H (fun a => e.symm (e.permCongr π (e a))) m) : ProbComp Dg) =
        id <$> pure (H π m)
      rw [id_map, hH]
  have hmap := SampleableType.map_uniformSample_evalDistEq_of_bijective (e.permCongr).bijective
  unfold realProb
  have h := (hmap.bind_left fun π => (fun b => b = true) <$>
    simulateQ (realImpl (fun π msg => H (fun a => e.symm (π (e a))) msg) π) game).prEvent_eq id
  simp only [id_map, bind_map_left, hrun] at h
  exact h.symm

/-- The calls of a game over `Msg'` and `Dg'`, asked over `Msg` and `Dg` through the bijections. -/
private def oracleLens (e : Msg' ≃ Msg) (g : Dg ≃ Dg') :
    PFunctor.Lens (GameSpec A Msg' Dg').toPFunctor (GameSpec A Msg Dg).toPFunctor where
  toFunA
    | .inl t => .inl t
    | .inr m => .inr (e m)
  toFunB
    | .inl _ => id
    | .inr _ => g

/-- The calls to the random oracle over `Msg` and `Dg`, asked over `Msg'` and `Dg'`. -/
private def romLens (e : Msg' ≃ Msg) (g : Dg ≃ Dg') :
    PFunctor.Lens (RomSpec Msg Dg).toPFunctor (RomSpec Msg' Dg').toPFunctor where
  toFunA
    | .inl n => .inl n
    | .inr m => .inr (e.symm m)
  toFunB
    | .inl _ => id
    | .inr _ => g.symm

/-- The relabelled simulator asks the random oracle at most once per call. -/
private theorem asksOnce_romLens {σ : Type} (e : Msg' ≃ Msg) (g : Dg ≃ Dg')
    {S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))} (hS : AsksOnce S) :
    AsksOnce (((QueryImpl.id' _).comapLens (romLens e g)).mapStateTBase S) := by
  intro t s
  change IsQueryBoundP (simulateQ _ ((S t).run s)) _ 1
  rw [← mapLens_eq_simulateQ]
  have hp : (fun u => ((romLens e g).toFunA u).isRight = true) = fun u => u.isRight = true := by
    funext u
    rcases u with n | m <;> rfl
  exact IsQueryBoundP.mapLens _ (by simp only [hp]; exact hS t s)

/-- The relabelled simulator on the game is the transported image of the relabelled game. -/
private theorem romGame_romLens {σ : Type} (e : Msg' ≃ Msg) (g : Dg ≃ Dg')
    (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))) (s₀ : σ)
    (game : OracleComp (GameSpec A Msg' Dg') Bool) :
    romGame (((QueryImpl.id' _).comapLens (romLens e g)).mapStateTBase S) s₀ game =
      (romGame S s₀ (game.mapLens (oracleLens e g))).mapLens (romLens e g) := by
  rw [romGame, romGame, StateT.run'_eq, StateT.run'_eq, mapLens_map, mapLens_eq_simulateQ,
    QueryImpl.simulateQ_mapStateTBase_run, OracleComp.simulateQ_mapLens]
  congr 3
  funext t
  rcases t with ((n | q) | m) <;> apply StateT.ext <;> intro s
  · simp [oracleLens, idealImpl, romLens, QueryImpl.mapStateTBase]
  · simp [oracleLens, idealImpl, QueryImpl.mapStateTBase]
  · simp [oracleLens, idealImpl, romLens, QueryImpl.mapStateTBase]
    rw [e.symm_apply_apply]

/-- The real world of the relabelled hash is the real world of the relabelled game. -/
private theorem realProb_oracleLens [FinEnum A] (e : Msg' ≃ Msg) (g : Dg ≃ Dg')
    (H : (A → A) → Msg → Dg) (game : OracleComp (GameSpec A Msg' Dg') Bool) :
    realProb (fun π m => g (H π (e m))) game = realProb H (game.mapLens (oracleLens e g)) := by
  have hrun : ∀ π : Equiv.Perm A, simulateQ (realImpl (fun π m => g (H π (e m))) π) game =
      simulateQ (realImpl H π) (game.mapLens (oracleLens e g)) := by
    intro π
    rw [OracleComp.simulateQ_mapLens]
    congr 1
    funext t
    rcases t with t | m
    · exact (id_map _).symm
    · change (pure (g (H π (e m))) : ProbComp Dg') = g <$> pure (H π (e m))
      rw [map_pure]
  unfold realProb
  simp only [hrun]

/-- A random oracle read through bijections of messages and digests is a random oracle. -/
private theorem romProb_mapLens_romLens [DecidableEq Msg] [DecidableEq Msg'] [SampleableType Dg]
    [SampleableType Dg'] (e : Msg' ≃ Msg) (g : Dg ≃ Dg') (oa : OracleComp (RomSpec Msg Dg) Bool) :
    romProb (oa.mapLens (romLens e g)) = romProb oa := by
  -- A cache over `Msg'` and `Dg'` is read as a cache over `Msg` and `Dg`.
  let read : (Msg' →ₒ Dg').QueryCache → (Msg →ₒ Dg).QueryCache :=
    fun c => QueryCache.ofFn fun m => (c (e.symm m)).map g.symm
  have hstep : QueryImpl.IntertwinesOn (fun _ => True) (fun c => (pure (read c) : ProbComp _))
      ((Msg' →ₒ Dg').romImpl.comapLens (romLens e g)) (Msg →ₒ Dg).romImpl := by
    refine QueryImpl.IntertwinesOn.of_evalDistEq fun t c _ => ?_
    rcases t with n | m
    · simp only [QueryImpl.comapLens_apply, romLens, OracleSpec.romImpl,
        roSim.run_apply_inl, id_map, pure_bind, bind_pure_comp]
      exact EvalDistEq.rfl
    · have hread : ∀ u, read (c.cacheQuery (e.symm m) u) = (read c).cacheQuery m (g.symm u) := by
        intro u
        ext m'
        by_cases hm : m' = m
        · subst hm
          simp [read]
        · simp [read, hm]
      simp only [QueryImpl.comapLens_apply, romLens, OracleSpec.romImpl, StateT.run_map,
        pure_bind, bind_pure_comp, QueryImpl.add_apply_inr, randomOracle.run_eq]
      have hrc : (read c) m = (c (e.symm m)).map g.symm := rfl
      rw [hrc]
      cases hc : c (e.symm m) with
      | some u =>
        simp only [Option.map_some, map_pure, pure_bind]
        exact EvalDistEq.rfl
      | none =>
        have hu := SampleableType.map_uniformSample_evalDistEq_of_bijective (α := Dg') (β := Dg)
          g.symm.bijective
        simpa [hread, Functor.map_map] using hu.map_congr fun a => (a, (read c).cacheQuery m a)
  have h := hstep.evalDist_simulateQ_run (fun _ _ _ _ _ => trivial) oa ∅ trivial
    (fun b _ => (pure b : ProbComp Bool))
  have hempty : read ∅ = ∅ := rfl
  simp only [pure_bind, map_pure, bind_pure_comp, hempty, ← StateT.run'_eq] at h
  unfold romProb
  rw [OracleComp.simulateQ_mapLens]
  exact (EvalDistEq.of_evalDist_eq h).prEvent_eq _

/-- **Relabelling the messages and the digests keeps indifferentiability**, with the same bound.

The relabelled hash reads each message through `e`, and costs what its image costs.

It applies `g` to every output. -/
theorem Indifferentiable.relabel [FinEnum A] [DecidableEq Msg] [DecidableEq Msg']
    [SampleableType Dg] [SampleableType Dg'] {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ}
    {ε : ℕ → ℝ≥0∞} (h : Indifferentiable H hashCost ε) (e : Msg' ≃ Msg) (g : Dg ≃ Dg') :
    Indifferentiable (fun π m => g (H π (e m))) (fun m => hashCost (e m)) ε := by
  obtain ⟨σ, s₀, S, hS, hgame⟩ := h
  refine ⟨σ, s₀, ((QueryImpl.id' _).comapLens (romLens e g)).mapStateTBase S,
    asksOnce_romLens e g hS, fun game N hN => ?_⟩
  rw [realProb_oracleLens, romGame_romLens, romProb_mapLens_romLens]
  exact hgame _ N (withinCost_mapLens _ (fun t => by rcases t with ((n | x) | m) <;> rfl) hN)

/-- **Relabelling the states keeps indifferentiability**, with the same bound and costs.

The relabelled hash reads `π` through the bijection `e` of states. -/
theorem Indifferentiable.relabel_state [FinEnum A] [FinEnum A'] [DecidableEq Msg]
    [SampleableType Dg] {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ} {ε : ℕ → ℝ≥0∞}
    (h : Indifferentiable H hashCost ε) (e : A ≃ A') :
    Indifferentiable (fun π msg => H (fun a => e.symm (π (e a))) msg) hashCost ε := by
  obtain ⟨σ, s₀, S, hS, hgame⟩ := h
  refine ⟨σ, s₀, stateSim e S, asksOnce_stateSim e hS, fun game N hN => ?_⟩
  rw [realProb_stateLens, romGame_stateSim]
  refine hgame _ N (withinCost_mapLens _ (fun t => ?_) hN)
  rcases t with ((n | x | y) | m) <;> rfl

/-- **Relabelling the digests keeps indifferentiability**, with the same bound and costs.

The relabelled hash applies the bijection `g` of digests to every output. -/
theorem Indifferentiable.relabel_digest [FinEnum A] [DecidableEq Msg] [SampleableType Dg]
    [SampleableType Dg'] {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ} {ε : ℕ → ℝ≥0∞}
    (h : Indifferentiable H hashCost ε) (g : Dg ≃ Dg') :
    Indifferentiable (fun π msg => g (H π msg)) hashCost ε :=
  h.relabel (Equiv.refl Msg) g

/-- **Relabelling the messages keeps indifferentiability**, with the same bound.

The relabelled hash reads each message through the bijection `e`, and costs what its image costs. -/
theorem Indifferentiable.relabel_message [FinEnum A] [DecidableEq Msg] [DecidableEq Msg']
    [SampleableType Dg] {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ} {ε : ℕ → ℝ≥0∞}
    (h : Indifferentiable H hashCost ε) (e : Msg' ≃ Msg) :
    Indifferentiable (fun π m => H π (e m)) (fun m => hashCost (e m)) ε :=
  h.relabel e (Equiv.refl Dg)

end Relabel

end EthLib.Cryptography.Indifferentiability
