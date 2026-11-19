module

public import EthLib.Cryptography.Proofs.LazyPermutation
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Proofs: indifferentiability from a random oracle

A hash `H` built on a permutation `π` is compared with a random oracle.

A game asks two oracles, the hash and the permutation in both directions, and returns a bit.

In the real world the permutation is uniform, and the hash is `H` built on it.

In the ideal world the hash is a random oracle, and a simulator answers the permutation.

The simulator keeps a state, flips coins and asks the random oracle, but sees no hash call.

`H` is indifferentiable from a random oracle with bound `ε` when one simulator serves every game.

Then a game that costs at most `N` tells the two worlds apart with advantage at most `ε N`.

This is Definition 1 of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §2.

Their §2 quotes it from their reference [7].

Here the cost of their §3.5 replaces the query count.

A call to the permutation costs 1, and the cost of a hash call is a parameter.

Definition 1 also bounds the running times of the game and the simulator; the version here does not.

A game here is one computation, so all its parts share their state.

Its adversary is the part that calls the permutation; the game's own procedures call the hash.

That is a functionality-respecting single-stage game of [Ristenpart, Shacham, Shrimpton][rss], §3.

For such a game, the composition below is their Theorem 3.1.

Their §4 shows that the composition fails for games with several stages that share no state.

Bertoni et al. bound the advantage of the sponge by the exact term of their Lemma 5.

`spongeExact_le_spongeBound` proves that the closed form of their equation (6) bounds that term.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
[rss]: https://hovav.net/ucsd/dist/revindiff.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Indifferentiability

open OracleComp OracleSpec ENNReal LazyPermutation

variable {A Msg Dg σ : Type}

/-! ## The two worlds -/

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
  Pr{let π ← $ᵗ (Equiv.Perm A); let b ← simulateQ (realImpl H π) game}[b = true]

/-- The chance that a game in the random-oracle model returns `true`.

The random oracle starts with no answer. -/
noncomputable def romProb [DecidableEq Msg] [SampleableType Dg]
    (game : OracleComp (RomSpec Msg Dg) Bool) : ℝ≥0∞ :=
  Pr{let b ← (simulateQ (Msg →ₒ Dg).romImpl game).run' ∅}[b = true]

/-! ## The cost of a game -/

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

Their oracle returns outputs of any length, and this one 256 bits.

A version of their simulator that draws the other output bits itself is such a simulator. -/
def AsksOnce (S : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))) : Prop :=
  ∀ t s, IsQueryBoundP ((S t).run s) (·.isRight = true) 1

/-- **Indifferentiability from a random oracle, with bound `ε` on the cost.**

One simulator, with one start state, serves every game.

It asks the random oracle at most once per call.

A game that costs at most `N` returns `true` with chances in the two worlds at most `ε N` apart.

The definition is Definition 1 of Bertoni et al., §2, without the bounds on running times. -/
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

It is `((1 - 2^-r) N^2 + (1 + 2^-r) N) / 2^(c + 1)`, for a cost `N`.

Write `x` for it.

For `N` well below `2^c`, equation (6) approximates the exact term by `1 - e^-x`.

It then notes that `1 - e^-x` is below `x`.

`spongeExact_le_spongeBound` proves that `x` bounds the exact term, for every `N`.

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

/-! ## Composition for single-stage games -/

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

end EthLib.Cryptography.Indifferentiability
