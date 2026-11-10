module

public import EthLib.Cryptography.Proofs.Bls.Security.PopWins

/-!
# Proofs: BLS aggregates with proofs of possession are unforgeable, from co-CDH

This is the bound for the game of aggregates with proofs of possession, in the random oracle model.

The reduction guesses the position `j` of the forged message among at most `q` message hashes.

It programs that hash to the challenge, and every other key hash to a known multiple of it.

A forgery at position `j` then gives the answer, unless one of two events happens.

- The message scalar drawn first at `j` is 0, with probability `1 / |F|` for each `j`.
- A key other than the honest one has the scalar 0, with probability at most `(qK - 1) / |F|`.

So a forger wins at most `q` times as often as the reduction, plus `(q + qK - 1) / |F|`.

The bound needs every element of `G1` to be a multiple of `g1`, as in a group of prime order.

It needs `qK` at most the characteristic of the scalars, so that the honest count is not zero.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

open OracleComp OracleSpec ENNReal MeasureTheory

variable {F G₁ G₂ M : Type} [DecidableEq M] [DecidableEq G₁] [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

omit [AddCommGroup G₁] [Module F G₁] in
/-- The message table never has more entries than there were message hash calls. -/
theorem impl_preservesInv_msgLength (g₂ : G₂) (a : F) :
    QueryImpl.PreservesInv (impl (M := M) (G₁ := G₁) g₂ a)
      fun st => st.msg.table.length ≤ st.msg.calls := by
  intro t st hst x hx
  rcases t with n | (m | m) | y
  · change x ∈ support ((·, st) <$> _) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨_, -, rfl⟩ := hx
    exact hst
  · change x ∈ support ((fun w => _) <$> hash g₂ m st.msg) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Security.impl_preservesInv_length g₂ a (.inr (.inl m)) st.msg hst w hw
  · change x ∈ support ((fun w => _) <$> ((fun w => _) <$> hash g₂ m st.msg)) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
    exact Security.impl_preservesInv_length g₂ a (.inr (.inl m)) st.msg hst w hw
  · change x ∈ support (keyHash g₂ y st) at hx
    rw [(mem_support_keyHash hx).2.2.2.1]
    exact hst

omit [AddCommGroup G₁] [Module F G₁] in
/-- An output of the game's oracles is an output of the oracles with some scalar fixed at `j`.

The game's run is distributed as that run with a uniform scalar, so both reach the same outputs. -/
theorem exists_mem_support_implAt {α : Type} {g₂ : G₂} {a : F} (j : ℕ)
    {oa : OracleComp (Spec M G₁ G₂) α} {st : State F G₁ M} {p : α × State F G₁ M}
    (hp : p ∈ support ((simulateQ (impl g₂ a) oa).run st)) :
    ∃ z, p ∈ support ((simulateQ (implAt g₂ a j z) oa).run st) := by
  rw [support_eq_of_evalDistEq (run_impl_eq_uniform_implAt g₂ a j oa st),
    mem_support_bind_iff] at hp
  obtain ⟨z, -, hz⟩ := hp
  exact ⟨z, hz⟩

/-- A run after the honest key hash stays within the bounds on hash calls.

Its outputs are outputs of the game, whose runs make at most `q` and `qK` calls. -/
theorem callBound_of_mem_support {scheme : Scheme G₁ G₂} {adversary : Adversary G₁ G₂ M}
    {q qK : ℕ} (hq : HashCallBound F scheme adversary q qK) {a t : F}
    {p : Output G₁ G₂ M × State F G₁ M}
    (hp : p ∈ support ((simulateQ (impl scheme.g₂ a)
      (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
        (State.withKey (a • scheme.g₁) t))) :
    p.2.msg.calls ≤ q ∧ p.2.keyCalls ≤ qK := by
  refine hq (wins scheme (a • scheme.g₁) p.2.msg.signed p.1, p.2) ?_
  unfold experiment
  rw [mem_support_bind_iff]
  refine ⟨a, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨p, ?_, by simp⟩
  rw [StateT.run_bind, keyHash_run_init, bind_map_left, mem_support_bind_iff]
  exact ⟨t, by simp, hp⟩

/-- In a game within `qK` key hash calls, a winning run has a nonzero honest count in `F`.

The count is at least one, since the honest key is among the keys.

It is below `qK`, since verification hashes each key after the honest proof's hash. -/
theorem honestCount_ne_zero {scheme : Scheme G₁ G₂} {adversary : Adversary G₁ G₂ M}
    {q qK : ℕ} (hchar : qK ≤ ringChar F) (hq : HashCallBound F scheme adversary q qK) {a t : F}
    {p : Output G₁ G₂ M × State F G₁ M}
    (hp : p ∈ support ((simulateQ (impl scheme.g₂ a)
      (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
        (State.withKey (a • scheme.g₁) t)))
    (hwin : wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true) :
    (honestCount (a • scheme.g₁) p : F) ≠ 0 := by
  have hmem : a • scheme.g₁ ∈ p.1.1.1.map Prod.fst := by
    simp only [wins, Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1.1.1.1
  have hpos : 0 < honestCount (a • scheme.g₁) p := List.count_pos_iff.mpr hmem
  have hle : honestCount (a • scheme.g₁) p ≤ p.1.1.1.length :=
    (List.count_le_length).trans (List.length_map _).le
  obtain ⟨z, hz⟩ := exists_mem_support_implAt 0 hp
  have hcalls := keyCalls_of_mem_support hz
  have hbound := (callBound_of_mem_support hq hp).2
  have hlt : honestCount (a • scheme.g₁) p < ringChar F := by
    simp only [State.withKey] at hcalls
    omega
  intro h
  rw [CharP.cast_eq_zero_iff F (ringChar F)] at h
  exact hpos.ne' (Nat.eq_zero_of_dvd_of_lt h hlt)

/-- The forger's advantage averages a win over the secret `a` and the honest key scalar `t`.

The run starts after the honest key hash, which draws `t`. -/
theorem forgeAdvantage_eq_lintegral (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) :
    letI : MeasurableSpace F := ⊤
    forgeAdvantage F scheme adversary = ∫⁻ a, ∫⁻ t,
      Pr{let p ← (simulateQ (impl scheme.g₂ a)
        (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
          (State.withKey (a • scheme.g₁) t)}[
        wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true] ∂𝒟[$ᵗ F] ∂𝒟[$ᵗ F] := by
  let : MeasurableSpace F := ⊤
  unfold forgeAdvantage experiment
  rw [prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun a => ?_
  dsimp only
  rw [StateT.run_bind, keyHash_run_init, bind_map_left, bind_assoc,
    prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun t => ?_
  change Pr{let z ← ((simulateQ (impl scheme.g₂ a)
        (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
          (State.withKey (a • scheme.g₁) t) >>= fun x =>
            pure (wins scheme (a • scheme.g₁) x.2.msg.signed x.1, x.2))}[z.1 = true] = _
  rw [bind_pure_comp, prEvent_map]

/-- A winning run has a key other than the honest one with the scalar 0, or a position `j < q`.

The position is that of its message, and the honest count is then not zero in the scalars.

So a win is at most `(qK - 1) / |F|` plus the sum over `j < q` of the wins at `j`. -/
theorem prEvent_wins_le_zeroKey_add_sum {scheme : Scheme G₁ G₂} {adversary : Adversary G₁ G₂ M}
    {q qK : ℕ} (hchar : qK ≤ ringChar F) (hq : HashCallBound F scheme adversary q qK) (a t : F) :
    Pr{let p ← (simulateQ (impl scheme.g₂ a)
        (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
          (State.withKey (a • scheme.g₁) t)}[
        wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true] ≤
      ((qK - 1 : ℕ) : ℝ≥0∞) * (Nat.card F : ℝ≥0∞)⁻¹ +
        ∑ j : Fin q, Pr{let p ← ((simulateQ (impl scheme.g₂ a)
          (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
            (State.withKey (a • scheme.g₁) t))}[
          At j p ∧ wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true ∧
            ¬ZeroKey (a • scheme.g₁) p.2 ∧ (honestCount (a • scheme.g₁) p : F) ≠ 0] := by
  refine le_trans (prEvent_mono_of_support _ _ (fun p => ZeroKey (a • scheme.g₁) p.2 ∨
      ∃ j ∈ Finset.univ, At ((j : Fin q) : ℕ) p ∧
        wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true ∧
          ¬ZeroKey (a • scheme.g₁) p.2 ∧ (honestCount (a • scheme.g₁) p : F) ≠ 0)
      fun p hp hw => ?_) ((prEvent_or_le _ _ _).trans
        (add_le_add (prEvent_zeroKey_le scheme adversary hq a t) (prEvent_exists_finset_le _ _ _)))
  by_cases hz : ZeroKey (a • scheme.g₁) p.2
  · exact Or.inl hz
  right
  obtain ⟨z, hz'⟩ := exists_mem_support_implAt 0 hp
  obtain ⟨k, s, hk, -⟩ := msgHash_of_mem_support hz'
  have hlt : k < p.2.msg.table.length :=
    (List.getElem?_eq_some_iff.mp (getElem?_of_lookup hk)).1
  have hlen : p.2.msg.table.length ≤ p.2.msg.calls :=
    simulateQ_run_preservesInv _ _ (impl_preservesInv_msgLength scheme.g₂ a) _ _
      (by simp [State.withKey, Security.State.init]) p hp
  have hcalls := (callBound_of_mem_support hq hp).1
  exact ⟨⟨k, by omega⟩, Finset.mem_univ _, ⟨s, hk⟩, hw, hz, honestCount_ne_zero hchar hq hp hw⟩

/-- A win at position `j` is at most `1 / |F|` plus the reduction's average success.

The game draws the message scalar `z` at `j` first, which is 0 with probability `1 / |F|`.

For `z ≠ 0`, a win at `j` is at most as likely as a success of the reduction with `Y = z • g2`. -/
theorem prEvent_at_le_lintegral {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    (hgen : ∀ x : G₁, ∃ sk : F, x = sk • scheme.g₁) (adversary : Adversary G₁ G₂ M)
    (a t : F) (j : ℕ) :
    letI : MeasurableSpace F := ⊤
    Pr{let p ← (simulateQ (impl scheme.g₂ a)
        (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
          (State.withKey (a • scheme.g₁) t)}[
        At j p ∧ wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true ∧
          ¬ZeroKey (a • scheme.g₁) p.2 ∧ (honestCount (a • scheme.g₁) p : F) ≠ 0] ≤
      (Nat.card F : ℝ≥0∞)⁻¹ + ∫⁻ z,
        Pr{let p ← (simulateQ (embedImpl scheme.g₂ (a • scheme.g₂) (z • scheme.g₂)
          (a • scheme.g₁) j) (run adversary (a • scheme.g₁) (t • (a • scheme.g₂)))).run
            (State.withKey (a • scheme.g₁) t)}[
          extract (a • scheme.g₁) j p.1 p.2 = (a * z) • scheme.g₂] ∂𝒟[$ᵗ F] := by
  let : MeasurableSpace F := ⊤
  rw [(run_impl_eq_uniform_implAt scheme.g₂ a j _ _).prEvent_eq,
    prEvent_bind_eq_lintegral_of_discrete]
  calc _ ≤ ∫⁻ z, (Pr{let y ← (pure z : ProbComp F)}[y = 0] +
          Pr{let p ← (simulateQ (embedImpl scheme.g₂ (a • scheme.g₂) (z • scheme.g₂)
            (a • scheme.g₁) j) (run adversary (a • scheme.g₁) (t • (a • scheme.g₂)))).run
              (State.withKey (a • scheme.g₁) t)}[
            extract (a • scheme.g₁) j p.1 p.2 = (a * z) • scheme.g₂]) ∂𝒟[$ᵗ F] :=
        lintegral_mono fun z => ?_
    _ = _ := by
      rw [lintegral_add_left Measurable.of_discrete, ← prEvent_bind_eq_lintegral_of_discrete,
        bind_pure, SampleableType.prEvent_uniformSample_eq_singleton_natCard]
  by_cases hz : z = 0
  · subst hz
    classical
    rw [prEvent_pure]
    exact (prEvent_le_one _).trans (by simp)
  · exact (prEvent_wins_le_extract hsound hgen adversary a t hz j).trans le_add_self

omit [AddCommGroup G₁] [Module F G₁] in
/-- The reduction succeeds with the average, over its guess `j < n + 1`, of its runs with `j`.

Each run is averaged over the scalar `s` of the honest key. -/
theorem prEvent_reduction_eq (g₂ : G₂) (adversary : Adversary G₁ G₂ M) (n : ℕ) (X₁ : G₁)
    (X₂ Y T : G₂) :
    letI : MeasurableSpace F := ⊤
    Pr{let g ← reduction (F := F) g₂ adversary (n + 1) X₁ X₂ Y}[g = T] =
      (∑ j : Fin (n + 1), ∫⁻ s, Pr{let p ← (simulateQ (embedImpl g₂ X₂ Y X₁ j)
        (run adversary X₁ (s • X₂))).run (State.withKey X₁ s)}[
          extract X₁ j p.1 p.2 = T] ∂𝒟[$ᵗ F]) / (n + 1) := by
  let : MeasurableSpace F := ⊤
  let : MeasurableSpace (Fin (n + 1)) := ⊤
  unfold reduction
  rw [prEvent_bind_eq_lintegral_of_discrete, ProbComp.lintegral_evalDist_uniformFin]
  congr 2
  funext j
  rw [prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun s => ?_
  change Pr{let g ← ((simulateQ (embedImpl g₂ X₂ Y X₁ j)
    (run adversary X₁ (s • X₂))).run (State.withKey X₁ s) >>= fun x =>
      pure (extract X₁ j x.1 x.2))}[g = T] = _
  rw [bind_pure_comp, prEvent_map]

omit [DecidableEq M] [DecidableEq G₁] in
/-- The advantage at co-CDH averages the solver's success over the scalars `a` and `c`. -/
theorem coCdhAdvantage_eq_lintegral [DecidableEq G₂] (g₁ : G₁) (g₂ : G₂)
    (adversary : CoCdhAdversary G₁ G₂) :
    letI : MeasurableSpace F := ⊤
    coCdhAdvantage F g₁ g₂ adversary = ∫⁻ a, ∫⁻ c,
      Pr{let g ← adversary (a • g₁) (a • g₂) (c • g₂)}[g = (a * c) • g₂] ∂𝒟[$ᵗ F] ∂𝒟[$ᵗ F] := by
  let : MeasurableSpace F := ⊤
  rw [coCdhAdvantage, coCdhExperiment, prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun a => ?_
  rw [prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun c => ?_
  rw [bind_pure_comp, prEvent_map]
  simp

omit [DecidableEq M] [DecidableEq G₁] [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] in
/-- Two uniform averages over the scalars commute, also across a finite sum. -/
theorem lintegral_sum_lintegral_comm {q : ℕ} (f : F → F → Fin q → ℝ≥0∞) :
    letI : MeasurableSpace F := ⊤
    ∫⁻ t, ∑ j, ∫⁻ z, f t z j ∂𝒟[$ᵗ F] ∂𝒟[$ᵗ F] =
      ∫⁻ z, ∑ j, ∫⁻ t, f t z j ∂𝒟[$ᵗ F] ∂𝒟[$ᵗ F] := by
  let : MeasurableSpace F := ⊤
  rw [lintegral_finsetSum _ fun _ _ => Measurable.of_discrete,
    lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
  exact Finset.sum_congr rfl fun j _ =>
    lintegral_lintegral_swap Measurable.of_discrete.aemeasurable

omit [DecidableEq M] [DecidableEq G₁] [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] in
/-- The uniform average of a constant plus a function is the constant plus the average. -/
theorem lintegral_uniform_const_add (c : ℝ≥0∞) (f : F → ℝ≥0∞) :
    letI : MeasurableSpace F := ⊤
    ∫⁻ x, (c + f x) ∂𝒟[$ᵗ F] = c + ∫⁻ x, f x ∂𝒟[$ᵗ F] := by
  let : MeasurableSpace F := ⊤
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- **Unforgeability of BLS aggregates with proofs of possession, from co-CDH.**

Let every run of the game make at most `q` message hash calls and `qK` key hash calls.

Let every element of `G1` be a multiple of `g1`, and `qK` be at most the characteristic of `F`.

Then the forger's advantage is at most `q` times the advantage of the reduction at co-CDH.

The bound adds `(q + qK - 1) / |F|`. -/
theorem forgeAdvantage_le [DecidableEq G₂] (scheme : Scheme G₁ G₂) (hsound : scheme.Sound F)
    (hgen : ∀ x : G₁, ∃ sk : F, x = sk • scheme.g₁) (adversary : Adversary G₁ G₂ M)
    {q qK : ℕ} (hq0 : 0 < q) (hchar : qK ≤ ringChar F)
    (hq : HashCallBound F scheme adversary q qK) :
    forgeAdvantage F scheme adversary ≤
      q * coCdhAdvantage F scheme.g₁ scheme.g₂ (reduction (F := F) scheme.g₂ adversary q) +
        ((q + qK - 1 : ℕ) : ℝ≥0∞) * (Nat.card F : ℝ≥0∞)⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  let : MeasurableSpace F := ⊤
  -- Every run hashes the honest key, so the bound on key hash calls is at least one.
  have hqK : 1 ≤ qK := by
    obtain ⟨p, hp⟩ := OracleComp.support_nonempty ((simulateQ (impl scheme.g₂ (0 : F))
      (run adversary ((0 : F) • scheme.g₁) ((0 : F) • ((0 : F) • scheme.g₂)))).run
        (State.withKey ((0 : F) • scheme.g₁) 0))
    obtain ⟨z, hz⟩ := exists_mem_support_implAt 0 hp
    have h₁ := keyCalls_of_mem_support hz
    have h₂ := (callBound_of_mem_support hq hp).2
    simp only [State.withKey] at h₁
    omega
  -- The reduction's success with the guess `j`, the honest scalar `t` and the challenge `z`.
  let G : F → F → F → Fin (n + 1) → ℝ≥0∞ := fun a t z j =>
    Pr{let p ← ((simulateQ (embedImpl scheme.g₂ (a • scheme.g₂) (z • scheme.g₂)
      (a • scheme.g₁) j) (run adversary (a • scheme.g₁) (t • (a • scheme.g₂)))).run
        (State.withKey (a • scheme.g₁) t))}[
      extract (a • scheme.g₁) j p.1 p.2 = (a * z) • scheme.g₂]
  have hstep : ∀ a t : F, Pr{let p ← ((simulateQ (impl scheme.g₂ a)
      (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
        (State.withKey (a • scheme.g₁) t))}[
      wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true] ≤
        (((qK - 1 : ℕ) : ℝ≥0∞) * (Nat.card F : ℝ≥0∞)⁻¹ +
          ((n + 1 : ℕ) : ℝ≥0∞) * (Nat.card F : ℝ≥0∞)⁻¹) +
          ∑ j, ∫⁻ z, G a t z j ∂𝒟[$ᵗ F] := by
    intro a t
    refine (prEvent_wins_le_zeroKey_add_sum hchar hq a t).trans ?_
    rw [add_assoc]
    refine add_le_add le_rfl ((Finset.sum_le_sum fun (j : Fin (n + 1)) _ =>
      prEvent_at_le_lintegral hsound hgen adversary a t j).trans_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hred : ∀ a : F, ∫⁻ z, ∑ j, ∫⁻ t, G a t z j ∂𝒟[$ᵗ F] ∂𝒟[$ᵗ F] =
      ((n + 1 : ℕ) : ℝ≥0∞) * ∫⁻ c, Pr{let g ← (reduction (F := F) scheme.g₂ adversary (n + 1)
        (a • scheme.g₁) (a • scheme.g₂) (c • scheme.g₂))}[g = (a * c) • scheme.g₂] ∂𝒟[$ᵗ F] := by
    intro a
    rw [← lintegral_const_mul _ Measurable.of_discrete]
    refine lintegral_congr fun c => ?_
    rw [prEvent_reduction_eq, Nat.cast_add, Nat.cast_one,
      ENNReal.mul_div_cancel (by positivity) (by simp)]
  rw [forgeAdvantage_eq_lintegral, coCdhAdvantage_eq_lintegral,
    ← lintegral_const_mul _ Measurable.of_discrete]
  calc _ ≤ ∫⁻ a, ((((qK - 1 : ℕ) : ℝ≥0∞) * (Nat.card F : ℝ≥0∞)⁻¹ +
          ((n + 1 : ℕ) : ℝ≥0∞) * (Nat.card F : ℝ≥0∞)⁻¹) +
          ∫⁻ t, ∑ j, ∫⁻ z, G a t z j ∂𝒟[$ᵗ F] ∂𝒟[$ᵗ F]) ∂𝒟[$ᵗ F] :=
        lintegral_mono fun a =>
          (lintegral_mono fun t => hstep a t).trans_eq (lintegral_uniform_const_add _ _)
    _ = _ := by
      rw [lintegral_uniform_const_add, add_comm]
      congr 1
      · refine lintegral_congr fun a => ?_
        rw [lintegral_sum_lintegral_comm, hred]
      · rw [← add_mul, ← Nat.cast_add]
        congr 2
        omega

end EthLib.Cryptography.Bls.Security.Pop
