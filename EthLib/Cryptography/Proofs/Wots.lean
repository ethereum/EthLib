module

public import EthLib.Cryptography.Wots
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Proofs: hash chains and the codeword search of WOTS+C

A walk of `s₁` steps, then `s₂` more, is a walk of `s₁ + s₂` steps.

A map of monads that keeps `pure` and `bind` commutes with a walk.

The search returns the least admissible trial in its window.

When the hash is a random oracle, a search over fresh inputs fails with an exact probability.
-/

@[expose] public section

namespace EthLib.Cryptography.Wots

/-! ## Chains -/

section Chain

variable {m : Type → Type} [Monad m] {α : Type} {n : Nat} {step : Fin n → α → m α}
  {start : Nat} {value : α}

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 ≤ n) : chain step start 0 h value = pure value := rfl

/-- A walk of `s + 1` steps is a walk of `s` steps, then the step from position `start + s`. -/
theorem chain_succ {s : Nat} (h : start + (s + 1) ≤ n) :
    chain step start (s + 1) h value =
      chain step start s (by omega) value >>= step ⟨start + s, by omega⟩ := rfl

/-- The bound on a walk is a proof, so walks of equal length agree. -/
theorem chain_steps_congr {steps steps' : Nat} (hs : steps = steps')
    (h : start + steps ≤ n) (h' : start + steps' ≤ n) :
    chain step start steps h value = chain step start steps' h' value := by
  subst hs
  rfl

/-- A walk of `s₁` steps, then `s₂` more from where it ends, is a walk of `s₁ + s₂` steps.

The second walk starts at any `mid` equal to `start + s₁`. -/
theorem chain_add [LawfulMonad m] {s₁ s₂ mid : Nat} (hmid : mid = start + s₁)
    (h₁ : start + s₁ ≤ n) (h : mid + s₂ ≤ n) :
    chain step start s₁ h₁ value >>= chain step mid s₂ h
      = chain step start (s₁ + s₂) (by omega) value := by
  subst hmid
  induction s₂ with
  | zero => exact bind_pure _
  | succ s ih =>
    show (chain step start s₁ h₁ value >>= fun v =>
        chain step (start + s₁) s (by omega) v >>= step ⟨start + s₁ + s, by omega⟩) =
      chain step start (s₁ + s) (by omega) value >>= step ⟨start + (s₁ + s), by omega⟩
    rw [← bind_assoc, ih (by omega)]
    -- The last step leaves `start + s₁ + s`, the same as `start + (s₁ + s)`.
    have hpos : (⟨start + s₁ + s, by omega⟩ : Fin n) = ⟨start + (s₁ + s), by omega⟩ :=
      Fin.ext (Nat.add_assoc _ _ _)
    rw [hpos]

/-- A map of monads that keeps `pure` and `bind` commutes with a walk. -/
theorem chain_map_monad {m' : Type → Type} [Monad m'] (φ : ∀ {β : Type}, m β → m' β)
    (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
    (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
    (step : Fin n → α → m α) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ n) (value : α),
      φ (chain step start steps h value) = chain (fun i v => φ (step i v)) start steps h value
  | 0, _, _ => map_pure _
  | s + 1, h, value => by
    rw [chain_succ, chain_succ, map_bind, chain_map_monad φ map_pure map_bind step start s]

end Chain

/-! ## The search -/

/-- The search returns a trial in its window whose test gives a codeword, and no earlier one does.

So the trial is a function of the inputs: the least admissible one. -/
theorem findFirst_spec {κ β : Type} {trial : Nat → κ} {test : κ → Id (Option β)} :
    ∀ {fuel c : Nat} {k : κ} {x : β},
      (findFirst trial test c fuel).run = some (k, x) →
      ∃ j, c ≤ j ∧ j < c + fuel ∧ k = trial j ∧ (test k).run = some x ∧
        ∀ j', c ≤ j' → j' < j → (test (trial j')).run = none := by
  intro fuel
  induction fuel with
  | zero => intro c k x h; simp [findFirst] at h
  | succ fuel ih =>
    intro c k x h
    simp only [findFirst, Id.run_bind] at h
    split at h
    -- Trial `c` itself is admissible: it is the least.
    · rename_i x' hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
      exact ⟨c, Nat.le_refl _, by omega, rfl, hx, fun j' h₁ h₂ => absurd h₂ (by omega)⟩
    -- Trial `c` fails, so the answer comes from the trials after it.
    · rename_i hx
      obtain ⟨j, hj₁, hj₂, hk, hcw, hmin⟩ := ih h
      refine ⟨j, by omega, by omega, hk, hcw, fun j' h₁ h₂ => ?_⟩
      rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
      · exact hx
      · exact hmin j' h₁ h₂

/-! ## The search in the random-oracle model

Each trial makes one hash query, and the hash is a lazily sampled random oracle.

When the trials query distinct points that the cache does not hold, every answer is fresh.

So the trials fail independently, each with the probability that one uniform answer fails. -/

section RandomOracle

open OracleSpec OracleComp ENNReal

variable {ι R κ β : Type} [DecidableEq ι] [SampleableType R]

/-- **A search of `n` fresh trials fails with probability `q^n`.**

The oracle answers points of `ι` with uniform values of `R`, beside private uniform sampling.

Trial `j` hashes the point `key (trial j)` once, and its test reads the answer `u` as `f u`.

The window `[c, c + n)` hashes `n` distinct points, and the cache holds none of them.

Then the search returns nothing with probability `q^n`.

Here `q` is the chance that `f` gives nothing on one uniform answer. -/
theorem prEvent_findFirst_romImpl_none (trial : ℕ → κ) (key : κ → ι) (f : R → Option β)
    (test : κ → OracleComp (unifSpec + (ι →ₒ R)) (Option β))
    (htest : ∀ k, test k = f <$> liftM ((ι →ₒ R).query (key k))) :
    ∀ (n c : ℕ) (cache : (ι →ₒ R).QueryCache),
      (∀ j j', c ≤ j → j < c + n → c ≤ j' → j' < c + n →
        key (trial j) = key (trial j') → j = j') →
      (∀ j, c ≤ j → j < c + n → cache (key (trial j)) = none) →
      Pr{let z ← (simulateQ (ι →ₒ R).romImpl (findFirst trial test c n)).run' cache}[z = none] =
        Pr{let u ← $ᵗ R}[f u = none] ^ n := by
  intro n
  induction n with
  | zero => intro c cache _ _; simp [findFirst]
  | succ n ih =>
    intro c cache hinj hfresh
    have hc := hfresh c le_rfl (by omega)
    have hrun : (simulateQ (ι →ₒ R).romImpl (findFirst trial test c (n + 1))).run' cache =
        ($ᵗ R) >>= fun u => match f u with
          | some x => pure (some (trial c, x))
          | none => (simulateQ (ι →ₒ R).romImpl (findFirst trial test (c + 1) n)).run'
              (cache.cacheQuery (key (trial c)) u) := by
      rw [findFirst, htest]
      simp only [simulateQ_bind, simulateQ_map, roSim.simulateQ_liftM_spec_query, StateT.run'_eq,
        StateT.run_bind, StateT.run_map, randomOracle.run_eq, hc]
      simp only [map_bind, bind_map_left, bind_assoc, pure_bind]
      refine bind_congr fun u => ?_
      cases f u <;> simp
    have hinner : ∀ u, Pr{let z ← (match f u with
          | some x => pure (some (trial c, x))
          | none => (simulateQ (ι →ₒ R).romImpl (findFirst trial test (c + 1) n)).run'
              (cache.cacheQuery (key (trial c)) u))}[z = none] =
        if f u = none then Pr{let u ← $ᵗ R}[f u = none] ^ n else 0 := by
      intro u
      cases h : f u with
      | some x => simp
      | none =>
        simp only [↓reduceIte]
        refine ih (c + 1) _ (fun j j' h₁ h₂ h₃ h₄ => hinj j j' (by omega) (by omega) (by omega)
          (by omega)) fun j h₁ h₂ => ?_
        have hne : key (trial j) ≠ key (trial c) := fun he => by
          have := hinj j c (by omega) (by omega) le_rfl (by omega) he
          omega
        rw [QueryCache.cacheQuery_of_ne _ _ hne]
        exact hfresh j (by omega) (by omega)
    rw [hrun, prEvent_bind_eq_tsum]
    simp only [hinner]
    set q := Pr{let u ← $ᵗ R}[f u = none]
    calc (∑' u, Pr{let z ← $ᵗ R}[z = u] * if f u = none then q ^ n else 0)
        = ∑' u, (if f u = none then Pr{let z ← $ᵗ R}[z = u] else 0) * q ^ n :=
          tsum_congr fun u => by split_ifs <;> simp
      _ = q * q ^ n := by rw [ENNReal.tsum_mul_right, ← prEvent_eq_tsum_ite]
      _ = q ^ (n + 1) := (pow_succ' _ _).symm

end RandomOracle

end EthLib.Cryptography.Wots
