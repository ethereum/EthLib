module

public import EthLib.Cryptography.Wots

/-!
# Proofs: hash chains and the codeword search of WOTS+C

A walk of `s₁` steps, then `s₂` more, is a walk of `s₁ + s₂` steps.

The search returns the least admissible trial in its window.
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

end EthLib.Cryptography.Wots
