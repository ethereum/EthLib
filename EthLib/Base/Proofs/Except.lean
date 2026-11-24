module

public import EthLib.Base.Except

/-!
# Proofs: assertions, maps and sequences in `Except`

The properties characterize the success and failure of steps that return `Except`.
-/

@[expose] public section

namespace EthLib.Base

/-- An assertion succeeds exactly when its condition holds. -/
theorem ensure_ok_iff {ε : Type} {condition : Prop} [Decidable condition] {error : ε}
    {u : Unit} : ensure condition error = .ok u ↔ condition := by
  unfold ensure
  split <;> simp_all

/-- A failed assertion fails with its own error. -/
theorem eq_of_ensure_eq_error {ε : Type} {condition : Prop} [Decidable condition]
    {error other : ε} (failed : ensure condition error = .error other) : other = error := by
  unfold ensure at failed
  split at failed <;> simp_all

/-- A step after a success runs on the value of that success.

Rewriting with it, instead of unfolding the bind, leaves the value unevaluated. -/
theorem ok_bind {ε α β : Type} (a : α) (g : α → Except ε β) : (Except.ok a >>= g) = g a := rfl

/-- Two steps in sequence fail when the first fails, or when the second fails on its value. -/
theorem bind_eq_error {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {e : ε}
    (h : x >>= g = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ g a = .error e := by
  cases x <;> simp_all [bind, Except.bind]

/-- A check followed by a step succeeds exactly when the check passes and the step succeeds. -/
theorem bind_unit_ok_iff {ε β : Type} {x : Except ε Unit} {g : Unit → Except ε β} {y : β} :
    x >>= g = .ok y ↔ x = .ok () ∧ g () = .ok y := by
  cases x <;> simp [bind, Except.bind]

/-- A map over a success applies the function to its value. -/
theorem map_ok {ε α β : Type} (f : α → β) (a : α) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) :=
  rfl

/-- A map succeeds exactly when the step under it succeeds with some value.

The map then sends that value to the result. -/
theorem map_ok_iff {ε α β : Type} {f : α → β} {x : Except ε α} {y : β} :
    f <$> x = .ok y ↔ ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp [Functor.map, Except.map]

/-- A success relabelled and passed on is the value passed on. -/
theorem mapError_ok_bind {ε ε' α β : Type} (f : ε → ε') (a : α) (k : α → Except ε' β) :
    (Except.mapError f (.ok a) >>= k) = k a :=
  rfl

/-- A successful bind in a state over `Except` runs its first part to a success, then the rest. -/
theorem stateT_bind_eq_ok {ε σ α β : Type} {m : StateT σ (Except ε) α}
    {g : α → StateT σ (Except ε) β} {s : σ} {r : β × σ}
    (h : (m >>= g) s = .ok r) : ∃ a : α × σ, m s = .ok a ∧ g a.1 a.2 = .ok r := by
  change (m s >>= fun p => g p.1 p.2) = .ok r at h
  cases hm : m s with
  | error e => rw [hm] at h; cases h
  | ok a => rw [hm] at h; exact ⟨a, rfl, h⟩

/-- A successful map in a state over `Except` ends with the state of the run it maps. -/
theorem stateT_map_eq_ok {ε σ α β : Type} {g : α → β} {x : StateT σ (Except ε) α} {s : σ}
    {r : β × σ} (h : (g <$> x) s = .ok r) : ∃ r' : α × σ, x s = .ok r' ∧ r.2 = r'.2 := by
  simp only [Functor.map, StateT.map, bind, Except.bind] at h
  cases hx : x s with
  | error e => rw [hx] at h; cases h
  | ok r' =>
    rw [hx] at h
    cases h
    exact ⟨r', rfl, rfl⟩

/-- A step that fails below a bound succeeds exactly at or above it, with its value. -/
theorem ite_lt_eq_ok_iff {ε α : Type} {a bound : Nat} {e : ε} {x out : α} :
    (if a < bound then Except.error e else .ok x) = .ok out ↔ bound ≤ a ∧ out = x := by
  by_cases below : a < bound
  · simp only [below, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    omega
  · simp only [below, ↓reduceIte, Except.ok.injEq]
    exact ⟨fun h => ⟨by omega, h.symm⟩, fun h => h.2.symm⟩

/-- A step that fails below a bound fails exactly there, with its error. -/
theorem ite_lt_eq_error_iff {ε α : Type} {a bound : Nat} {e other : ε} {x : α} :
    (if a < bound then Except.error e else .ok x) = .error other ↔ a < bound ∧ other = e := by
  by_cases below : a < bound
  · simp only [below, ↓reduceIte, Except.error.injEq, true_and]
    exact eq_comm
  · simp [below]

end EthLib.Base
