module

public import Init

/-!
# `Base.Proofs.ExceptRel`

A relation on values, lifted to two computations that can fail.

The two are related when both fail with the same error, or both succeed with related values.

A map, a change of the error and a sequence of two steps keep the lifted relation.

Proofs that run the same step on two related inputs use it to compare the two runs.
-/

@[expose] public section

namespace EthLib.Base

/-- Two results are related when both fail with the same error, or succeed with related values. -/
def ExceptRel {ε α β : Type} (r : α → β → Prop) : Except ε α → Except ε β → Prop
  | .error e, .error e' => e = e'
  | .ok a, .ok b => r a b
  | _, _ => False

namespace ExceptRel

variable {ε δ α β γ γ' : Type} {r : α → β → Prop}

/-- Two successes are related exactly when their values are. -/
@[simp] theorem ok_ok {a : α} {b : β} : ExceptRel (ε := ε) r (.ok a) (.ok b) ↔ r a b :=
  Iff.rfl

/-- Two failures are related exactly when their errors are equal. -/
@[simp] theorem error_error {e e' : ε} :
    ExceptRel r (.error e : Except ε α) (.error e' : Except ε β) ↔ e = e' :=
  Iff.rfl

/-- A failure is never related to a success. -/
@[simp] theorem error_ok {e : ε} {b : β} : ¬ ExceptRel r (.error e : Except ε α) (.ok b) :=
  id

/-- A success is never related to a failure. -/
@[simp] theorem ok_error {a : α} {e : ε} : ¬ ExceptRel r (.ok a) (.error e : Except ε β) :=
  id

/-- Changing the errors of two related results by one function keeps them related. -/
theorem mapError {x : Except ε α} {y : Except ε β} (f : ε → δ) (h : ExceptRel r x y) :
    ExceptRel r (x.mapError f) (y.mapError f) := by
  cases x <;> cases y <;> simp_all [ExceptRel, Except.mapError]

/-- Mapping two related results by functions that keep the relation keeps them related. -/
theorem map {s : γ → γ' → Prop} {f : α → γ} {g : β → γ'} {x : Except ε α} {y : Except ε β}
    (h : ExceptRel r x y) (hf : ∀ {a b}, r a b → s (f a) (g b)) :
    ExceptRel s (f <$> x) (g <$> y) := by
  cases x <;> cases y <;> simp_all [ExceptRel, Functor.map, Except.map]

/-- Chaining two related results with steps that keep the relation keeps it.

Each step needs the relation only on the values that the first results hold. -/
theorem bind {s : γ → γ' → Prop} {x : Except ε α} {y : Except ε β}
    {k : α → Except ε γ} {k' : β → Except ε γ'} (h : ExceptRel r x y)
    (hk : ∀ {a b}, r a b → x = .ok a → y = .ok b → ExceptRel s (k a) (k' b)) :
    ExceptRel s (x >>= k) (y >>= k') := by
  cases x with
  | error _ =>
    cases y with
    | error _ => simpa [ExceptRel, Bind.bind, Except.bind] using h
    | ok _ => exact absurd h id
  | ok a =>
    cases y with
    | error _ => exact absurd h id
    | ok b => exact hk h rfl rfl

end ExceptRel

end EthLib.Base
