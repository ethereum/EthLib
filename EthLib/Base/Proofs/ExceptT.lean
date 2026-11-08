module

public import Init

/-!
# `Base.Proofs.ExceptT`

The identity monad with errors computes as the error monad itself.

Definitions that take a hash in any monad run in it when the hash is plain.

These facts let a proof read such a run as a plain computation with errors.
-/

@[expose] public section

namespace EthLib.Base

/-- A step in the identity monad with errors is a step with errors. -/
theorem exceptT_id_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (bind (m := ExceptT ε Id) x f) = x.bind f := by
  cases x <;> rfl

/-- A step with errors is the bind of errors. -/
theorem except_bind_eq {ε α β : Type} (x : Except ε α) (f : α → Except ε β) : x >>= f = x.bind f :=
  rfl

/-- A value in the identity monad with errors is a value with errors. -/
theorem exceptT_id_pure {ε α : Type} (a : α) :
    (pure (f := ExceptT ε Id) a) = Except.ok (ε := ε) a :=
  rfl

/-- Renaming the errors in the identity monad renames them in place. -/
theorem exceptT_id_adapt {ε ε' α : Type} (f : ε → ε') (x : Except ε α) :
    ExceptT.adapt (m := Id) f x = x.mapError f := by
  cases x <;> rfl

/-- A computation with errors, lifted into the identity monad with errors, is itself. -/
theorem exceptT_id_monadLift {ε α : Type} (x : Except ε α) :
    (liftM (n := ExceptT ε Id) x) = x := by
  cases x <;> rfl

/-- A plain value, lifted into the identity monad with errors, never fails. -/
theorem exceptT_id_lift {ε α : Type} (a : Id α) : ExceptT.lift (ε := ε) a = Except.ok a :=
  rfl

end EthLib.Base
