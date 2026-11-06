module

public import EthLib.Networking.Gossip.Validation

/-!
# Proofs: gossip validation outcomes

A chain of checks accepts exactly when every check in it accepts.

So an accepted message meets each condition that the chain states.
-/

@[expose] public section

namespace EthLib.Networking.Gossip

namespace ValidationResult

@[simp] theorem accept_andThen (next : Unit → ValidationResult) :
    accept.andThen next = next () := rfl

/-- Two checks in a row accept exactly when both accept. -/
theorem andThen_eq_accept {first : ValidationResult} {next : Unit → ValidationResult} :
    first.andThen next = accept ↔ first = accept ∧ next () = accept := by
  cases first <;> simp [andThen]

/-- A check that does not accept decides the outcome of the chain. -/
theorem andThen_of_ne_accept {first : ValidationResult} (h : first ≠ accept)
    (next : Unit → ValidationResult) : first.andThen next = first := by
  cases first
  · exact absurd rfl h
  all_goals rfl

@[simp] theorem accept_andThenM {m : Type → Type} [Monad m] (next : Unit → m ValidationResult) :
    accept.andThenM next = next () := rfl

/-- A check that does not accept decides the outcome of a chain that may fail. -/
theorem andThenM_of_ne_accept {m : Type → Type} [Monad m] {first : ValidationResult}
    (h : first ≠ accept) (next : Unit → m ValidationResult) :
    first.andThenM next = pure first := by
  cases first
  · exact absurd rfl h
  all_goals rfl

end ValidationResult

/-- An ignore check accepts exactly when its condition holds. -/
@[simp] theorem ignoreUnless_eq_accept {condition : Bool} {reason : String} :
    ignoreUnless condition reason = .accept ↔ condition = true := by
  cases condition <;> simp [ignoreUnless]

/-- A reject check accepts exactly when its condition holds. -/
@[simp] theorem rejectUnless_eq_accept {condition : Bool} {reason : String} :
    rejectUnless condition reason = .accept ↔ condition = true := by
  cases condition <;> simp [rejectUnless]

/-- A reject check never ignores. -/
@[simp] theorem rejectUnless_ne_ignore {condition : Bool} {reason other : String} :
    rejectUnless condition reason ≠ .ignore other := by
  cases condition <;> simp [rejectUnless]

/-- An ignore check runs the next checks when its condition holds, and else ignores. -/
@[simp] theorem ignoreUnless_andThen {condition : Bool} {reason : String}
    {next : Unit → ValidationResult} :
    (ignoreUnless condition reason).andThen next =
      if condition then next () else .ignore reason := by
  cases condition <;> rfl

/-- A reject check runs the next checks when its condition holds, and else rejects. -/
@[simp] theorem rejectUnless_andThen {condition : Bool} {reason : String}
    {next : Unit → ValidationResult} :
    (rejectUnless condition reason).andThen next =
      if condition then next () else .reject reason := by
  cases condition <;> rfl

/-- An ignore check runs the next checks, which may fail, when its condition holds. -/
@[simp] theorem ignoreUnless_andThenM {m : Type → Type} [Monad m] {condition : Bool}
    {reason : String} {next : Unit → m ValidationResult} :
    (ignoreUnless condition reason).andThenM next =
      if condition then next () else pure (.ignore reason) := by
  cases condition <;> rfl

/-- A reject check runs the next checks, which may fail, when its condition holds. -/
@[simp] theorem rejectUnless_andThenM {m : Type → Type} [Monad m] {condition : Bool}
    {reason : String} {next : Unit → m ValidationResult} :
    (rejectUnless condition reason).andThenM next =
      if condition then next () else pure (.reject reason) := by
  cases condition <;> rfl

end EthLib.Networking.Gossip
