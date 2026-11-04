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

end ValidationResult

/-- An ignore check accepts exactly when its condition holds. -/
@[simp] theorem ignoreUnless_eq_accept {condition : Bool} {reason : String} :
    ignoreUnless condition reason = .accept ↔ condition = true := by
  cases condition <;> simp [ignoreUnless]

/-- A reject check accepts exactly when its condition holds. -/
@[simp] theorem rejectUnless_eq_accept {condition : Bool} {reason : String} :
    rejectUnless condition reason = .accept ↔ condition = true := by
  cases condition <;> simp [rejectUnless]

end EthLib.Networking.Gossip
