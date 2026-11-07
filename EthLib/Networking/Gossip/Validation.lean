module

/-!
# `Networking.Gossip.Validation`

The outcome of validating one gossip message.

Gossipsub v1.1 lets the application accept, reject or ignore each message.

Its section "Extended Validators" says so, in [libp2p/specs `98c5aa9`][gossipsub].

An accepted message is delivered and forwarded.

A rejected message is invalid, and its sender is penalized.

An ignored message is neither delivered nor forwarded, and its sender is not penalized.

Each consensus topic states its rules as conditions that ignore or reject a message.

A message that meets no such condition is accepted.

[gossipsub]: https://github.com/libp2p/specs/blob/98c5aa9421703fc31b0833ad8860a55db15be063/pubsub/gossipsub/gossipsub-v1.1.md#extended-validators
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The outcome of validating one gossip message, with the reason of an ignore or a reject. -/
inductive ValidationResult where
  /-- The message is valid: deliver it and forward it. -/
  | accept
  /-- Drop the message without a penalty, for the stated reason. -/
  | ignore (reason : String)
  /-- Drop the message as invalid, and penalize its sender, for the stated reason. -/
  | reject (reason : String)
  deriving DecidableEq, Repr, Inhabited

namespace ValidationResult

/-- Whether the message is delivered and forwarded. -/
def isAccept : ValidationResult → Bool
  | accept => true
  | _ => false

/-- Run the next checks only after an accepted outcome.

The first outcome that ignores or rejects is the result. -/
def andThen (first : ValidationResult) (next : Unit → ValidationResult) : ValidationResult :=
  match first with
  | accept => next ()
  | other => other

/-- Run the next checks, which may fail, only after an accepted outcome.

The first outcome that ignores or rejects is the result, and the next checks do not run. -/
def andThenM {m : Type → Type} [Monad m] (first : ValidationResult)
    (next : Unit → m ValidationResult) : m ValidationResult :=
  match first with
  | accept => next ()
  | other => pure other

end ValidationResult

/-- Ignore the message for the reason unless the condition holds. -/
def ignoreUnless (condition : Bool) (reason : String) : ValidationResult :=
  if condition then .accept else .ignore reason

/-- Reject the message for the reason unless the condition holds. -/
def rejectUnless (condition : Bool) (reason : String) : ValidationResult :=
  if condition then .accept else .reject reason

end EthLib.Networking.Gossip
