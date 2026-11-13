module

public import EthLib.Consensus.BuilderApi.Registration

/-!
# Proofs: a builder keeps a registration exactly when the five rules hold

A registration passes exactly when its key names a validator of the state that is eligible.

Its time must be at most ten seconds ahead, no older than the kept one, and signed.

The clock plus ten seconds must fit in 64 bits, as in the source.

So a kept registration carries a valid signature.

The time kept for a key never goes back.

A validator that has activated and exited is refused.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A registry finds the signed registration it has just kept for its key. -/
theorem Registry.find?_insert_self (registry : Registry) (signed : SignedValidatorRegistrationV1) :
    (registry.insert signed).find? signed.message.pubkey = some signed := by
  simp [Registry.insert, Registry.find?]

/-- A registration passes exactly when the five rules hold. -/
theorem processRegistration_ok_iff {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {registry : Registry}
    {signed : SignedValidatorRegistrationV1} {now : UInt64} :
    processRegistration config checks state registry signed now = .ok () ↔
      (∃ validator, validatorOfPubkey? state signed.message.pubkey = some validator ∧
        isEligibleForRegistration state validator = true) ∧
      now.toNat + MAX_REGISTRATION_LOOKAHEAD.toNat < 2 ^ 64 ∧
      signed.message.timestamp.toNat ≤ now.toNat + MAX_REGISTRATION_LOOKAHEAD.toNat ∧
      (∀ previous, registry.find? signed.message.pubkey = some previous →
        previous.message.timestamp ≤ signed.message.timestamp) ∧
      verifyRegistrationSignature config checks signed = .ok true := by
  unfold processRegistration
  cases hv : validatorOfPubkey? state signed.message.pubkey with
  | none => simp [hv]
  | some validator =>
    cases he : isEligibleForRegistration state validator <;>
    by_cases hc : now.toNat + MAX_REGISTRATION_LOOKAHEAD.toNat < 2 ^ 64 <;>
    by_cases ht : signed.message.timestamp.toNat ≤ now.toNat + MAX_REGISTRATION_LOOKAHEAD.toNat <;>
    cases hp : registry.find? signed.message.pubkey <;>
    (try rename_i previous; by_cases ho : previous.message.timestamp ≤ signed.message.timestamp) <;>
    cases hs : verifyRegistrationSignature config checks signed <;>
    (try rename_i b; cases b) <;>
    simp [*, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure]

/-- A registration that passes carries the signature of its key. -/
theorem processRegistration_signature {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {registry : Registry}
    {signed : SignedValidatorRegistrationV1} {now : UInt64}
    (kept : processRegistration config checks state registry signed now = .ok ()) :
    verifyRegistrationSignature config checks signed = .ok true :=
  (processRegistration_ok_iff.1 kept).2.2.2.2

/-- Once a registration passes and is kept, the time kept for its key has not gone back. -/
theorem processRegistration_monotone {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {registry : Registry}
    {signed : SignedValidatorRegistrationV1} {now : UInt64}
    (kept : processRegistration config checks state registry signed now = .ok ())
    {previous : SignedValidatorRegistrationV1}
    (before : registry.find? signed.message.pubkey = some previous) :
    (registry.insert signed).find? signed.message.pubkey = some signed ∧
      previous.message.timestamp ≤ signed.message.timestamp :=
  ⟨Registry.find?_insert_self _ _, (processRegistration_ok_iff.1 kept).2.2.2.1 previous before⟩

/-- A validator that has activated and exited by the current epoch is refused as not eligible. -/
theorem processRegistration_exited {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {registry : Registry}
    {signed : SignedValidatorRegistrationV1} {now : UInt64} {validator : Validator}
    (found : validatorOfPubkey? state signed.message.pubkey = some validator)
    (activated : validator.activationEpoch ≤ getCurrentEpoch state)
    (exited : validator.exitEpoch ≤ getCurrentEpoch state) :
    processRegistration config checks state registry signed now = .error .notEligible := by
  have refused : isEligibleForRegistration state validator = false := by
    simp only [isEligibleForRegistration, isActiveValidator, isPendingForRegistration,
      Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨Or.inr (UInt64.not_lt.2 exited), UInt64.not_lt.2 activated⟩
  simp [processRegistration, found, refused, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

end EthLib.Consensus.BuilderApi
