module

public import EthLib.Consensus.BuilderApi

/-!
# `Consensus.BuilderApi.Registration`

From Bellatrix to Fulu, a validator registers its fee recipient and gas limit with each builder.

A builder keeps a registration only when five rules hold, in the order of the source.

The key must be that of a validator of the state.

That validator must be active or pending in the current epoch.

The time of the registration must be at most ten seconds ahead of the builder's clock.

The source adds those ten seconds as a 64-bit integer, which fails on a clock near its limit.

The time must not be earlier than the registration that the builder keeps for the key.

The signature must verify.

The source keeps only the message of a registration, and EthLib keeps it with its signature.

The [Relay API] serves the signed registration of each upcoming proposer, so a relay needs both.

The [builder specification] gives the rules, and [`validators.yaml`] the 200 and 400 responses.

The rules hold at any fork, and the exports take them from Bellatrix to Fulu only.

[builder specification]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/builder.md#process_registration
[`validators.yaml`]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/apis/builder/validators.yaml
[Relay API]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/types/responses.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- How far ahead of the builder's clock a registration may be, in seconds. -/
def MAX_REGISTRATION_LOOKAHEAD : UInt64 := 10

/-- Whether a validator is pending in an epoch: its activation comes later.

It reads only the activation epoch, not the queue of pending deposits. -/
def isPendingForRegistration (validator : Validator) (epoch : Epoch) : Bool :=
  epoch < validator.activationEpoch

/-- Whether a validator may register: active or pending in the current epoch of the state. -/
def isEligibleForRegistration (state : BeaconState preset fork) (validator : Validator) : Bool :=
  let epoch := getCurrentEpoch state
  isActiveValidator validator epoch || isPendingForRegistration validator epoch

/-- Why a builder refuses a registration. -/
inductive RegistrationError where
  /-- No validator of the state has the key. -/
  | unknownValidator
  /-- The validator is neither active nor pending in the current epoch. -/
  | notEligible
  /-- The builder's clock plus the lookahead does not fit in 64 bits. -/
  | clockOverflow
  /-- The time of the registration is too far ahead of the builder's clock. -/
  | tooFarInFuture
  /-- The time of the registration is earlier than that of the one the builder keeps. -/
  | olderThanPrevious
  /-- The signature does not verify. -/
  | badSignature
  /-- The signing root cannot be computed. -/
  | root (fault : Err)
  deriving DecidableEq, Repr

/-- The signed registrations that a builder keeps, one for each key.

The source keeps only the message, and the registry keeps the signature with it. -/
structure Registry where
  /-- The signed registrations; the first one for a key is the one the builder keeps. -/
  entries : List SignedValidatorRegistrationV1 := []

namespace Registry

/-- The signed registration that the builder keeps for a key, if any. -/
def find? (registry : Registry) (pubkey : BLSPubkey) : Option SignedValidatorRegistrationV1 :=
  registry.entries.find? (·.message.pubkey = pubkey)

/-- The registry that keeps a signed registration in place of the one for the same key. -/
def insert (registry : Registry) (signed : SignedValidatorRegistrationV1) : Registry :=
  ⟨signed :: registry.entries.filter (·.message.pubkey ≠ signed.message.pubkey)⟩

end Registry

/-- The validator of the state with a key, the first one when several share it. -/
def validatorOfPubkey? (state : BeaconState preset fork) (pubkey : BLSPubkey) : Option Validator :=
  state.validators.data.toList.find? (·.pubkey = pubkey)

/-- Whether a builder keeps a signed registration, checked at a time of its clock in seconds.

The rules run in the order of the source, so the first that fails names the error.

The clock plus the lookahead must fit in 64 bits, as the integers of the source do. -/
def processRegistration (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (registry : Registry)
    (signed : SignedValidatorRegistrationV1) (now : UInt64) : Except RegistrationError Unit := do
  let registration := signed.message
  let some validator := validatorOfPubkey? state registration.pubkey
    | throw .unknownValidator
  unless isEligibleForRegistration state validator do throw .notEligible
  unless now.toNat + MAX_REGISTRATION_LOOKAHEAD.toNat < 2 ^ 64 do throw .clockOverflow
  unless registration.timestamp.toNat ≤ now.toNat + MAX_REGISTRATION_LOOKAHEAD.toNat do
    throw .tooFarInFuture
  if let some previous := registry.find? registration.pubkey then
    unless previous.message.timestamp ≤ registration.timestamp do throw .olderThanPrevious
  match verifyRegistrationSignature config checks signed with
  | .error fault => throw (.root fault)
  | .ok false => throw .badSignature
  | .ok true => pure ()

/-- The status of a request that registers one validator: 200 when kept, 400 otherwise. -/
def registerValidatorStatus (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (registry : Registry)
    (signed : SignedValidatorRegistrationV1) (now : UInt64) : Nat :=
  match processRegistration config checks state registry signed now with
  | .ok () => 200
  | .error _ => 400

end EthLib.Consensus.BuilderApi
