module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.BuilderApi.AuthData
public import EthLib.Consensus.BuilderApi.Encoding

/-!
# `Consensus.BuilderApi.RequestAuth`

From Gloas, a proposer authenticates its requests to a builder, which keeps its preferences.

The [builder specification] gives the rules for [preferences] and for [bid requests].

Its [validator document] gives the authentication data.

[builder specification]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/specs/gloas/builder.md
[preferences]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/specs/gloas/builder.md#builder-preferences
[bid requests]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/specs/gloas/builder.md#per-request-validator-inputs
[validator document]: https://github.com/ethereum/builder-specs/blob/0911550c65b1e4a326fe7fbd7d0ca52ff0b6a4b7/specs/gloas/validator.md#constructing-the-builderrequestauth
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

/-- A check of a request to a builder that fails. -/
inductive AuthFailure where
  /-- The version header is absent, or does not name the Gloas version of the body. -/
  | badVersion
  /-- The data of the authentication is empty. -/
  | emptyData
  /-- The data is not the data agreed with the builder. -/
  | dataMismatch
  /-- The slot of the authentication is not the slot of the path. -/
  | slotMismatch
  /-- The slot of the authentication is before the builder's current slot. -/
  | slotPassed
  /-- The builder knows another proposer for the slot, as from the lookahead of its state.

  The source makes this check a SHOULD, so a builder that skips it still conforms. -/
  | notProposer
  /-- The signature does not verify against the key of the path. -/
  | badSignature
  deriving DecidableEq, Repr

/-- The status that a failed check gives: 401 for the signature, and 400 for any other. -/
def AuthFailure.status : AuthFailure → Nat
  -- A signature that fails to verify gets 401.
  | .badSignature => 401
  -- Every other failed check gets 400.
  | _ => 400

/-- The failures of the version header, which must name the fork of the body's type.

The authentication and the preferences exist from Gloas only, so the header must be `gloas`. -/
def headerFailures (versionHeader : Option String) : List AuthFailure :=
  -- The source gives 400 for a header that is absent or names a fork it does not recognize.
  --
  -- EthLib also refuses any fork but Gloas, the fork of the body's type.
  if versionHeader = some ConsensusVersion.gloas.name then [] else [.badVersion]

/-- The data that a proposer and a builder agree: the data agreed out of band, if any.

Otherwise it is the default data from the builder's URL. -/
def agreedData (outOfBand : Option ByteArray) (builderUrl : String) :
    Except AuthDataError ByteArray :=
  match outOfBand with
  -- The data agreed with the builder out of band, when there is some.
  | some data => .ok data
  -- Else the default data from the builder's URL, which the validator should use.
  | none => defaultAuthData builderUrl

/-- The failures of the data of an authentication, against the data agreed with the builder.

Empty data fails, even when the agreed data is empty too. -/
def dataFailures (agreed : ByteArray) (auth : BuilderRequestAuth) : List AuthFailure :=
  -- A zero-length data is invalid.
  (if auth.data.data.isEmpty then [.emptyData] else []) ++
    -- The data matches the value agreed with the proposer.
    (if auth.data.data = agreed.data then [] else [.dataMismatch])

/-- The failures of the signature of an authentication, against the key of the path. -/
def signatureFailures (config : Config) (checks : SignatureChecks) (pubkey : BLSPubkey)
    (auth : SignedBuilderRequestAuth) : Except Err (List AuthFailure) := do
  -- The signature verifies against the key of the path.
  return if ← verifyBuilderRequestAuthSignature config checks auth pubkey then [] else
    [.badSignature]

/-- From Gloas: every check that fails on the authentication of a request for a bid.

The agreed data is the data agreed out of band, or by default the data from the builder's URL. -/
def authFailures (config : Config) (checks : SignatureChecks) (agreed : ByteArray)
    (pathSlot : Slot) (pubkey : BLSPubkey) (versionHeader : Option String)
    (auth : SignedBuilderRequestAuth) : Except Err (List AuthFailure) := do
  -- The source also refuses a malformed body and a request without its timing headers.
  --
  -- Those rules are outside these checks.
  let signature ← signatureFailures config checks pubkey auth
  -- The version header, then the data.
  return headerFailures versionHeader ++ dataFailures agreed auth.message ++
    -- The slot of the authentication matches the slot of the path.
    (if auth.message.slot = pathSlot then [] else [.slotMismatch]) ++ signature

/-- From Gloas: the key of the proposer of a slot, by the lookahead of the builder's state.

A slot outside the current and next epoch of the state has none.

Neither has a slot whose proposer is not in the registry, which a valid state never holds. -/
def lookaheadProposerKey {preset : Preset} {fork : Fork} (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (slot : Slot) : Option BLSPubkey :=
  lookaheadSchedule state (Nat.le_trans (by decide) gloas) slot >>= validatorPubkey? state

/-- From Gloas: every check that fails on a request that submits preferences.

The builder knows the key of the proposer of some slots, and none of the others.

A builder that skips the check of the proposer knows none. -/
def preferencesFailures (config : Config) (checks : SignatureChecks) (agreed : ByteArray)
    (currentSlot : Slot) (proposerOf : Slot → Option BLSPubkey) (pubkey : BLSPubkey)
    (versionHeader : Option String) (request : BuilderPreferencesRequest) :
    Except Err (List AuthFailure) := do
  let slot := request.auth.message.slot
  let signature ← signatureFailures config checks pubkey request.auth
  -- The version header, then the data.
  return headerFailures versionHeader ++ dataFailures agreed request.auth.message ++
    -- The slot of the authentication has not already passed.
    --
    -- The source defines a passed slot no more precisely, and EthLib takes one before the current.
    (if slot < currentSlot then [.slotPassed] else []) ++
    -- The builder knows no other proposer for the slot.
    (if (proposerOf slot).all (· = pubkey) then [] else [.notProposer]) ++ signature

/-- Whether a status may answer a request whose checks of the authentication fail as listed.

When some check fails, the status is that of a failure in the list.

The source does not say which status wins when a 400 check and the signature both fail.

When no check fails, the other rules of the source decide the status, so any is allowed here. -/
def AllowedStatus (failures : List AuthFailure) (status : Nat) : Prop :=
  failures ≠ [] → ∃ failure ∈ failures, failure.status = status

instance (failures : List AuthFailure) (status : Nat) :
    Decidable (AllowedStatus failures status) := by
  unfold AllowedStatus; infer_instance

/-- The preferences that a builder should keep, by the key of the proposer and the slot.

The first preferences accepted for a key and slot stay, and later ones are ignored. -/
structure PreferencesStore where
  /-- The entries, the latest first. -/
  entries : List ((BLSPubkey × Slot) × BuilderPreferences) := []

namespace PreferencesStore

/-- The preferences kept for a proposer at a slot, if any. -/
def get (store : PreferencesStore) (pubkey : BLSPubkey) (slot : Slot) :
    Option BuilderPreferences :=
  store.entries.lookup (pubkey, slot)

/-- The store with preferences kept under a key and a slot, ahead of every earlier entry. -/
def keep (store : PreferencesStore) (pubkey : BLSPubkey) (slot : Slot)
    (preferences : BuilderPreferences) : PreferencesStore :=
  -- The newest entry first.
  --
  -- A submission keeps preferences only for a key and slot with none, so nothing is hidden.
  ⟨((pubkey, slot), preferences) :: store.entries⟩

/-- From Gloas: the store after a request that submits preferences under the key of its path. -/
def submit (store : PreferencesStore) (config : Config) (checks : SignatureChecks)
    (agreed : ByteArray) (currentSlot : Slot) (proposerOf : Slot → Option BLSPubkey)
    (pubkey : BLSPubkey) (versionHeader : Option String) (request : BuilderPreferencesRequest) :
    Except Err PreferencesStore := do
  let slot := request.auth.message.slot
  let failures ←
    preferencesFailures config checks agreed currentSlot proposerOf pubkey versionHeader request
  -- When no check fails, the store keeps the preferences per proposer and per slot.
  --
  -- A submission for a key and slot already kept is ignored, and still answered with 202.
  return if failures = [] ∧ store.get pubkey slot = none then
    store.keep pubkey slot request.preferences
  -- Otherwise the store is unchanged.
  else store

end PreferencesStore

/-- From Gloas: whether a bid keeps within the preferences kept for its proposer at its slot. -/
def BidHonorsPreferences {preset : Preset} {fork : Fork} (store : PreferencesStore)
    (pubkey : BLSPubkey) (bid : ExecutionPayloadBid preset fork) : Prop :=
  -- A bid for a slot with stored preferences honors their cap on the execution payment.
  --
  -- Without them, the builder may serve a bid with any execution payment.
  ∀ preferences, store.get pubkey bid.slot = some preferences →
    bid.executionPayment ≤ preferences.maxExecutionPayment

end EthLib.Consensus.BuilderApi
