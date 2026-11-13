module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.BuilderApi.AuthData
public import EthLib.Consensus.BuilderApi.Encoding

/-!
# `Consensus.BuilderApi.RequestAuth`

From Gloas, a proposer authenticates its requests to a builder with a signed message.

The message holds data that the proposer agreed with the builder, and the slot of the proposal.

A builder checks the version header, the data, the slot and the signature of each request.

A failed signature gives 401, and every other failed check gives 400.

A request for a bid must name the slot of its path.

A request that submits preferences must not name a slot that has passed.

A builder should keep accepted preferences for each proposer and slot.

A bid that it serves for that slot keeps its execution payment within their cap.

These are the checks of the authentication.

The source also refuses a malformed body and a request without its timing headers, outside them.

The [builder specification] gives the rules for [preferences] and for [bid requests].

Its [validator document] gives the authentication data.

[builder specification]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md
[preferences]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md#builder-preferences
[bid requests]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/builder.md#per-request-validator-inputs
[validator document]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/validator.md#constructing-the-builderrequestauth
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
  /-- The signature does not verify against the key of the path. -/
  | badSignature
  deriving DecidableEq, Repr

/-- The status that a failed check gives: 401 for the signature, and 400 for any other. -/
def AuthFailure.status : AuthFailure → Nat
  | .badSignature => 401
  | _ => 400

/-- The failures of the version header, which must name the fork of the body's type.

The authentication and the preferences exist from Gloas only, so the header must be `gloas`. -/
def headerFailures (versionHeader : Option String) : List AuthFailure :=
  if versionHeader = some ConsensusVersion.gloas.name then [] else [.badVersion]

/-- The data that a proposer and a builder agree: the data agreed out of band, if any.

Otherwise it is the default data from the builder's URL. -/
def agreedData (outOfBand : Option ByteArray) (builderUrl : String) :
    Except AuthDataError ByteArray :=
  match outOfBand with
  | some data => .ok data
  | none => defaultAuthData builderUrl

/-- The failures of the data of an authentication, against the data agreed with the builder.

Empty data fails, even when the agreed data is empty too. -/
def dataFailures (agreed : ByteArray) (auth : BuilderRequestAuth) : List AuthFailure :=
  (if auth.data.data.isEmpty then [.emptyData] else []) ++
    (if auth.data.data = agreed.data then [] else [.dataMismatch])

/-- The failures of the signature of an authentication, against the key of the path. -/
def signatureFailures (config : Config) (checks : SignatureChecks) (pubkey : BLSPubkey)
    (auth : SignedBuilderRequestAuth) : Except Err (List AuthFailure) := do
  return if ← verifyBuilderRequestAuthSignature config checks auth pubkey then [] else
    [.badSignature]

/-- From Gloas: every check that fails on the authentication of a request for a bid.

The data must be the agreed data, and the slot must be the slot of the path.

The agreed data is the data agreed out of band, or by default the data from the builder's URL. -/
def authFailures (config : Config) (checks : SignatureChecks) (agreed : ByteArray)
    (pathSlot : Slot) (pubkey : BLSPubkey) (versionHeader : Option String)
    (auth : SignedBuilderRequestAuth) : Except Err (List AuthFailure) := do
  let signature ← signatureFailures config checks pubkey auth
  return headerFailures versionHeader ++ dataFailures agreed auth.message ++
    (if auth.message.slot = pathSlot then [] else [.slotMismatch]) ++ signature

/-- From Gloas: every check that fails on a request that submits preferences.

The slot of the authentication has passed when it is before the builder's current slot.

The source defines a passed slot no more precisely. -/
def preferencesFailures (config : Config) (checks : SignatureChecks) (agreed : ByteArray)
    (currentSlot : Slot) (pubkey : BLSPubkey) (versionHeader : Option String)
    (request : BuilderPreferencesRequest) : Except Err (List AuthFailure) := do
  let signature ← signatureFailures config checks pubkey request.auth
  return headerFailures versionHeader ++ dataFailures agreed request.auth.message ++
    (if request.auth.message.slot < currentSlot then [.slotPassed] else []) ++ signature

/-- Whether a status may answer a request whose checks of the authentication fail as listed.

When some check fails, the status is that of a failure in the list.

The source does not say which status wins when a 400 check and the signature both fail.

When no check fails, the other rules of the source decide the status, so any is allowed here. -/
def AllowedStatus (failures : List AuthFailure) (status : Nat) : Prop :=
  failures ≠ [] → ∃ failure ∈ failures, failure.status = status

instance (failures : List AuthFailure) (status : Nat) :
    Decidable (AllowedStatus failures status) := by
  unfold AllowedStatus; infer_instance

/-- The preferences that a builder keeps, by the key of the proposer and the slot.

A later entry for the same key and slot comes first, and hides the earlier one.

The source says that a builder should keep them, and does not say which of two submissions wins. -/
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
  ⟨((pubkey, slot), preferences) :: store.entries⟩

/-- From Gloas: the store after a request that submits preferences under the key of its path.

When no check of the request fails, it keeps the preferences under that key and the request's slot.

Otherwise it is unchanged. -/
def submit (store : PreferencesStore) (config : Config) (checks : SignatureChecks)
    (agreed : ByteArray) (currentSlot : Slot) (pubkey : BLSPubkey) (versionHeader : Option String)
    (request : BuilderPreferencesRequest) : Except Err PreferencesStore := do
  let failures ← preferencesFailures config checks agreed currentSlot pubkey versionHeader request
  return if failures = [] then
    store.keep pubkey request.auth.message.slot request.preferences
  else store

end PreferencesStore

/-- From Gloas: whether a bid keeps within the preferences kept for its proposer at its slot.

Without kept preferences, any execution payment is allowed. -/
def BidHonorsPreferences {preset : Preset} {fork : Fork} (store : PreferencesStore)
    (pubkey : BLSPubkey) (bid : ExecutionPayloadBid preset fork) : Prop :=
  ∀ preferences, store.get pubkey bid.slot = some preferences →
    bid.executionPayment ≤ preferences.maxExecutionPayment

end EthLib.Consensus.BuilderApi
