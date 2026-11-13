module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.BeaconApi.Validators

/-!
# `Consensus.BeaconApi.Registries`

The answers of the Beacon API that read the registries of validators and of builders of a state.

The [validators], [balances] and [identities] endpoints give one entry per named validator.

A request names validators by index or by public key, and an empty list names them all.

An identifier that names no validator gives no entry and no error.

The validators endpoint also keeps only the validators whose status passes a filter.

The source gives no order, so an answer is any permutation of the entries.

The [validator] endpoint gives the entry of one validator, and code 404 when there is none.

From Gloas, the [builders] endpoint gives the builders alike, with a filter on their status.

It gives code 400 for a state before Gloas.

The flags `execution_optimistic` and `finalized` come from the store, not from the state.

SOUNDNESS.md records the points that the source leaves open.

[validators]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/validators.yaml
[validator]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/validator.yaml
[balances]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/validator_balances.yaml
[identities]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/validator_identities.yaml
[builders]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states/builders.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-! ## Selection -/

/-- The indices that a list of identifiers names in a registry of a given size, once each.

An empty list names every index of the registry that fits in 64 bits. -/
def selectIndices (size : Nat) (resolve : ValidatorId → Option UInt64)
    (ids : List ValidatorId) : List UInt64 :=
  if ids.isEmpty then
    (List.range (min size UInt64.size)).map UInt64.ofNat
  else
    ((ids.filterMap resolve).eraseDups).mergeSort fun a b => a.toNat ≤ b.toNat

/-- The indices that a list of identifiers names in the registry of validators, once each. -/
def selectValidators (state : BeaconState preset fork) (ids : List ValidatorId) :
    List ValidatorIndex :=
  selectIndices state.validators.data.size (resolveValidatorId state) ids

/-- A name in a status filter: one status, or a group of statuses. -/
inductive StatusName where
  /-- One status. -/
  | status (status : ValidatorStatus)
  /-- Every status of a group. -/
  | group (group : CoarseStatus)
  deriving DecidableEq, Repr

namespace StatusName

/-- Whether a name covers a status: the status itself, or its group. -/
def covers : StatusName → ValidatorStatus → Bool
  | .status named, actual => named == actual
  | .group named, actual => actual.coarse == named

/-- The name that a text gives, as the API writes it, or an error with code 400. -/
def parse (text : String) : Except ErrorMessage StatusName :=
  let statuses := [ValidatorStatus.pendingInitialized, .pendingQueued, .activeOngoing,
    .activeExiting, .activeSlashed, .exitedUnslashed, .exitedSlashed, .withdrawalPossible,
    .withdrawalDone]
  let groups := [CoarseStatus.pending, .active, .exited, .withdrawal]
  match statuses.find? (·.name == text), groups.find? (·.name == text) with
  | some found, _ => .ok (.status found)
  | none, some found => .ok (.group found)
  | none, none => .error { code := 400, message := s!"Invalid validator status: {text}" }

end StatusName

/-- A filter on the status of a validator: a list of names of statuses or of groups. -/
abbrev StatusFilter := List StatusName

/-- Whether a status passes a filter: the filter is empty, or one of its names covers it. -/
def StatusFilter.passes (filter : StatusFilter) (status : ValidatorStatus) : Bool :=
  filter.isEmpty || filter.any (·.covers status)

/-! ## Entries -/

/-- An entry of the validators answer: the index, balance, status and record of a validator. -/
structure ValidatorResponse where
  /-- The index in the registry. -/
  index : ValidatorIndex
  /-- The balance. -/
  balance : Gwei
  /-- The status at the current epoch of the state. -/
  status : ValidatorStatus
  /-- The record of the validator. -/
  validator : Validator
  deriving DecidableEq, Repr

/-- An entry of the balances answer: the index and balance of a validator. -/
structure ValidatorBalanceResponse where
  /-- The index in the registry. -/
  index : ValidatorIndex
  /-- The balance. -/
  balance : Gwei
  deriving DecidableEq, Repr

instance : SszType ValidatorBalanceResponse :=
  .container ["index", "balance"] (fun r => (r.index, r.balance))
    (fun (index, balance) => ⟨index, balance⟩)

instance : ApiSpelling ValidatorBalanceResponse := .unmarked

/-- An entry of the identities answer: the index, key and activation epoch of a validator. -/
structure ValidatorIdentityResponse where
  /-- The index in the registry. -/
  index : ValidatorIndex
  /-- The public key. -/
  pubkey : BLSPubkey
  /-- The epoch of activation, or the far future epoch before it is set. -/
  activationEpoch : Epoch
  deriving DecidableEq, Repr

instance : SszType ValidatorIdentityResponse :=
  .container ["index", "pubkey", "activation_epoch"]
    (fun r => (r.index, r.pubkey, r.activationEpoch))
    (fun (index, pubkey, activationEpoch) => ⟨index, pubkey, activationEpoch⟩)

instance : ApiSpelling ValidatorIdentityResponse := .unmarked

/-- The JSON of an entry of the validators answer, with the status as the API names it. -/
def ValidatorResponse.toJson (entry : ValidatorResponse) : Except Err Json := do
  return Json.mkObj [("index", .str (toString entry.index.toNat)),
    ("balance", .str (toString entry.balance.toNat)), ("status", .str entry.status.name),
    ("validator", ← toApiJson entry.validator)]

/-! ## Answers -/

/-- The entries of the validators answer.

Each status is taken at the current epoch of the state.

An index with no balance in the state gives no entry. -/
def stateValidators (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : StatusFilter) : List ValidatorResponse :=
  (selectValidators state ids).filterMap fun index => do
    let validator ← state.validators.data[index.toNat]?
    let balance ← state.balances.data[index.toNat]?
    let status := validatorStatus validator balance (getCurrentEpoch state)
    if filter.passes status then some { index, balance, status, validator } else none

/-- Whether a list is an answer of the validators endpoint: the entries in any order. -/
def IsValidatorsAnswer (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : StatusFilter) (answer : List ValidatorResponse) : Prop :=
  answer.Perm (stateValidators state ids filter)

/-- The entries of the balances answer.

An index with no balance in the state gives no entry. -/
def stateBalances (state : BeaconState preset fork) (ids : List ValidatorId) :
    List ValidatorBalanceResponse :=
  (selectValidators state ids).filterMap fun index =>
    (state.balances.data[index.toNat]?).map fun balance => { index, balance }

/-- Whether a list is an answer of the balances endpoint: the entries in any order. -/
def IsBalancesAnswer (state : BeaconState preset fork) (ids : List ValidatorId)
    (answer : List ValidatorBalanceResponse) : Prop :=
  answer.Perm (stateBalances state ids)

/-- The entries of the identities answer. -/
def stateIdentities (state : BeaconState preset fork) (ids : List ValidatorId) :
    List ValidatorIdentityResponse :=
  (selectValidators state ids).filterMap fun index =>
    (state.validators.data[index.toNat]?).map fun validator =>
      { index, pubkey := validator.pubkey, activationEpoch := validator.activationEpoch }

/-- Whether a list is an answer of the identities endpoint: the entries in any order. -/
def IsIdentitiesAnswer (state : BeaconState preset fork) (ids : List ValidatorId)
    (answer : List ValidatorIdentityResponse) : Prop :=
  answer.Perm (stateIdentities state ids)

/-- The entry of the endpoint for one validator, or the error with code 404 for none.

An identifier that names no validator, or an index with no balance, gives that error. -/
def stateValidator (state : BeaconState preset fork) (id : ValidatorId) :
    Except ErrorMessage ValidatorResponse :=
  match stateValidators state [id] [] with
  | entry :: _ => .ok entry
  | [] => .error { code := 404, message := "Validator not found" }

/-! ## Requests -/

/-- The most identifiers that a request in a query string may carry. -/
def MAX_QUERY_IDS : Nat := 64

/-- The identifiers of a request, or an error with code 400 for a text that is no identifier.

A request in a query string with more than 64 identifiers gives the error with code 414.

A body may carry any number. -/
def readValidatorIds (inQuery : Bool) (texts : List String) :
    Except ErrorMessage (List ValidatorId) :=
  if inQuery && texts.length > MAX_QUERY_IDS then
    .error { code := 414, message := "Too many validator IDs in request" }
  else texts.mapM parseValidatorId

/-- The status filter of a request, or an error with code 400 for a text that is no name. -/
def readStatusFilter (texts : List String) : Except ErrorMessage StatusFilter :=
  texts.mapM StatusName.parse

/-- The builder identifiers of a request, or an error with code 400 for a text that is none.

A builder is named as a validator is, and the request is a body, with any number of identifiers. -/
def readBuilderIds (texts : List String) : Except ErrorMessage (List ValidatorId) :=
  texts.mapM fun text => (parseValidatorId text).mapError fun _ => invalidId "builder" text

/-! ## Responses -/

/-- The response of the validators endpoint, without the two flags that come from the store. -/
def validatorsResponse (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : StatusFilter) : Except ErrorMessage ApiEnvelope := do
  let entries ← (stateValidators state ids filter).mapM fun entry =>
    entry.toJson.mapError fun fault => internalError (reprStr fault)
  return { data := .arr entries.toArray }

/-- The response of the balances endpoint, without the two flags that come from the store. -/
def balancesResponse (state : BeaconState preset fork) (ids : List ValidatorId) :
    Except ErrorMessage ApiEnvelope := do
  return { data := .arr (← (stateBalances state ids).mapM apiJsonOr500).toArray }

/-- The SSZ body of the balances answer: a list bounded by the registry limit.

A longer answer gives the error with code 500. -/
def balancesSsz (state : BeaconState preset fork) (ids : List ValidatorId) :
    Except ErrorMessage ByteArray :=
  let entries := (stateBalances state ids).toArray
  if bound : entries.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat then
    apiSszOr500 (SszList.mk entries bound)
  else .error (internalError "more balances than the registry limit")

/-- The response of the identities endpoint, without the two flags that come from the store.

The source gives no list type for its SSZ body, so there is none here. -/
def identitiesResponse (state : BeaconState preset fork) (ids : List ValidatorId) :
    Except ErrorMessage ApiEnvelope := do
  return { data := .arr (← (stateIdentities state ids).mapM apiJsonOr500).toArray }

/-! ## Builders -/

/-- From Gloas: the index of the builder that an identifier names in a state, or none.

A builder is named as a validator is: by its index, or by its public key.

An index names a builder when it is below the size of the registry.

A public key names the first builder of the registry that holds it. -/
def resolveBuilderId (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    ValidatorId → Option BuilderIndex
  | .index index => if index.toNat < (state.builders gloas).data.size then some index else none
  | .pubkey pubkey => ((state.builders gloas).data.findIdx? (·.pubkey == pubkey)).map UInt64.ofNat

/-- The builder status that a text gives, as the API writes it, or an error with code 400. -/
def BuilderStatus.parse (text : String) : Except ErrorMessage BuilderStatus :=
  match [BuilderStatus.pending, .active, .exited].find? (·.name == text) with
  | some found => .ok found
  | none => .error { code := 400, message := s!"Invalid builder status: {text}" }

/-- Whether a builder status passes a filter: the filter is empty, or it holds the status. -/
def builderStatusPasses (filter : List BuilderStatus) (status : BuilderStatus) : Bool :=
  filter.isEmpty || filter.contains status

/-- An entry of the builders answer: the index, status and record of a builder. -/
structure BuilderResponse where
  /-- The index in the registry of builders. -/
  index : BuilderIndex
  /-- The status of the builder. -/
  status : BuilderStatus
  /-- The record of the builder. -/
  builder : Builder
  deriving DecidableEq, Repr

/-- The JSON of an entry of the builders answer, with the status as the API names it. -/
def BuilderResponse.toJson (entry : BuilderResponse) : Except Err Json := do
  return Json.mkObj [("index", .str (toString entry.index.toNat)),
    ("status", .str entry.status.name), ("builder", ← toApiJson entry.builder)]

/-- From Gloas: the entries of the builders answer, for the requested builders.

Each builder whose status does not pass the filter gives no entry. -/
def stateBuilders (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (ids : List ValidatorId) (filter : List BuilderStatus) : List BuilderResponse :=
  (selectIndices (state.builders gloas).data.size (resolveBuilderId state gloas) ids).filterMap
    fun index => do
      let builder ← (state.builders gloas).data[index.toNat]?
      let status ← (builderStatus state gloas index).toOption
      if builderStatusPasses filter status then some { index, status, builder } else none

/-- Whether a list is an answer of the builders endpoint: the entries in any order. -/
def IsBuildersAnswer (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (ids : List ValidatorId) (filter : List BuilderStatus) (answer : List BuilderResponse) :
    Prop :=
  answer.Perm (stateBuilders state gloas ids filter)

/-- The response of the builders endpoint, without the two flags that come from the store.

A state before Gloas gives the error with code 400. -/
def buildersResponse (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : List BuilderStatus) : Except ErrorMessage ApiEnvelope := do
  if gloas : .glamsterdam ≤ fork then
    let entries ← (stateBuilders state gloas ids filter).mapM fun entry =>
      entry.toJson.mapError fun fault => internalError (reprStr fault)
    return { data := .arr entries.toArray }
  else .error (beforeFork "builders" .glamsterdam)

end EthLib.Consensus.BeaconApi
