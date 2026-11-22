module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.BeaconApi.Validators

/-!
# `Consensus.BeaconApi.Registries`

The answers of the Beacon API that read the registries of validators and of builders of a state.

The [validators], [balances] and [identities] endpoints give one entry per named validator.

The [validator] endpoint gives the entry of one validator.

From Gloas, the [builders] endpoint gives the builders alike.

The source gives no order, so an answer is any permutation of the entries.

The flags `execution_optimistic` and `finalized` come from the store, not from the state.

SOUNDNESS.md records the points that the source leaves open.

[validators]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/validators.yaml
[validator]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/validator.yaml
[balances]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/validator_balances.yaml
[identities]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/validator_identities.yaml
[builders]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/builders.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-! ## Selection -/

/-- The indices that a list of identifiers names in a registry of a given size, once each. -/
def selectIndices (size : Nat) (resolve : ValidatorId → Option UInt64)
    (ids : List ValidatorId) : List UInt64 :=
  -- The source: an empty or omitted list names them all.
  --
  -- Here that is every index of the registry that fits in 64 bits.
  if ids.isEmpty then
    (List.range (min size UInt64.size)).map UInt64.ofNat
  else
    -- The source: an identifier that names nothing gives no entry, and no error.
    --
    -- Each named index once, also when an index and a key, or a repeated text, name it.
    --
    -- EthLib's choice: the schema marks the list unique, but gives no code for a repeat.
    --
    -- The indices in increasing order, EthLib's choice, since the source gives no order.
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
  -- A status covers itself.
  | .status named, actual => named == actual
  -- A group covers each status in it.
  | .group named, actual => actual.coarse == named

/-- The name that a text gives, as the API writes it, or an error with code 400. -/
def parse (text : String) : Except ErrorMessage StatusName :=
  -- The validators endpoint: one of the nine statuses of the schema, or one of the four groups.
  let statuses := [ValidatorStatus.pendingInitialized, .pendingQueued, .activeOngoing,
    .activeExiting, .activeSlashed, .exitedUnslashed, .exitedSlashed, .withdrawalPossible,
    .withdrawalDone]
  let groups := [CoarseStatus.pending, .active, .exited, .withdrawal]
  match statuses.find? (·.name == text), groups.find? (·.name == text) with
  | some found, _ => .ok (.status found)
  | none, some found => .ok (.group found)
  -- Else an invalid status: code 400, with EthLib's message.
  | none, none => .error { code := 400, message := s!"Invalid validator status: {text}" }

end StatusName

/-- A filter on the status of a validator: a list of names of statuses or of groups. -/
abbrev StatusFilter := List StatusName

/-- Whether a status passes a filter: the filter is empty, or one of its names covers it. -/
def StatusFilter.passes (filter : StatusFilter) (status : ValidatorStatus) : Bool :=
  -- The source: an empty or omitted list takes all statuses.
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

/-- The entries of the validators answer. -/
def stateValidators (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : StatusFilter) : List ValidatorResponse :=
  (selectValidators state ids).filterMap fun index => do
    let validator ← state.validators.data[index.toNat]?
    -- An index with no balance in the state gives no entry.
    let balance ← state.balances.data[index.toNat]?
    -- The status document writes each condition at the current epoch, read as that of the state.
    let status := validatorStatus validator balance (getCurrentEpoch state)
    -- The validators endpoint: only a validator whose status passes the filter.
    if filter.passes status then some { index, balance, status, validator } else none

/-- Whether a list is an answer of the validators endpoint: the entries in any order. -/
def IsValidatorsAnswer (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : StatusFilter) (answer : List ValidatorResponse) : Prop :=
  answer.Perm (stateValidators state ids filter)

/-- The entries of the balances answer. -/
def stateBalances (state : BeaconState preset fork) (ids : List ValidatorId) :
    List ValidatorBalanceResponse :=
  (selectValidators state ids).filterMap fun index =>
    -- The index and the balance; an index with no balance in the state gives no entry.
    (state.balances.data[index.toNat]?).map fun balance => { index, balance }

/-- Whether a list is an answer of the balances endpoint: the entries in any order. -/
def IsBalancesAnswer (state : BeaconState preset fork) (ids : List ValidatorId)
    (answer : List ValidatorBalanceResponse) : Prop :=
  answer.Perm (stateBalances state ids)

/-- The entries of the identities answer. -/
def stateIdentities (state : BeaconState preset fork) (ids : List ValidatorId) :
    List ValidatorIdentityResponse :=
  (selectValidators state ids).filterMap fun index =>
    -- The index, the public key and the activation epoch of the record.
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
  -- The entry that the validators answer gives the identifier, with no status filter.
  match stateValidators state [id] [] with
  | entry :: _ => .ok entry
  -- The validator endpoint: else code 404, with the example message of the source.
  | [] => .error { code := 404, message := "Validator not found" }

/-! ## Requests -/

/-- The most identifiers that a request in a query string may carry.

The schema of the source allows at most 64 identifiers in the query string. -/
def MAX_QUERY_IDS : Nat := 64

/-- The identifiers of a request, or an error with code 400 for a text that is no identifier. -/
def readValidatorIds (inQuery : Bool) (texts : List String) :
    Except ErrorMessage (List ValidatorId) :=
  -- The GET endpoints: more than 64 identifiers get code 414, with the example message.
  --
  -- A body, which the POST endpoints take to enable larger requests, may carry any number.
  --
  -- The count comes before the texts are read, an order that the source does not fix.
  if inQuery && texts.length > MAX_QUERY_IDS then
    .error { code := 414, message := "Too many validator IDs in request" }
  -- Each text is an index or a public key, else code 400.
  else texts.mapM parseValidatorId

/-- The status filter of a request, or an error with code 400 for a text that is no name. -/
def readStatusFilter (texts : List String) : Except ErrorMessage StatusFilter :=
  -- Each text is a status or a group, else code 400.
  texts.mapM StatusName.parse

/-- The builder identifiers of a request, or an error with code 400 for a text that is none. -/
def readBuilderIds (texts : List String) : Except ErrorMessage (List ValidatorId) :=
  -- The builders endpoint: a body with any number of identifiers.
  --
  -- Each is a builder index or a public key, as a validator identifier is, else code 400.
  texts.mapM fun text => (parseValidatorId text).mapError fun _ => invalidId "builder" text

/-! ## Responses -/

/-- The response of the validators endpoint, without the two flags that come from the store. -/
def validatorsResponse (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : StatusFilter) : Except ErrorMessage ApiEnvelope := do
  -- An entry with no JSON gives code 500.
  let entries ← (stateValidators state ids filter).mapM fun entry =>
    entry.toJson.mapError fun _ => internalError "no JSON of an entry"
  -- The validators endpoint: the data is the array of the entries, with no version.
  return { data := .arr entries.toArray }

/-- The response of the balances endpoint, without the two flags that come from the store. -/
def balancesResponse (state : BeaconState preset fork) (ids : List ValidatorId) :
    Except ErrorMessage ApiEnvelope := do
  -- The balances endpoint: the array of the entries, with no version.
  return { data := .arr (← (stateBalances state ids).mapM apiJsonOr500).toArray }

/-- The SSZ body of the balances answer. -/
def balancesSsz (state : BeaconState preset fork) (ids : List ValidatorId) :
    Except ErrorMessage ByteArray :=
  let entries := (stateBalances state ids).toArray
  -- The balances endpoint: a list of index and balance pairs, bounded by the registry limit.
  if bound : entries.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat then
    apiSszOr500 (SszList.mk entries bound)
  -- A longer answer has no SSZ form: code 500.
  else .error (internalError "more balances than the registry limit")

/-- The response of the identities endpoint, without the two flags that come from the store.

The source gives no list type for its SSZ body, so there is none here. -/
def identitiesResponse (state : BeaconState preset fork) (ids : List ValidatorId) :
    Except ErrorMessage ApiEnvelope := do
  return { data := .arr (← (stateIdentities state ids).mapM apiJsonOr500).toArray }

/-! ## Builders -/

/-- From Gloas: the index of the builder that an identifier names in a state, or none. -/
def resolveBuilderId (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    ValidatorId → Option BuilderIndex
  -- The builders endpoint: an index names a builder when it is below the size of the registry.
  | .index index => if index.toNat < (state.builders gloas).data.size then some index else none
  -- A public key names the first builder of the registry that holds it, EthLib's choice.
  --
  -- The source does not say which builder a key held twice names.
  | .pubkey pubkey => ((state.builders gloas).data.findIdx? (·.pubkey == pubkey)).map UInt64.ofNat

/-- The builder status that a text gives, as the API writes it, or an error with code 400. -/
def BuilderStatus.parse (text : String) : Except ErrorMessage BuilderStatus :=
  -- The builders endpoint: one of the three builder statuses of the schema.
  match [BuilderStatus.pending, .active, .exited].find? (·.name == text) with
  | some found => .ok found
  -- Else an invalid status: code 400, with EthLib's message.
  | none => .error { code := 400, message := s!"Invalid builder status: {text}" }

/-- Whether a builder status passes a filter: the filter is empty, or it holds the status. -/
def builderStatusPasses (filter : List BuilderStatus) (status : BuilderStatus) : Bool :=
  -- The builders endpoint: an empty or omitted list takes all statuses.
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

/-- From Gloas: the entries of the builders answer, for the requested builders. -/
def stateBuilders (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (ids : List ValidatorId) (filter : List BuilderStatus) : List BuilderResponse :=
  -- The builders that the identifiers name, as for validators.
  (selectIndices (state.builders gloas).data.size (resolveBuilderId state gloas) ids).filterMap
    fun index => do
      let builder ← (state.builders gloas).data[index.toNat]?
      -- The status that the state gives the builder.
      let status ← (builderStatus state gloas index).toOption
      -- Only a builder whose status passes the filter.
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
    -- An entry with no JSON gives code 500.
    let entries ← (stateBuilders state gloas ids filter).mapM fun entry =>
      entry.toJson.mapError fun _ => internalError "no JSON of an entry"
    return { data := .arr entries.toArray }
  -- The builders endpoint: 400 for a state before Gloas.
  else .error (beforeFork "builders" .glamsterdam)

end EthLib.Consensus.BeaconApi
