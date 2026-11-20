module

public import EthLib.Consensus.KeymanagerApi.Types
public import EthLib.Consensus.BuilderApi.AuthData
public import EthLib.Consensus.Containers.BuilderConfig

/-!
# `Consensus.KeymanagerApi.BuilderConfig`

The calls of the Keymanager API on the builder configuration of a key, from [the source].

They are on `/eth/v1/validator/{pubkey}/builder_config`: a get, a set and a delete.

A configuration names the builders that a key asks for bids, and the terms of each bid.

The operator may leave out fields, and the [schema] says how each one resolves.

An omitted list of builders is the list of the client.

An omitted term of an entry is the default of the key, and then that of the client.

An omitted cap on the execution payment is that of the client.

Omitted authentication data is the default data of the URL of the entry.

Omitted builder keys are the empty list, which accepts any builder.

A get gives the resolved configuration, so a set of that answer fixes every value.

A set replaces the stored configuration in full, and a delete removes it.

[the source]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/apis/builder_config.yaml
[schema]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/types/builder_entry.yaml
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-! ## The stored and the resolved forms -/

/-- One builder of a configuration as the operator set it, with each term optional. -/
structure BuilderEntrySetting where
  /-- The URL of the builder, which the source requires. -/
  url : String
  /-- The data that authenticates a request to the builder. -/
  authData : Option ByteArray := none
  /-- The builder keys whose bids the entry accepts. -/
  builderPubkeys : Option (List BLSPubkey) := none
  /-- The cap on the execution payment counted in a bid, in Gwei. -/
  maxExecutionPayment : Option UInt64 := none
  /-- The floor on the payment of a bid, in Gwei. -/
  minBid : Option UInt64 := none
  /-- The weight of a bid, in percent. -/
  builderBoostFactor : Option UInt64 := none

/-- A configuration as the operator set it, with each field optional. -/
structure BuilderConfigSetting where
  /-- The default floor of the key, in Gwei. -/
  minBid : Option UInt64 := none
  /-- The default weight of the key, in percent. -/
  builderBoostFactor : Option UInt64 := none
  /-- The builders, or none for those of the client. -/
  builders : Option (List BuilderEntrySetting) := none

/-- One builder with every term fixed: the terms of a bid of the Beacon API, and how to reach it.
-/
structure ResolvedBuilderEntry where
  /-- The URL of the builder. -/
  url : String
  /-- The data that authenticates a request to the builder. -/
  authData : ByteArray
  /-- The terms that a bid from the builder must meet. -/
  terms : BidTerms

/-- A configuration with every value fixed. -/
structure ResolvedBuilderConfig where
  /-- The floor of the key, in Gwei, which also applies to bids received on gossip. -/
  minBid : UInt64
  /-- The weight of the key, in percent, which also applies to bids received on gossip. -/
  builderBoostFactor : UInt64
  /-- The builders. -/
  builders : List ResolvedBuilderEntry

/-- The builder configuration of the client, which a key without its own follows.

The client fixes it at its start, as the source says, so it is a value. -/
structure ClientBuilderConfig where
  /-- The floor of a key without its own, in Gwei. -/
  minBid : UInt64
  /-- The weight of a key without its own, in percent. -/
  builderBoostFactor : UInt64
  /-- The cap on the execution payment of an entry without its own, in Gwei. -/
  maxExecutionPayment : UInt64
  /-- The builders of a key without its own list. -/
  builders : List BuilderEntrySetting

/-! ## Resolution -/

/-- The authentication data of an entry: its own, else the default data of its URL. -/
def BuilderEntrySetting.resolvedAuthData (entry : BuilderEntrySetting) :
    Except BuilderApi.AuthDataError ByteArray :=
  match entry.authData with
  | some data => .ok data
  | none => BuilderApi.defaultAuthData entry.url

/-- An entry with every term fixed, from the defaults of its key and of the client. -/
def BuilderEntrySetting.resolve (client : ClientBuilderConfig) (minBid builderBoostFactor : UInt64)
    (entry : BuilderEntrySetting) : Except BuilderApi.AuthDataError ResolvedBuilderEntry := do
  return {
    url := entry.url
    authData := ← entry.resolvedAuthData
    terms := {
      builderPubkeys := entry.builderPubkeys.getD []
      maxExecutionPayment := entry.maxExecutionPayment.getD client.maxExecutionPayment
      minBid := entry.minBid.getD minBid
      builderBoostFactor := entry.builderBoostFactor.getD builderBoostFactor } }

/-- A configuration with every value fixed, from the configuration of the client.

The defaults of the key apply to the builders of the client too, as the schema says. -/
def BuilderConfigSetting.resolve (client : ClientBuilderConfig) (config : BuilderConfigSetting) :
    Except BuilderApi.AuthDataError ResolvedBuilderConfig := do
  let minBid := config.minBid.getD client.minBid
  let builderBoostFactor := config.builderBoostFactor.getD client.builderBoostFactor
  let builders ← (config.builders.getD client.builders).mapM
    (BuilderEntrySetting.resolve client minBid builderBoostFactor)
  return { minBid, builderBoostFactor, builders }

/-- The stored form of a resolved entry, with every term set. -/
def ResolvedBuilderEntry.toSetting (entry : ResolvedBuilderEntry) : BuilderEntrySetting :=
  { url := entry.url, authData := some entry.authData
    builderPubkeys := some entry.terms.builderPubkeys
    maxExecutionPayment := some entry.terms.maxExecutionPayment, minBid := some entry.terms.minBid
    builderBoostFactor := some entry.terms.builderBoostFactor }

/-- The stored form of a resolved configuration, with every value set. -/
def ResolvedBuilderConfig.toSetting (config : ResolvedBuilderConfig) : BuilderConfigSetting :=
  { minBid := some config.minBid, builderBoostFactor := some config.builderBoostFactor
    builders := some (config.builders.map ResolvedBuilderEntry.toSetting) }

/-! ## The JSON form -/

-- The bounds of the schema are those of the Beacon API configuration and of the Builder API.

/-- Authentication data: `0x` and between 1 and 4096 bytes of hex, in either letter case. -/
def readAuthData (path : String) (document : Json) : Except KeymanagerError ByteArray := do
  let text ← readString path document
  match Serialization.Ssz.ofHex text with
  | .ok bytes =>
    if 1 ≤ bytes.size ∧ bytes.size ≤ MAX_BUILDER_AUTH_DATA_SIZE then .ok ⟨bytes⟩
    else .error (.field path)
  | .error _ => .error (.field path)

/-- A URL: a string of 1 to 2048 bytes. -/
def readBuilderUrl (path : String) (document : Json) : Except KeymanagerError String := do
  let url ← readString path document
  if 1 ≤ url.utf8ByteSize ∧ url.utf8ByteSize ≤ MAX_BUILDER_URL_SIZE then .ok url
  else .error (.field path)

/-- At most 64 builder keys. -/
def readBuilderPubkeys (path : String) (document : Json) :
    Except KeymanagerError (List BLSPubkey) := do
  let keys ← readPubkeys path document
  if keys.length ≤ MAX_BUILDER_PUBKEYS then .ok keys else .error (.field path)

/-- An entry of a configuration, from its object; its URL is required. -/
def readBuilderEntrySetting (path : String) (document : Json) :
    Except KeymanagerError BuilderEntrySetting := do
  return {
    url := ← requiredField path "url" readBuilderUrl document
    authData := ← optionalField path "auth_data" readAuthData document
    builderPubkeys := ← optionalField path "builder_pubkeys" readBuilderPubkeys document
    maxExecutionPayment := ← optionalField path "max_execution_payment" readUint64 document
    minBid := ← optionalField path "min_bid" readUint64 document
    builderBoostFactor := ← optionalField path "builder_boost_factor" readUint64 document }

/-- At most 64 entries of a configuration, each read in turn. -/
def readBuilderEntries (path : String) (document : Json) :
    Except KeymanagerError (List BuilderEntrySetting) := do
  let .arr elements := document | .error (.field path)
  let entries ← elements.toList.zipIdx.mapM fun (element, index) =>
    readBuilderEntrySetting s!"{path}[{index}]" element
  if entries.length ≤ MAX_BUILDER_ENTRIES then .ok entries else .error (.field path)

/-- A configuration, from its object; every field may be left out. -/
def readBuilderConfigSetting (document : Json) : Except KeymanagerError BuilderConfigSetting := do
  return {
    minBid := ← optionalField "" "min_bid" readUint64 document
    builderBoostFactor := ← optionalField "" "builder_boost_factor" readUint64 document
    builders := ← optionalField "" "builders" readBuilderEntries document }

/-! ## The rules of a set -/

/-- Why a configuration may not be set: an entry whose authentication data does not resolve.

Two entries with the same URL and the same authentication data are refused too.

Omitted data is compared as the default data of the URL, as the schema says. -/
def BuilderConfigSetting.refusal (config : BuilderConfigSetting) : Option String :=
  match (config.builders.getD []).mapM fun entry => do
      return (entry.url, ← entry.resolvedAuthData) with
  | .error _ => some "an entry has no authentication data and its URL gives none"
  | .ok pairs =>
    if pairs.Nodup then none else some "two entries share their URL and authentication data"

/-- The builder configuration of a client, from an object of the keymanager form.

Each field is required: the floor, the weight, the cap on the execution payment and the builders.

The builders must meet the rules of a set, as those of a key do.
-/
def readClientBuilderConfig (document : Json) : Except KeymanagerError ClientBuilderConfig := do
  let minBid ← requiredField "" "min_bid" readUint64 document
  let builderBoostFactor ← requiredField "" "builder_boost_factor" readUint64 document
  let maxExecutionPayment ← requiredField "" "max_execution_payment" readUint64 document
  let builders ← requiredField "" "builders" readBuilderEntries document
  if ({ builders := some builders } : BuilderConfigSetting).refusal.isSome then
    throw (.field ".builders")
  return { minBid, builderBoostFactor, maxExecutionPayment, builders }

/-- Authentication data as the API writes it, in lowercase hex. -/
def authDataJson (data : ByteArray) : Json :=
  .str (Serialization.Ssz.toHex data.data)

/-- The JSON of a resolved entry, with every field. -/
def resolvedBuilderEntryJson (entry : ResolvedBuilderEntry) : Json :=
  Json.mkObj [
    ("url", stringJson entry.url),
    ("auth_data", authDataJson entry.authData),
    ("builder_pubkeys", .arr (entry.terms.builderPubkeys.map Interchange.bytesJson).toArray),
    ("max_execution_payment", Interchange.uint64Json entry.terms.maxExecutionPayment),
    ("min_bid", Interchange.uint64Json entry.terms.minBid),
    ("builder_boost_factor", Interchange.uint64Json entry.terms.builderBoostFactor)]

/-- The JSON of a resolved configuration, with every field. -/
def resolvedBuilderConfigJson (config : ResolvedBuilderConfig) : Json :=
  Json.mkObj [
    ("min_bid", Interchange.uint64Json config.minBid),
    ("builder_boost_factor", Interchange.uint64Json config.builderBoostFactor),
    ("builders", .arr (config.builders.map resolvedBuilderEntryJson).toArray)]

end EthLib.Consensus.KeymanagerApi
