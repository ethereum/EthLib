module

public import EthLib.Consensus.KeymanagerApi.Client

/-!
# `Consensus.KeymanagerApi.Settings`

The calls of the Keymanager API that set the fee recipient, the gas limit and the graffiti of a key.

They are on `/eth/v1/validator/{pubkey}/` with [`feerecipient`], [`gas_limit`] and [`graffiti`].

Each setting maps keys to values, and a key without a mapping has the default of the client.

The client takes its defaults at its start, as the source says.

A get gives the value of the key, or the default, with HTTP 200.

A set replaces any earlier mapping of the key, with HTTP 202.

A delete removes the mapping of a key that the client manages, with HTTP 204.

Each call gets HTTP 404 for a key that the client does not manage, local or remote.

The source gives the get, the set and the delete this one response: the key was not found.

A fee recipient of zero is refused with HTTP 400; the source forbids it and names no code.

The source does not say how a graffiti string fills the 32 bytes of a block, so it is kept as is.

[`feerecipient`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/apis/fee_recipient.yaml
[`gas_limit`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/apis/gas_limit.yaml
[`graffiti`]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/apis/graffiti.yaml
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-- Whether the client manages a key: it holds it, or signs with it through a remote signer. -/
def KeyState.isManaged (state : KeyState) (pubkey : BLSPubkey) : Bool :=
  state.isActive pubkey || state.remoteKeys.any (·.pubkey == pubkey)

/-- A setting of each key: where the state keeps its mappings, and its default. -/
structure Setting (α : Type) where
  /-- The mappings of the setting in a state, latest first. -/
  mappings : KeyState → List (BLSPubkey × α)
  /-- The state with other mappings of the setting. -/
  withMappings : KeyState → List (BLSPubkey × α) → KeyState
  /-- The default value, which the client fixes at its start. -/
  default : ClientConfig → α

namespace Setting

variable {α : Type}

/-- The value of a key: its mapping, or the default. -/
def get (setting : Setting α) (config : ClientConfig) (state : KeyState) (pubkey : BLSPubkey) :
    α :=
  ((setting.mappings state).lookup pubkey).getD (setting.default config)

/-- The state after a set, whose mapping replaces any earlier one of the key. -/
def set (setting : Setting α) (state : KeyState) (pubkey : BLSPubkey) (value : α) : KeyState :=
  setting.withMappings state ((pubkey, value) :: (setting.mappings state).filter (·.1 != pubkey))

/-- The response with HTTP 404 for a key that the client does not manage. -/
def notManaged : Response :=
  ⟨404, errorResponseJson ⟨"The key was not found on the server"⟩⟩

/-- The state after a delete, which removes the mapping of a key that the client manages. -/
def delete (setting : Setting α) (state : KeyState) (pubkey : BLSPubkey) :
    Except Response KeyState :=
  if state.isManaged pubkey then
    .ok (setting.withMappings state ((setting.mappings state).filter (·.1 != pubkey)))
  else .error notManaged

end Setting

/-- The fee recipient of each key. -/
def feeRecipientSetting : Setting ExecutionAddress where
  mappings state := state.feeRecipients
  withMappings state mappings := { state with feeRecipients := mappings }
  default config := config.defaultFeeRecipient

/-- The gas limit of each key. -/
def gasLimitSetting : Setting UInt64 where
  mappings state := state.gasLimits
  withMappings state mappings := { state with gasLimits := mappings }
  default config := config.defaultGasLimit

/-- The graffiti of each key. -/
def graffitiSetting : Setting String where
  mappings state := state.graffiti
  withMappings state mappings := { state with graffiti := mappings }
  default config := config.defaultGraffiti

/-! ## The calls -/

/-- The answer of a get with HTTP 200, whose data is the given JSON. -/
def dataResponse (data : Json) : Response :=
  ⟨200, Json.mkObj [("data", data)]⟩

/-- The calls on one setting at the path of a key: a get, a set and a delete.

The body of a set reads to a value, which a check may refuse with a message. -/
structure SettingCalls (α : Type) where
  /-- The setting. -/
  setting : Setting α
  /-- The value of the body of a set. -/
  read : Json → Except KeymanagerError α
  /-- Why a value may not be set, if it may not. -/
  refuse : α → Option String
  /-- The answer of a get, from the settings of the client, the key and its value. -/
  answer : ClientConfig → BLSPubkey → α → Response

/-- The response of a call on a setting at the path of a key, and the state after it. -/
def SettingCalls.handle {α : Type} (calls : SettingCalls α) (config : ClientConfig)
    (state : KeyState) (method : String) (pubkey : BLSPubkey) (body : Json) :
    Response × KeyState :=
  if !state.isManaged pubkey then (Setting.notManaged, state) else
  match method with
  | "GET" =>
    (calls.answer config pubkey (calls.setting.get config state pubkey),
      state)
  | "POST" =>
    match calls.read body with
    | .error _ => (badRequest "the request does not read", state)
    | .ok value =>
      match calls.refuse value with
      | some message => (badRequest message, state)
      | none => (⟨202, .null⟩, calls.setting.set state pubkey value)
  | "DELETE" =>
    match calls.setting.delete state pubkey with
    | .ok state => (⟨204, .null⟩, state)
    | .error response => (response, state)
  | _ => (⟨404, errorResponseJson ⟨"Path not found"⟩⟩, state)

/-- The calls on the fee recipient, which refuse the zero address. -/
def feeRecipientCalls : SettingCalls ExecutionAddress where
  setting := feeRecipientSetting
  read := requiredField "" "ethaddress" readEthAddress
  refuse address :=
    if address = Vector.replicate 20 0 then
      some "Cannot specify the 0x00 fee recipient address through the API"
    else none
  answer _ pubkey address := dataResponse (feeRecipientJson ⟨some pubkey, address⟩)

/-- The calls on the gas limit. -/
def gasLimitCalls : SettingCalls UInt64 where
  setting := gasLimitSetting
  read := requiredField "" "gas_limit" readUint64
  refuse _ := none
  answer _ pubkey limit := dataResponse (gasLimitJson ⟨some pubkey, limit⟩)

/-- The calls on the graffiti. -/
def graffitiCalls : SettingCalls String where
  setting := graffitiSetting
  read := requiredField "" "graffiti" readString
  refuse _ := none
  answer _ pubkey graffiti := dataResponse
    (Json.mkObj [("pubkey", Interchange.bytesJson pubkey), ("graffiti", stringJson graffiti)])

/-! ## The builder configuration -/

/-- The builder configuration of each key; a key never set has the empty configuration.

The empty configuration resolves as the client's own, as the [source] says of a set of `{}`.

[source]: https://github.com/ethereum/keymanager-APIs/blob/3e7c64e2118f819a51de7093ea2b2f03bb2f8f6e/apis/builder_config.yaml
-/
def builderConfigSetting : Setting BuilderConfigSetting where
  mappings state := state.builderConfigs
  withMappings state mappings := { state with builderConfigs := mappings }
  default _ := {}

/-- The answer of a get of a builder configuration: the configuration resolved, with HTTP 200.

A configuration that does not resolve, from a client whose own one does not, gives HTTP 500. -/
def builderConfigGet (config : ClientConfig) (value : BuilderConfigSetting) : Response :=
  match value.resolve config.builder with
  | .ok resolved => dataResponse (resolvedBuilderConfigJson resolved)
  | .error _ => ⟨500, errorResponseJson ⟨"the builder configuration does not resolve"⟩⟩

/-- The calls on the builder configuration of a key.

A get gives the configuration of the key resolved against that of the client.

A set replaces the configuration of the key in full, and a delete removes it.

A set whose entries share a URL and authentication data is refused with HTTP 400.

So is a set with an entry whose authentication data is omitted and whose URL gives none. -/
def builderConfigCalls : SettingCalls BuilderConfigSetting where
  setting := builderConfigSetting
  read := readBuilderConfigSetting
  refuse value := value.refusal
  answer config _ value := builderConfigGet config value

end EthLib.Consensus.KeymanagerApi
