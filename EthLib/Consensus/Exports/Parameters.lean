module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.PyValue
public import Lean.Data.Json
public import EthLib.Base.Hex
public import EthLib.Base.Json.Document
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Consensus.BeaconApi.Config
public import EthLib.Networking.ReqResp.Encoding

/-!
# `Exports.Parameters`

C-ABI exports of the presets, the configurations and the parameters at a fork.

Each one takes typed Python values and comes back as a `dict`, keyed by the names of the source.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result PyValue UnreadArgument forkUpTo pyExport rejectArgument
  toResult)

open Lean Base

/-- Bytes in hex, after `0x`. -/
instance {n : Nat} : ToJson (Vector UInt8 n) where
  -- A byte string reaches Python as a `str` of `0x` and lowercase hex.
  toJson bytes := hexString bytes.toList

/-- A 64-bit integer as a JSON number, which Python reads as an `int`. -/
local instance (priority := high) : ToJson UInt64 where
  -- Local, so only the forms derived here write a number.
  --
  -- Those are the forms of the preset, the configuration, the parameters and their entries.
  --
  -- Elsewhere a 64-bit integer keeps the JSON form of Lean, a string of digits.
  toJson n := toJson n.toNat

/-- A 64-bit integer, from a number or from a string that Lean reads as one. -/
local instance (priority := high) : FromJson UInt64 where
  fromJson? json := match json with
    | .str _ => Lean.UInt64.fromJson? json
    | _ => do
      let n ← fromJson? (α := Nat) json
      if h : n < UInt64.size then return UInt64.ofNatLT n h
      else throw s!"{n} does not fit in 64 bits"

/-- A 256-bit integer as a JSON number, which Python reads as an `int`. -/
local instance (priority := high) : ToJson U256 where
  -- Local to this file, as the form of a 64-bit integer is.
  toJson n := toJson n.toNat

deriving instance ToJson for BlobScheduleEntry
deriving instance ToJson for GasLimitScheduleEntry
deriving instance ToJson for Networking.Gossip.SubnetParameters
deriving instance ToJson for Config
deriving instance ToJson for Parameters

/-- Bytes from hex after `0x`, of the length of the vector. -/
instance {n : Nat} : FromJson (Vector UInt8 n) where
  fromJson? json := do
    let text ← json.getStr?
    let bytes ← (Serialization.Ssz.ofHex text).mapError fun e => s!"{text}: {reprStr e}"
    Base.exactBytes n bytes fun _ => s!"{text} does not hold {n} bytes"

/-- A 256-bit integer, from a number or from decimal digits. -/
instance : FromJson U256 where
  fromJson? json := do
    let n ← match json with
      | .str text => match text.toNat? with
        | some n => pure n
        | none => throw s!"{text} is not a number"
      | _ => fromJson? (α := Nat) json
    if n < 2 ^ 256 then return BitVec.ofNat 256 n else throw s!"{n} does not fit in 256 bits"

deriving instance FromJson for BlobScheduleEntry
deriving instance FromJson for GasLimitScheduleEntry
deriving instance FromJson for Networking.Gossip.SubnetParameters
deriving instance FromJson for Config

/-- A value of the spec map of the Beacon API, with each number as a JSON number. -/
def specValuePy : BeaconApi.SpecValue → Json
  | .int value => toJson value
  | .bytes value => hexString value
  | .text value => .str value
  | .list items => .arr (items.map specValuePy).toArray
  | .entry fields => Json.mkObj (fields.map fun (name, value) => (name, toJson value))

/-- The values of a preset or a configuration, each under its name, with numbers as numbers. -/
def entriesJson (entries : List (String × BeaconApi.SpecValue)) : Json :=
  -- The values of the spec map of the Beacon API, which names them all once.
  Json.mkObj (entries.map fun (name, value) => (name, specValuePy value))

/-- The preset of a name, with the values that it derives from its fields. -/
def presetJson (preset : Preset) : Json := entriesJson (BeaconApi.presetEntries preset)

/-- The text of a name, or an error that a Python traceback shows. -/
def nameOf (bytes : ByteArray) : Result String := do
  let some name := String.fromUTF8? bytes | rejectArgument none "name is not UTF-8"
  return name

/-- The preset of a name. -/
def presetOf : String → Result Preset
  -- A preset is named by `mainnet` or `minimal`.
  | "mainnet" => return .mainnet
  | "minimal" => return .minimal
  -- No error type covers an unknown name, so it has code 0 and a message.
  | name => rejectArgument none s!"no preset is named {name}"

/-- The configuration of a name. -/
def configOf : String → Result Config
  -- A configuration is named by `mainnet` or `minimal`.
  | "mainnet" => return .mainnet
  | "minimal" => return .minimal
  -- No error type covers an unknown name, so it has code 0 and a message.
  | name => rejectArgument none s!"no configuration is named {name}"

/-- The configuration of a name, with some of its values replaced by those of a JSON object. -/
def configWith (name replacements : ByteArray) : Result Config := do
  let config ← configOf (← nameOf name)
  -- An empty replacement keeps the configuration of the name.
  if replacements.isEmpty then return config
  let some text := String.fromUTF8? replacements | rejectArgument none "configuration is not UTF-8"
  -- The object names its values as the configuration file does.
  let replaced ← toResult none ((Base.Json.ofText text).mapError fun e =>
    UnreadArgument.mk s!"configuration: {e}")
  toResult none ((fromJson? ((toJson config).mergeObj replaced)).mapError fun e =>
    UnreadArgument.mk s!"configuration: {e}")

/-- The configuration of a name, with some of its values replaced by those of a `dict`. -/
def configWithValue (name : String) (replacements : Option PyValue) : Result Config := do
  let config ← configOf name
  match replacements with
  -- None or an empty `dict` keeps the configuration of the name.
  | none | some (.dict #[]) => return config
  -- The `dict` names its values as the configuration file does.
  --
  -- Each value replaces its key in the JSON form of the configuration, bytes as `0x` and hex.
  | some (.dict entries) =>
    toResult none
      ((fromJson? ((toJson config).mergeObj (PyValue.dict entries).toJson)).mapError fun e =>
        UnreadArgument.mk s!"configuration: {e}")
  -- Any other value than a `dict` has code 0.
  | some _ => rejectArgument none "configuration: expected a dict"

/-- The fork of a name, for the forks from Phase 0 to Hegotá, whose beacon chain is Heze. -/
def forkOf (name : ByteArray) : Result Fork := do
  -- A fork is named by its name in Lean, and an unknown name has code 0.
  let fork ← forkUpTo .hegota name
  -- The configuration has no epoch for BPO3 to BPO5, so they fail.
  if .bpo3 ≤ fork ∧ fork ≤ .bpo5 then rejectArgument none s!"fork {fork.name} not yet specified"
  if .phase0 ≤ fork then return fork
  else rejectArgument none s!"{fork.name} is not a fork of the beacon chain"

/-- The configuration of a name, with the payload cap that every network shares. -/
def configJson (config : Config) : Json := entriesJson (BeaconApi.configEntries config)

/-- The preset of a name, as a `dict`. -/
def presetValue (name : String) : Result PyValue := do
  return PyValue.ofJson (presetJson (← presetOf name))

/-- The preset of a name, as a `dict`.

The argument is the name of the preset. -/
@[export eth_consensus_preset]
def presetExport (args : PyValue) : Result PyValue := pyExport presetValue args

/-- The configuration of a name, as a `dict`. -/
def configValue (name : String) : Result PyValue := do
  return PyValue.ofJson (configJson (← configOf name))

/-- The configuration of a name, as a `dict`.

The argument is the name of the configuration. -/
@[export eth_consensus_config]
def configExport (args : PyValue) : Result PyValue := pyExport configValue args

/-- The parameters of a preset at a fork, as a `dict`. -/
def parametersValue (args : String × String) : Result PyValue := do
  let (name, fork) := args
  let preset ← presetOf name
  return PyValue.ofJson (toJson (parameters preset (← forkOf fork.toUTF8)))

/-- The parameters of a preset at a fork, as a `dict`.

The arguments are the name of the preset and the name of the fork. -/
@[export eth_consensus_parameters]
def parametersExport (args : PyValue) : Result PyValue := pyExport parametersValue args

end EthLib.Consensus.Exports
