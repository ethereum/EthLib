module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.Proofs.PyValue
public import Lean.Data.Json
public import EthLib.Base.Hex
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Consensus.Config
public import EthLib.Consensus.Preset
public import EthLib.Networking.ReqResp.Encoding

/-!
# `Exports.Parameters`

C-ABI exports of the presets, the configurations and the parameters at a fork.

Each one takes typed Python values and comes back as a `dict`.

The keys of the `dict` are the names of the source.

An integer is an `int`, and a byte string is a `str` of `0x` and lowercase hex.

A preset or a configuration is named by `mainnet` or `minimal`, and a fork by its name in Lean.

An unknown name comes back as code 0 and a message, since no error type covers it.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result PyValue forkUpTo pyExport)

open Lean Base

/-- Bytes in hex, after `0x`. -/
instance {n : Nat} : ToJson (Vector UInt8 n) where
  toJson bytes := hexString bytes.toList

/-- A 64-bit integer as a JSON number, which Python reads as an `int`.

It stays local to this file, so only the JSON forms derived here write a number.

Those are the forms of the preset, the configuration, the parameters and their entries.

Elsewhere a 64-bit integer keeps the JSON form of Lean, a string of digits. -/
local instance (priority := high) : ToJson UInt64 where
  toJson n := toJson n.toNat

/-- A 64-bit integer, from a number or from a string that Lean reads as one. -/
local instance (priority := high) : FromJson UInt64 where
  fromJson? json := match json with
    | .str _ => Lean.UInt64.fromJson? json
    | _ => do
      let n ← fromJson? (α := Nat) json
      if h : n < UInt64.size then return UInt64.ofNatLT n h
      else throw s!"{n} does not fit in 64 bits"

/-- A 256-bit integer as a JSON number, which Python reads as an `int`.

It stays local to this file, as the form of a 64-bit integer does. -/
local instance (priority := high) : ToJson U256 where
  toJson n := toJson n.toNat

deriving instance ToJson for Preset
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
    if h : bytes.size = n then return ⟨bytes, h⟩
    else throw s!"{text} does not hold {n} bytes"

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

/-- The preset of a name, with the values that it derives from its fields. -/
def presetJson (preset : Preset) : Json :=
  (toJson preset).mergeObj <| Json.mkObj [
    ("UPDATE_TIMEOUT", toJson preset.UPDATE_TIMEOUT),
    ("FIELD_ELEMENTS_PER_EXT_BLOB", toJson preset.FIELD_ELEMENTS_PER_EXT_BLOB),
    ("CELLS_PER_EXT_BLOB", toJson preset.CELLS_PER_EXT_BLOB),
    ("NUMBER_OF_COLUMNS", toJson preset.NUMBER_OF_COLUMNS)]

/-- The text of a name, or an error that a Python traceback shows. -/
def nameOf (bytes : ByteArray) : Result String := do
  let some name := String.fromUTF8? bytes | throw (0, "name is not UTF-8")
  return name

/-- The preset of a name. -/
def presetOf : String → Result Preset
  | "mainnet" => return .mainnet
  | "minimal" => return .minimal
  | name => throw (0, s!"no preset is named {name}")

/-- The configuration of a name. -/
def configOf : String → Result Config
  | "mainnet" => return .mainnet
  | "minimal" => return .minimal
  | name => throw (0, s!"no configuration is named {name}")

/-- The configuration of a name, with some of its values replaced.

The replacements come as a JSON object with the names of the configuration file.

An empty replacement keeps the configuration of the name. -/
def configWith (name replacements : ByteArray) : Result Config := do
  let config ← configOf (← nameOf name)
  if replacements.isEmpty then return config
  let some text := String.fromUTF8? replacements | throw (0, "configuration is not UTF-8")
  let replaced ← (Json.parse text).mapError fun e => (0, s!"configuration: {e}")
  (fromJson? ((toJson config).mergeObj replaced)).mapError fun e => (0, s!"configuration: {e}")

/-- The configuration of a name, with some of its values replaced.

The replacements come as a `dict` with the names of the configuration file.

Each value replaces its key in the JSON form of the configuration, bytes as `0x` and hex.

None or an empty `dict` keeps the configuration of the name.

Any other value than a `dict` has code 0. -/
def configWithValue (name : String) (replacements : Option PyValue) : Result Config := do
  let config ← configOf name
  match replacements with
  | none | some (.dict #[]) => return config
  | some (.dict entries) =>
    (fromJson? ((toJson config).mergeObj (PyValue.dict entries).toJson)).mapError fun e =>
      (0, s!"configuration: {e}")
  | some _ => throw (0, "configuration: expected a dict")

/-- The fork of a name, for the forks from Phase 0 to Hegotá, whose beacon chain is Heze.

The configuration has no epoch for BPO3 to BPO5, so they fail. -/
def forkOf (name : ByteArray) : Result Fork := do
  let fork ← forkUpTo .hegota name
  if .bpo3 ≤ fork ∧ fork ≤ .bpo5 then throw (0, s!"fork {fork.name} not yet specified")
  if .phase0 ≤ fork then return fork
  else throw (0, s!"{fork.name} is not a fork of the beacon chain")

/-- The JSON text of a value, as UTF-8 bytes. -/
def jsonBytes (value : Json) : ByteArray := value.compress.toUTF8

/-- The configuration of a name, with the payload cap that every network shares. -/
def configJson (config : Config) : Json :=
  (toJson config).mergeObj <| Json.mkObj [
    ("MAX_PAYLOAD_SIZE", toJson Networking.ReqResp.MAX_PAYLOAD_SIZE)]

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
