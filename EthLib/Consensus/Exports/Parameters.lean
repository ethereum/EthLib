module

public import EthLib.Base.Exports
public import Lean.Data.Json
public import EthLib.Base.Hex
public import EthLib.Consensus.Config
public import EthLib.Consensus.Preset
public import EthLib.Networking.ReqResp.Encoding

/-!
# `Exports.Parameters`

C-ABI exports of the presets, the configurations and the parameters at a fork.

Each one comes back as a JSON object whose keys are the names of the source.

An integer is a string of decimal digits, and a byte string is `0x` and lowercase hex.

A preset or a configuration is named by `mainnet` or `minimal`, and a fork by its name in Lean.

An unknown name comes back as code 0 and a message, since no error type covers it.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result forkUpTo)

open Lean Base

/-- Bytes in hex, after `0x`. -/
instance {n : Nat} : ToJson (Vector UInt8 n) where
  toJson bytes := toString <| bytes.toList.foldl (init := "0x") fun text byte =>
    (text.push hexAlphabet[byte.toNat / 16]!).push hexAlphabet[byte.toNat % 16]!

/-- A 256-bit integer as decimal digits. -/
instance : ToJson U256 where
  toJson n := toString n.toNat

deriving instance ToJson for Preset
deriving instance ToJson for BlobScheduleEntry
deriving instance ToJson for Networking.Gossip.SubnetParameters
deriving instance ToJson for Config
deriving instance ToJson for Parameters

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

/-- The fork of a name, for the forks from Phase 0 to BPO2, the last fork up to Fulu.

Gloas and Heze are not yet specified, so Glamsterdam and Hegotá fail. -/
def forkOf (name : ByteArray) : Result Fork := do
  let fork ← forkUpTo .bpo2 name
  if .phase0 ≤ fork then return fork
  else throw (0, s!"{fork.name} is not a fork of the beacon chain")

/-- The JSON text of a value, as UTF-8 bytes. -/
def jsonBytes (value : Json) : ByteArray := value.compress.toUTF8

/-- The preset of a name, as a JSON object. -/
@[export eth_consensus_preset]
def presetExport (name : ByteArray) : Result ByteArray := do
  return jsonBytes (presetJson (← presetOf (← nameOf name)))

/-- The configuration of a name, with the payload cap that every network shares. -/
def configJson (config : Config) : Json :=
  (toJson config).mergeObj <| Json.mkObj [
    ("MAX_PAYLOAD_SIZE", toJson Networking.ReqResp.MAX_PAYLOAD_SIZE)]

/-- The configuration of a name, as a JSON object. -/
@[export eth_consensus_config]
def configExport (name : ByteArray) : Result ByteArray := do
  return jsonBytes (configJson (← configOf (← nameOf name)))

/-- The parameters of a preset at a fork, as a JSON object. -/
@[export eth_consensus_parameters]
def parametersExport (name fork : ByteArray) : Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  return jsonBytes (toJson (parameters preset (← forkOf fork)))

end EthLib.Consensus.Exports
