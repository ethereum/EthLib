module

public import EthLib.Base.ChainConfig
public import EthLib.Base.ExecutionConfig
public import EthLib.Base.Hex
public import EthLib.Base.Exports.PyValue
public import Lean.Data.Json

/-!
# Exports: the active fork of a network

The C exports of the active fork of a chain, for the Python bindings.

A chain is named, as mainnet, Hoodi and Sepolia are, or passes its configuration as a `dict`.

The configuration of a named chain also crosses as a `dict`.
-/

public section

namespace EthLib.Base.ChainConfig.Exports

open EthLib.Exports (ExportError Result PyValue UnreadArgument pyExport forkOfName
  rejectArgument toResult)

open Lean (Json)

/-- An activation from its kind, `block` or `time`, and its number.

The number must be below `2^64`, since the fork identifier holds it in 64 bits.

A blob schedule reads its activation here too, so it has the bound, though no identifier holds it.
-/
def activationOf (kind : String) (n : Json) : Result Activation := do
  let some n := n.getNat?.toOption | rejectArgument none "an activation has no number"
  -- The fork identifier hashes an activation in 64 bits, so a larger one is refused.
  unless n < ACTIVATION_BOUND do rejectArgument none "an activation is not below 2^64"
  match kind with
  | "block" => pure (.block n)
  | "time" => pure (.time n)
  | _ => rejectArgument none s!"no activation kind {kind}"

/-- One activation of a configuration: a fork name, `block` or `time`, and a number. -/
def activationOfJson (j : Json) : Result (Fork × Activation) := do
  let .arr #[.str name, .str kind, n] := j
    | rejectArgument none "an activation is not [fork, kind, n]"
  return (← forkOfName name.toUTF8, ← activationOf kind n)

/-- One blob schedule: `block` or `time`, a number, the target, the maximum and the update fraction.

A fork name in front gives the fork that the schedule belongs to.

The three numbers must meet the bounds of a schedule, so the target and maximum stay in 64 bits. -/
def blobScheduleOfJson (j : Json) : Result (Option Fork × Activation × BlobSchedule) := do
  let (fork, kind, n, target, max, fraction) ← match j with
    | .arr #[.str kind, n, target, max, fraction] => pure (none, kind, n, target, max, fraction)
    | .arr #[.str name, .str kind, n, target, max, fraction] =>
      pure (some (← forkOfName name.toUTF8), kind, n, target, max, fraction)
    | _ => rejectArgument none "a blob schedule is not [fork?, kind, n, target, max, fraction]"
  let some target := target.getNat?.toOption | rejectArgument none "a blob schedule has no target"
  let some max := max.getNat?.toOption | rejectArgument none "a blob schedule has no maximum"
  let some fraction := fraction.getNat?.toOption
    | rejectArgument none "a blob schedule has no fraction"
  let some schedule := BlobSchedule.ofNat? target max fraction
    | rejectArgument none ("a blob schedule needs target ≤ max, 0 < max, " ++
        "0 < update fraction and a blob gas of max below 2^64")
  return (fork, ← activationOf kind n, schedule)

/-- The deposit contract address of a configuration: `0x` and forty hex digits. -/
def depositContractOfJson (j : Json) : Result Address := do
  let text ← match j with
    | .str text => pure text
    | .null => rejectArgument none "config: no depositContractAddress"
    | _ => rejectArgument none "config: depositContractAddress is not text"
  let '0' :: 'x' :: digits := text.toList
    | rejectArgument none "config: depositContractAddress does not start with 0x"
  unless digits.length = 40 do
    rejectArgument none "config: depositContractAddress is not forty hex digits"
  let some bytes := hexBytes? digits
    | rejectArgument none "config: depositContractAddress is not hex"
  -- Python `bytes` become `0x` and forty hex digits, which read back as these 20 bytes.
  toResult none (Base.exactBytes 20 bytes fun _ =>
    UnreadArgument.mk "config: depositContractAddress is not 20 bytes")

/-- A chain configuration given as JSON, with no blob schedule of its own when none is given.

The deposit contract address must be given, since no address is right for every chain.

No fork by block number may come after a fork by timestamp in the timeline, as EIP-6122 requires.

The chain ID is a 64-bit number, so a larger one is rejected rather than reduced. -/
def configOfJson (j : Json) : Result ChainConfig := do
  -- The keys of the JSON are the chain ID, the deposit contract, the activations and the schedules.
  let some chainId := (j.getObjValAs? Nat "chainId").toOption
    | rejectArgument none "config: no chainId"
  unless chainId < 2 ^ 64 do rejectArgument none "config: chainId is not below 2^64"
  let depositContractAddress ← depositContractOfJson (j.getObjValD "depositContractAddress")
  let .arr activations := j.getObjValD "activations"
    | rejectArgument none "config: no activations"
  let activations ← activations.toList.mapM activationOfJson
  -- EIP-6122 puts forks by time after forks by block, so none comes before a fork by block.
  unless activationsOrdered activations do
    rejectArgument none "config: a fork by block comes after a fork by time"
  let schedules ← match j.getObjValD "blobSchedules" with
    | .arr entries => entries.toList.mapM blobScheduleOfJson
    | .null => pure []
    | _ => rejectArgument none "config: blobSchedules is not an array"
  return { chainId := UInt64.ofNat chainId, depositContractAddress := depositContractAddress,
            activations := activations, blobSchedules := schedules }

/-- The configuration of a chain that EthLib holds, by its name. -/
def namedConfigOf : String → Result ChainConfig
  | "mainnet" => pure mainnet
  | "hoodi" => pure hoodi
  | "sepolia" => pure sepolia
  -- No error type covers an unknown name, so it has code 0 and a message.
  | name => rejectArgument none s!"no chain is named {name}"

/-- An activation as the reader of a configuration takes it: its kind, then its number. -/
def activationJson : Activation → List Json
  | .block n => [.str "block", Lean.toJson n]
  | .time t => [.str "time", Lean.toJson t]

/-- A configuration as the JSON that the reader of a configuration takes. -/
def configJsonOf (config : ChainConfig) : Json :=
  Json.mkObj [
    ("chainId", Lean.toJson config.chainId.toNat),
    -- The address is `0x` and forty lowercase hex digits.
    ("depositContractAddress", .str (hexString config.depositContractAddress.toList)),
    -- Each activation is its fork's name, its kind and its number.
    ("activations", .arr (config.activations.map fun (fork, a) =>
      Json.arr (.str fork.name :: activationJson a).toArray).toArray),
    -- Each schedule is its fork's name if it has one, its activation and its three numbers.
    ("blobSchedules", .arr (config.blobSchedules.map fun (fork, a, s) =>
      Json.arr ((fork.map fun f => Json.str f.name).toList ++ activationJson a ++
        [Lean.toJson s.target.toNat, Lean.toJson s.max.toNat,
          Lean.toJson s.baseFeeUpdateFraction]).toArray).toArray)]

/-- The configuration of a chain that EthLib holds, as a `dict`. -/
def chainConfigValue (name : String) : Result PyValue := do
  return .ofJson (configJsonOf (← namedConfigOf name))

/-- The configuration of a chain that EthLib holds, as a `dict`.

The argument is the name of the chain: `mainnet`, `hoodi` or `sepolia`. -/
@[export eth_chain_config]
def chainConfigExport (args : PyValue) : Result PyValue := pyExport chainConfigValue args

/-- The name of the active fork of a chain at a block, if a fork is active.

The chain is the name of one that EthLib holds, or a configuration as a `dict`. -/
def activeForkOf (args : PyValue × UInt64 × UInt64) : Result (Option String) := do
  -- A block number and a timestamp cross the boundary as 64-bit integers, as EIP-6122 reads them.
  let (config, number, timestamp) := args
  let config ← match config with
    -- A name crosses as a `str`, and picks a configuration that EthLib holds.
    | .str name => namedConfigOf name
    -- A configuration crosses as the typed value of its JSON, a `dict`.
    | config => configOfJson config.toJson
  -- A fork crosses the boundary as its name, a `str` such as `bellatrix`.
  return (config.activeFork number.toNat timestamp.toNat).map (·.name)

/-- The name of the active fork of a chain at a block, or `None` when none is active.

The arguments are the chain, the block number and the timestamp.

The chain is a name or a configuration `dict`. -/
@[export eth_active_fork]
def activeForkExport (args : PyValue) : Result PyValue := pyExport activeForkOf args

/-- A refused configuration file reaches Python with its code and its printed error. -/
instance : ExportError ExecutionConfig.ConfigError where
  code := ExecutionConfig.ConfigError.code
  message := reprStr

/-- A base configuration given as JSON, merged with the keys of a configuration file.

A file that the reader refuses gives the code of its error. -/
def executionConfigOf (base file : PyValue) : Result ChainConfig := do
  let base ← configOfJson base.toJson
  -- A client configuration file crosses as the `dict` of its JSON.
  --
  -- EIP-7840 and EIP-7892 shape that JSON.
  toResult "execution config" (ExecutionConfig.readExecutionConfig base file.toJson)

/-- The blob schedule of a chain at a block, from a base configuration and a configuration file.

It is the target, the maximum and the update fraction, if the chain sets a schedule there. -/
def executionBlobScheduleOf (args : PyValue × PyValue × UInt64 × UInt64) :
    Result (Option (UInt64 × UInt64 × Nat)) := do
  let (base, file, number, timestamp) := args
  let config ← executionConfigOf base file
  return (config.blobScheduleAt number.toNat timestamp.toNat).map
    fun s => (s.target, s.max, s.baseFeeUpdateFraction)

/-- The blob schedule of a chain at a block, from a base configuration and a configuration file.

The arguments are the base and the file as `dict`, the block number and the timestamp. -/
@[export eth_execution_blob_schedule]
def executionBlobScheduleExport (args : PyValue) : Result PyValue :=
  pyExport executionBlobScheduleOf args

/-- The fork times and blob schedules of a configuration, as a configuration file holds them.

A configuration that a file cannot hold whole is refused, so the export loses nothing.

The check reads the file back onto the forks by block number, and compares. -/
def writeExecutionConfigOf (config : PyValue) : Result PyValue := do
  let config ← configOfJson config.toJson
  let file := ExecutionConfig.writeExecutionConfig config
  let blocks := { config with
    activations := config.activations.filter (·.2 matches .block _), blobSchedules := [] }
  unless (ExecutionConfig.readExecutionConfig blocks file).toOption == some config do
    rejectArgument none "config: a configuration file cannot hold it whole"
  return .ofJson file

/-- The fork times and blob schedules of a configuration, as the `dict` of a configuration file.

The argument is the configuration as a `dict`. -/
@[export eth_write_execution_config]
def writeExecutionConfigExport (args : PyValue) : Result PyValue :=
  pyExport writeExecutionConfigOf args

end EthLib.Base.ChainConfig.Exports
