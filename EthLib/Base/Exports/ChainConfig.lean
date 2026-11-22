module

public import EthLib.Base.ChainConfig
public import EthLib.Base.ExecutionConfig
public import EthLib.Base.Hex
public import EthLib.Base.Exports.PyValue
public import Lean.Data.Json

/-!
# Exports: the active fork of a network

The C exports of the active fork of a chain, for the Python bindings.

Mainnet and Hoodi have an export each, and any other chain passes its configuration.

A block number and a timestamp cross the boundary as 64-bit integers, as EIP-6122 reads them.

A fork crosses it as its name, a `str` such as `bellatrix`.

A chain configuration crosses it as the typed value of its JSON, a `dict`.

Its keys are its chain ID, its deposit contract, its activations and its blob schedules.

The deposit contract is its address: `0x` and forty hex digits, which Python `bytes` become.

An activation is a fork name, `block` or `time`, and a number.

A blob schedule is `block` or `time`, a number, the target, the maximum and the update fraction.

A blob schedule can start with the name of its fork.

A client configuration file crosses as the `dict` of its JSON, as EIP-7840 and EIP-7892 shape it.
-/

public section

namespace EthLib.Base.ChainConfig.Exports

open EthLib.Exports (ExportError Result PyValue UnreadArgument pyExport forkOfName
  rejectArgument toResult)

/-- The name of the active fork of mainnet at a block, if a fork is active. -/
def mainnetActiveForkOf (args : UInt64 × UInt64) : Result (Option String) :=
  let (number, timestamp) := args
  pure ((mainnet.activeFork number.toNat timestamp.toNat).map (·.name))

/-- The name of the active fork of mainnet at a block, or `None` when none is active.

The arguments are the block number and the timestamp. -/
@[export eth_mainnet_active_fork]
def mainnetActiveForkExport (args : PyValue) : Result PyValue := pyExport mainnetActiveForkOf args

/-- The name of the active fork of Hoodi at a block, if a fork is active. -/
def hoodiActiveForkOf (args : UInt64 × UInt64) : Result (Option String) :=
  let (number, timestamp) := args
  pure ((hoodi.activeFork number.toNat timestamp.toNat).map (·.name))

/-- The name of the active fork of Hoodi at a block, or `None` when none is active.

The arguments are the block number and the timestamp. -/
@[export eth_hoodi_active_fork]
def hoodiActiveForkExport (args : PyValue) : Result PyValue := pyExport hoodiActiveForkOf args

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

/-- One blob schedule of a configuration: its activation, target, maximum and update fraction.

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
  toResult none (Base.exactBytes 20 bytes fun _ =>
    UnreadArgument.mk "config: depositContractAddress is not 20 bytes")

/-- A chain configuration given as JSON, with no blob schedule of its own when none is given.

The deposit contract address must be given, since no address is right for every chain.

No fork by block number may come after a fork by timestamp in the timeline, as EIP-6122 requires.

The chain ID is a 64-bit number, so a larger one is rejected rather than reduced. -/
def configOfJson (j : Json) : Result ChainConfig := do
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

/-- The name of the active fork of a configured chain at a block, if a fork is active.

The configuration is a `dict` with the keys and values of the JSON that other exports read. -/
def activeForkOf (args : PyValue × UInt64 × UInt64) : Result (Option String) := do
  let (config, number, timestamp) := args
  let config ← configOfJson config.toJson
  return (config.activeFork number.toNat timestamp.toNat).map (·.name)

/-- The name of the active fork of a configured chain at a block, or `None` when none is active.

The arguments are the configuration as a `dict`, the block number and the timestamp. -/
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
