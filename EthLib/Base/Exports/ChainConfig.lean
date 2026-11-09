module

public import EthLib.Base.ChainConfig
public import EthLib.Base.Hex
public import EthLib.Base.Exports.Proofs.PyValue
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
-/

public section

namespace EthLib.Base.ChainConfig.Exports

open EthLib.Exports (Result PyValue pyExport forkOfName)

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

/-- An activation from its kind, `block` or `time`, and its number. -/
def activationOf (kind : String) (n : Json) : Result Activation := do
  let some n := n.getNat?.toOption | throw (0, "an activation has no number")
  match kind with
  | "block" => pure (.block n)
  | "time" => pure (.time n)
  | _ => throw (0, s!"no activation kind {kind}")

/-- One activation of a configuration: a fork name, `block` or `time`, and a number. -/
def activationOfJson (j : Json) : Result (Fork × Activation) := do
  let .arr #[.str name, .str kind, n] := j | throw (0, "an activation is not [fork, kind, n]")
  return (← forkOfName name.toUTF8, ← activationOf kind n)

/-- One blob schedule of a configuration: its activation, target, maximum and update fraction.

The target must be at most the maximum, and the maximum and the fraction must be positive. -/
def blobScheduleOfJson (j : Json) : Result (Activation × BlobSchedule) := do
  let .arr #[.str kind, n, target, max, fraction] := j
    | throw (0, "a blob schedule is not [kind, n, target, max, fraction]")
  let some target := target.getNat?.toOption | throw (0, "a blob schedule has no target")
  let some max := max.getNat?.toOption | throw (0, "a blob schedule has no maximum")
  let some fraction := fraction.getNat?.toOption | throw (0, "a blob schedule has no fraction")
  if h : target ≤ max ∧ 0 < max ∧ 0 < fraction then
    return (← activationOf kind n, ⟨target, max, fraction, h.1, h.2.1, h.2.2⟩)
  else throw (0, "a blob schedule needs target ≤ max, 0 < max and 0 < update fraction")

/-- The deposit contract address of a configuration: `0x` and forty hex digits. -/
def depositContractOfJson (j : Json) : Result Address := do
  let text ← match j with
    | .str text => pure text
    | .null => throw (0, "config: no depositContractAddress")
    | _ => throw (0, "config: depositContractAddress is not text")
  let '0' :: 'x' :: digits := text.toList
    | throw (0, "config: depositContractAddress does not start with 0x")
  unless digits.length = 40 do throw (0, "config: depositContractAddress is not forty hex digits")
  let some bytes := hexBytes? digits
    | throw (0, "config: depositContractAddress is not hex")
  if h : bytes.data.size = 20 then return ⟨bytes.data, h⟩
  else throw (0, "config: depositContractAddress is not 20 bytes")

/-- A chain configuration given as JSON, with no blob schedule of its own when none is given.

The deposit contract address must be given, since no address is right for every chain.

No fork by block number may come after a fork by timestamp in the timeline, as EIP-6122 requires.

The chain ID is a 64-bit number, so a larger one is rejected rather than reduced. -/
def configOfJson (j : Json) : Result ChainConfig := do
  let some chainId := (j.getObjValAs? Nat "chainId").toOption | throw (0, "config: no chainId")
  unless chainId < 2 ^ 64 do throw (0, "config: chainId is not below 2^64")
  let depositContractAddress ← depositContractOfJson (j.getObjValD "depositContractAddress")
  let .arr activations := j.getObjValD "activations" | throw (0, "config: no activations")
  let activations ← activations.toList.mapM activationOfJson
  -- EIP-6122 puts forks by time after forks by block, so none comes before a fork by block.
  unless activationsOrdered activations do
    throw (0, "config: a fork by block comes after a fork by time")
  let schedules ← match j.getObjValD "blobSchedules" with
    | .arr entries => entries.toList.mapM blobScheduleOfJson
    | .null => pure []
    | _ => throw (0, "config: blobSchedules is not an array")
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

end EthLib.Base.ChainConfig.Exports
