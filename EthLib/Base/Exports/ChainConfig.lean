module

public import EthLib.Base.ChainConfig
public import EthLib.Base.Exports
public import Lean.Data.Json

/-!
# Exports: the active fork of a network

The C exports of the active fork of mainnet and of Hoodi, for the Python bindings.

A block number and a timestamp cross the boundary as 64-bit integers, as EIP-6122 reads them.

A fork crosses it as its name in UTF-8, such as `bellatrix`.

A chain configuration crosses it as JSON: its chain ID, its activations and its blob schedules.

An activation is a fork name, `block` or `time`, and a number.

A blob schedule is `block` or `time`, a number, the target, the maximum and the update fraction.
-/

public section

namespace EthLib.Base.ChainConfig.Exports

/-- The name of the active fork of mainnet at a block, or no bytes when no fork is active. -/
@[export eth_mainnet_active_fork]
def mainnetActiveForkExport (number timestamp : UInt64) : ByteArray :=
  match mainnet.activeFork number.toNat timestamp.toNat with
  | some fork => fork.name.toUTF8
  | none => .empty

/-- The name of the active fork of Hoodi at a block, or no bytes when no fork is active. -/
@[export eth_hoodi_active_fork]
def hoodiActiveForkExport (number timestamp : UInt64) : ByteArray :=
  match hoodi.activeFork number.toNat timestamp.toNat with
  | some fork => fork.name.toUTF8
  | none => .empty

open Lean (Json)
open EthLib.Exports (Result forkOfName)

/-- The JSON value of some UTF-8 text. -/
def parseJson (what : String) (text : ByteArray) : Result Json := do
  let some text := String.fromUTF8? text | throw (0, s!"{what} is not UTF-8")
  match Json.parse text with
  | .ok j => pure j
  | .error e => throw (0, s!"{what} is not JSON: {e}")

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

/-- A chain configuration given as JSON, with no blob schedule of its own when none is given. -/
def configOfJson (j : Json) : Result ChainConfig := do
  let some chainId := (j.getObjValAs? Nat "chainId").toOption | throw (0, "config: no chainId")
  let .arr activations := j.getObjValD "activations" | throw (0, "config: no activations")
  let activations ← activations.toList.mapM activationOfJson
  let schedules ← match j.getObjValD "blobSchedules" with
    | .arr entries => entries.toList.mapM blobScheduleOfJson
    | .null => pure []
    | _ => throw (0, "config: blobSchedules is not an array")
  return { chainId := BitVec.ofNat 256 chainId, activations, blobSchedules := schedules }

end EthLib.Base.ChainConfig.Exports
