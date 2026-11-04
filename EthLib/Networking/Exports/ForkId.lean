module

public import EthLib.Base.Exports
public import EthLib.Networking.Devp2p.ForkId

/-!
# `Exports.ForkId`

C-ABI exports for the fork identifier, callable from the Python C extension.

A fork identifier crosses the boundary as its RLP list `[FORK_HASH, FORK_NEXT]`.

A schedule crosses it as the RLP list `[genesis-hash, genesis-time, merge-fork, forks]`.

- `merge-fork` is an empty list, or a list of the one block of `FORK_NEXT_VALUE`.
- `forks` holds `[name, kind, value]` for each fork, with kind 0 for a block and 1 for a time.
- A fork name is written as its case is, such as `homestead`.

A block number and a timestamp cross the boundary as 64-bit integers.

An input that the export rejects before the fork identifier rules has code 0.
-/

public section

namespace EthLib.Networking.Devp2p.Exports

open EthLib.Base
open EthLib.Exports (Result forkOfName)
open EthLib.Serialization.Rlp

/-- A message for a refusal, phrased for someone reading a Python traceback. -/
def forkIdMessage : ForkIdError → String
  | .remoteStale => "remote is on an earlier fork and announces another next fork"
  | .localIncompatibleOrStale => "chains are incompatible, or the local node is stale"

/-- The activation of one fork in `[name, kind, value]`. -/
def readActivation (item : Item) : Result (Fork × Activation) := do
  let .ok [name, kind, value] := item.fields 3 | throw (0, "a fork is not [name, kind, value]")
  let .ok name := name.toBytes | throw (0, "a fork name is not a byte string")
  let fork ← forkOfName name
  let .ok (value : Nat) := Codec.ofItem value | throw (0, "a fork value is not a scalar")
  match (Codec.ofItem kind : Except RlpError Nat) with
  | .ok 0 => return (fork, .block value)
  | .ok 1 => return (fork, .time value)
  | _ => throw (0, "a fork kind is not 0 or 1")

/-- The schedule in the RLP list `[genesis-hash, genesis-time, merge-fork, forks]`.

The chain ID does not enter the fork identifier, so the configuration has chain ID 0. -/
def readSchedule (bytes : ByteArray) : Result Schedule := do
  let .ok item := Serialization.Rlp.decode bytes | throw (0, "schedule is not one RLP item")
  let .ok [hash, time, merge, forks] := item.fields 4 |
    throw (0, "schedule is not [genesis-hash, genesis-time, merge-fork, forks]")
  let .ok (hash : Hash32) := Codec.ofItem hash | throw (0, "genesis hash is not 32 bytes")
  let .ok (time : Nat) := Codec.ofItem time | throw (0, "genesis time is not a scalar")
  let mergeForkBlock ← match (Codec.ofItem merge : Except RlpError (List Nat)) with
    | .ok [] => pure none
    | .ok [n] => pure (some n)
    | _ => throw (0, "merge fork is not a list of at most one block")
  let .ok forks := forks.toItems | throw (0, "forks are not a list")
  let activations ← forks.mapM readActivation
  return ⟨hash, time, ⟨0, activations⟩, mergeForkBlock⟩

/-- The fork identifier, as RLP, of a node with the schedule `schedule` at a head. -/
@[export eth_fork_id]
def forkIdExport (schedule : ByteArray) (number timestamp : UInt64) : Result ByteArray := do
  let s ← readSchedule schedule
  (Codec.encode (s.forkId number.toNat timestamp.toNat)).mapError fun _ => (0, "too large")

/-- The fork identifier, as RLP, of a mainnet node at a head. -/
@[export eth_mainnet_fork_id]
def mainnetForkIdExport (number timestamp : UInt64) : Result ByteArray :=
  (Codec.encode (Schedule.mainnet.forkId number.toNat timestamp.toNat)).mapError
    fun _ => (0, "too large")

/-- Whether a node with the schedule `schedule` at a head accepts the RLP identifier `remote`.

It returns true on acceptance, and the code of the rule that refuses otherwise. -/
@[export eth_fork_id_validate]
def validateExport (schedule : ByteArray) (number timestamp : UInt64) (remote : ByteArray) :
    Result Bool := do
  let s ← readSchedule schedule
  let .ok (id : ForkId) := Codec.decode remote | throw (0, "remote is not an RLP fork identifier")
  (s.validate number.toNat timestamp.toNat id).map (fun _ => true)
    |>.mapError fun e => (e.code, forkIdMessage e)

end EthLib.Networking.Devp2p.Exports
