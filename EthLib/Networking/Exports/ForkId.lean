module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Devp2p.ForkId

/-!
# `Exports.ForkId`

C-ABI exports for the fork identifier, callable from the Python C extension.

A remote fork identifier, and the output of the encoder, is its RLP list `[FORK_HASH, FORK_NEXT]`.

A schedule crosses it as the RLP list `[genesis-hash, genesis-time, merge-fork, forks]`.

- `merge-fork` is an empty list, or a list of the one block of `FORK_NEXT_VALUE`.
- `forks` holds `[name, kind, value]` for each fork, with kind 0 for a block and 1 for a time.
- A fork name is written as its case is, such as `homestead`.

A block number and a timestamp cross the boundary as 64-bit integers.

The fork identifier of a node comes back as typed Python values: its hash and its next fork.

Two exports write a schedule and a fork identifier in RLP, from typed Python values.

An input that the export rejects before the fork identifier rules has code 0.
-/

public section

namespace EthLib.Networking.Devp2p.Exports

open EthLib.Base
open EthLib.Exports (Result PyValue forkOfName pyExport)
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
  -- The chain ID and the deposit contract play no part in a fork ID.
  let config : ChainConfig :=
    { chainId := 0, depositContractAddress := Vector.replicate 20 0, activations := activations }
  return ⟨hash, time, config, mergeForkBlock⟩

/-- The hash and the next fork of a fork identifier. -/
def forkIdFields (id : ForkId) : Vector UInt8 4 × UInt64 :=
  (id.hash, id.next)

/-- The fork identifier of a node with a schedule in RLP at a head: its hash and its next fork. -/
def forkIdOf (args : ByteArray × UInt64 × UInt64) : Result (Vector UInt8 4 × UInt64) := do
  let (schedule, number, timestamp) := args
  let s ← readSchedule schedule
  return forkIdFields (s.forkId number.toNat timestamp.toNat)

/-- The fork identifier of a node with a schedule at a head: its hash and its next fork.

The arguments are the schedule in RLP, the block number and the timestamp of the head. -/
@[export eth_fork_id]
def forkIdExport (args : PyValue) : Result PyValue :=
  pyExport forkIdOf args

/-- The fork identifier of a mainnet node at a head: its hash and its next fork.

The arguments are the block number and the timestamp of the head. -/
@[export eth_mainnet_fork_id]
def mainnetForkIdExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((number, timestamp) : UInt64 × UInt64) =>
    pure (forkIdFields (Schedule.mainnet.forkId number.toNat timestamp.toNat))) args

/-- The RLP schedule `[genesis-hash, genesis-time, merge-fork, forks]` of a chain.

Each fork is its name, its kind, 0 for a block and 1 for a time, and its block or time.

The kind is written as given, and the reader of a schedule rejects any other. -/
def scheduleOf (args : ByteArray × Nat × Option Nat × List (String × Nat × Nat)) :
    Result ByteArray := do
  let (hash, time, merge, forks) := args
  let item : Item := .list [.bytes hash, Codec.toItem time, .list (merge.toList.map Codec.toItem),
    .list (forks.map fun (name, kind, value) =>
      .list [.bytes name.toUTF8, Codec.toItem kind, Codec.toItem value])]
  (Serialization.Rlp.encode item).mapError fun _ => (0, "schedule has no RLP encoding")

/-- The RLP schedule `[genesis-hash, genesis-time, merge-fork, forks]` of a chain.

The arguments are the genesis hash, the genesis time, the merge fork block or `None`, and the forks.

Each fork is its name, its kind, 0 for a block and 1 for a time, and its block or time. -/
@[export eth_fork_id_schedule]
def scheduleExport (args : PyValue) : Result PyValue :=
  pyExport scheduleOf args

/-- The RLP fork identifier `[FORK_HASH, FORK_NEXT]`. -/
def encodeOf (args : Vector UInt8 4 × UInt64) : Result ByteArray := do
  let (hash, next) := args
  (Codec.encode (⟨hash, next⟩ : ForkId)).mapError fun _ => (0, "too large")

/-- The RLP fork identifier `[FORK_HASH, FORK_NEXT]`, from its 4-byte hash and its next fork. -/
@[export eth_fork_id_encode]
def encodeExport (args : PyValue) : Result PyValue :=
  pyExport encodeOf args

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
