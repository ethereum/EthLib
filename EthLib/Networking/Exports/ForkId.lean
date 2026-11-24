module

public import EthLib.Base.Exports.PyValue
public import EthLib.Networking.Devp2p.ForkId

/-!
# `Exports.ForkId`

C-ABI exports for the fork identifier, callable from the Python C extension.

A remote fork identifier, and the output of the encoder, is its RLP list `[FORK_HASH, FORK_NEXT]`.

An input that the export rejects before the fork identifier rules has code 0.
-/

public section

namespace EthLib.Networking.Devp2p.Exports

open EthLib.Base
open EthLib.Exports (ExportError Result PyValue UnreadArgument forkOfName pyExport rejectArgument
  toResult)
open EthLib.Serialization.Rlp

/-- A message for a refusal, phrased for someone reading a Python traceback. -/
def forkIdMessage : ForkIdError → String
  | .remoteStale => "remote is on an earlier fork and announces another next fork"
  | .localIncompatibleOrStale => "chains are incompatible, or the local node is stale"

/-- A refused fork identifier reaches Python with the code of its rule, and a message for it. -/
instance : ExportError ForkIdError where
  code := ForkIdError.code
  message := forkIdMessage

/-- The activation of one fork in `[name, kind, value]`.

The value must be below `2^64`, since the fork identifier holds it in 64 bits. -/
def readActivation (item : Item) : Result (Fork × Activation) := do
  let .ok [name, kind, value] := item.fields 3 |
    rejectArgument none "a fork is not [name, kind, value]"
  let .ok name := name.toBytes | rejectArgument none "a fork name is not a byte string"
  let fork ← forkOfName name
  let .ok (value : Nat) := Codec.ofItem value | rejectArgument none "a fork value is not a scalar"
  unless value < ACTIVATION_BOUND do rejectArgument none "a fork value is not below 2^64"
  match (Codec.ofItem kind : Except RlpError Nat) with
  | .ok 0 => return (fork, .block value)
  | .ok 1 => return (fork, .time value)
  | _ => rejectArgument none "a fork kind is not 0 or 1"

/-- The schedule in the RLP list `[genesis-hash, genesis-time, merge-fork, forks]`.

- `merge-fork` is an empty list, or a list of the one block of `FORK_NEXT_VALUE`.
- `forks` holds `[name, kind, value]` for each fork, with kind 0 for a block and 1 for a time.
- A fork name is written as its case is, such as `homestead`.

The chain ID does not enter the fork identifier, so the configuration has chain ID 0. -/
def readSchedule (bytes : ByteArray) : Result Schedule := do
  let .ok item := Serialization.Rlp.decode bytes |
    rejectArgument none "schedule is not one RLP item"
  let .ok [hash, time, merge, forks] := item.fields 4 |
    rejectArgument none "schedule is not [genesis-hash, genesis-time, merge-fork, forks]"
  let .ok (hash : Hash32) := Codec.ofItem hash | rejectArgument none "genesis hash is not 32 bytes"
  let .ok (time : Nat) := Codec.ofItem time | rejectArgument none "genesis time is not a scalar"
  let mergeForkBlock ← match (Codec.ofItem merge : Except RlpError (List Nat)) with
    | .ok [] => pure none
    | .ok [n] =>
      -- The merge fork block is a fork block of the identifier, so it has the same bound.
      unless n < ACTIVATION_BOUND do rejectArgument none "merge fork is not below 2^64"
      pure (some n)
    | _ => rejectArgument none "merge fork is not a list of at most one block"
  let .ok forks := forks.toItems | rejectArgument none "forks are not a list"
  let activations ← forks.mapM readActivation
  -- The chain ID and the deposit contract play no part in a fork ID.
  let config : ChainConfig :=
    { chainId := 0, depositContractAddress := Vector.replicate 20 0, activations := activations }
  return ⟨hash, time, config, mergeForkBlock⟩

/-- The hash and the next fork of a fork identifier.

The fork identifier of a node comes back to Python as these typed values. -/
def forkIdFields (id : ForkId) : Vector UInt8 4 × UInt64 :=
  (id.hash, id.next)

/-- The fork identifier of a node with a schedule in RLP at a head: its hash and its next fork. -/
def forkIdOf (args : ByteArray × UInt64 × UInt64) : Result (Vector UInt8 4 × UInt64) := do
  -- A block number and a timestamp cross the boundary as 64-bit integers.
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
  toResult none ((Serialization.Rlp.encode item).mapError fun _ =>
    UnreadArgument.mk "schedule has no RLP encoding")

/-- The RLP schedule `[genesis-hash, genesis-time, merge-fork, forks]` of a chain.

The arguments are the genesis hash, the genesis time, the merge fork block or `None`, and the forks.

Each fork is its name, its kind, 0 for a block and 1 for a time, and its block or time.

It and the encoder of a fork identifier write RLP from typed Python values. -/
@[export eth_fork_id_schedule]
def scheduleExport (args : PyValue) : Result PyValue :=
  pyExport scheduleOf args

/-- The RLP fork identifier `[FORK_HASH, FORK_NEXT]`. -/
def encodeOf (args : Vector UInt8 4 × UInt64) : Result ByteArray := do
  let (hash, next) := args
  toResult none ((Codec.encode (⟨hash, next⟩ : ForkId)).mapError fun _ =>
    UnreadArgument.mk "too large")

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
  let .ok (id : ForkId) := Codec.decode remote |
    rejectArgument none "remote is not an RLP fork identifier"
  toResult none ((s.validate number.toNat timestamp.toNat id).map fun _ => true)

end EthLib.Networking.Devp2p.Exports
