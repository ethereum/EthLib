module

public import EthLib.Base.Hash32
public import EthLib.Execution.Network.Protocol
public import EthLib.Networking.Devp2p.ForkId

/-!
# `Execution.Network.Status`

The handshake of the eth capability, Status (0x00), and the notice BlockRangeUpdate (0x11).

The source is "Status (0x00)" and "BlockRangeUpdate (0x11)" of [`caps/eth.md`][eth], with the
Status of eth/68 from [EIP-7642](https://eips.ethereum.org/EIPS/eip-7642#status-message-changes).

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#status-0x00

- eth/68: `[version, networkid, td, blockhash, genesis, forkid]`.
- eth/69 on: `[version, networkid, genesis, forkid, earliest, latest, latestHash]`.

From eth/69 on, a node announces the blocks it can serve, in Status and in BlockRangeUpdate.

Each peer validates the fork identifier of the other, and disconnects when they are
incompatible, as [EIP-2364](https://eips.ethereum.org/EIPS/eip-2364#specification) requires.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp

/-- The message ID of Status. -/
def STATUS_ID : Nat := 0x00

/-- The message ID of BlockRangeUpdate, from eth/69 on. -/
def BLOCK_RANGE_UPDATE_ID : Nat := 0x11

/-- The blocks that a node serves: `[earliest, latest, latestHash]`.

It serves the bodies and the receipts of each block from `earliest` to `latest`.

It serves the headers of every block from genesis on. -/
structure BlockRange where
  /-- The number of the earliest block whose body and receipts the node serves. -/
  earliest : Nat
  /-- The number of the latest block that the node has. -/
  latest : Nat
  /-- The hash of that latest block. -/
  latestHash : Hash32
  deriving DecidableEq, Repr

namespace BlockRange

/-- The items of a range, `earliest`, `latest` and `latestHash`. -/
def items (r : BlockRange) : List Item :=
  [Codec.toItem r.earliest, Codec.toItem r.latest, Codec.toItem r.latestHash]

/-- A range as the RLP list `[earliest, latest, latestHash]`, the data of BlockRangeUpdate. -/
instance : Codec BlockRange where
  toItem r := .list r.items
  ofItem item := do
    match ← item.fields 3 with
    | [e, l, h] => return ⟨← e.field 0, ← l.field 1, ← h.field 2⟩
    | items => throw (.wrongFieldCount 3 items.length)

/-- A range is valid when its earliest block is not after its latest block.

A peer that announces `earliest > latest` should be disconnected. -/
def Valid (r : BlockRange) : Prop := r.earliest ≤ r.latest

instance (r : BlockRange) : Decidable r.Valid := Nat.decLe _ _

end BlockRange

/-- The Status message of a version. -/
inductive Status where
  /-- eth/68: `[version, networkid, td, blockhash, genesis, forkid]`.

  `td` is the total difficulty of the best block, whose hash is `blockhash`. -/
  | eth68 (version networkId totalDifficulty : Nat) (blockHash genesis : Hash32) (forkId : ForkId)
  /-- eth/69 on: `[version, networkid, genesis, forkid, earliest, latest, latestHash]`. -/
  | eth69 (version networkId : Nat) (genesis : Hash32) (forkId : ForkId) (range : BlockRange)
  deriving DecidableEq, Repr

namespace Status

/-- The protocol version that the message announces. -/
def version : Status → Nat
  | eth68 v .. | eth69 v .. => v

/-- The fork identifier that the message announces. -/
def forkId : Status → ForkId
  | eth68 _ _ _ _ _ id | eth69 _ _ _ id _ => id

/-- The message as an RLP list, in the field order of its version. -/
def toItem : Status → Item
  | eth68 v n td h g id =>
    .list [Codec.toItem v, Codec.toItem n, Codec.toItem td, Codec.toItem h, Codec.toItem g,
      Codec.toItem id]
  | eth69 v n g id r => .list ([Codec.toItem v, Codec.toItem n, Codec.toItem g, Codec.toItem id] ++
      r.items)

/-- The Status message of a version in an RLP list.

eth/68 reads six fields, and every later version reads seven, so each rejects the other form. -/
def ofItem (version : EthVersion) (item : Item) : Except RlpError Status :=
  if version = .eth68 then do
    match ← item.fields 6 with
    | [v, n, td, h, g, id] =>
      return eth68 (← v.field 0) (← n.field 1) (← td.field 2) (← h.field 3) (← g.field 4)
        (← id.field 5)
    | items => throw (.wrongFieldCount 6 items.length)
  else do
    match ← item.fields 7 with
    | [v, n, g, id, e, l, h] =>
      return eth69 (← v.field 0) (← n.field 1) (← g.field 2) (← id.field 3)
        ⟨← e.field 4, ← l.field 5, ← h.field 6⟩
    | items => throw (.wrongFieldCount 7 items.length)

end Status

/-- Why a node refuses the Status of a peer. -/
inductive StatusError where
  /-- The message announces another version than the one the peers negotiated. -/
  | version (announced : Nat)
  /-- The fork identifier of the peer is incompatible. -/
  | forkId (error : ForkIdError)
  /-- The announced range starts after it ends. -/
  | range (earliest latest : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 101, above every code of a message error, so that the two never meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def StatusError.code : StatusError → UInt32
  | .version _ => 101
  | .forkId _ => 102
  | .range .. => 103

/--
Whether a node accepts the Status of a peer, on the negotiated version `version`.

The node has the schedule `s`, and its head has a block number and a timestamp.

- The announced version must be the negotiated one.
- The fork identifier must pass the rules of EIP-2124.
- From eth/69 on, the announced range must be valid.

The network ID and the genesis hash are left to the node, since no rule of the specification
reads them.
-/
def checkStatus (version : EthVersion) (s : Schedule) (number timestamp : Nat)
    (status : Status) : Except StatusError Unit := do
  if status.version ≠ version.number then throw (.version status.version)
  (s.validate number timestamp status.forkId).mapError .forkId
  match status with
  | .eth68 .. => pure ()
  | .eth69 _ _ _ _ r => if r.Valid then pure () else throw (.range r.earliest r.latest)

end EthLib.Execution.Network
