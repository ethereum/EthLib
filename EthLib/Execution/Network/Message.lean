module

public import EthLib.Execution.Network.Status

/-!
# `Execution.Network.Message`

The messages of the eth capability, read by their message ID and the negotiated version.

A message on the wire is its message ID, then the RLP list of its data, as in
"Message Encoding" of [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#message-encoding

Here the ID is relative to the capability: Status is 0x00 whatever offset RLPx gives eth.

A message whose ID the version does not use is rejected.

So is a message that EthLib does not read yet: today only Status and BlockRangeUpdate.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Serialization.Rlp

/-- A message of the eth capability. -/
inductive Message where
  /-- Status (0x00), the handshake. -/
  | status (s : Status)
  /-- BlockRangeUpdate (0x11), from eth/69 on. -/
  | blockRangeUpdate (r : BlockRange)
  deriving DecidableEq, Repr

/-- Every way a message can be rejected. -/
inductive EthError where
  /-- The version does not use the message ID, or EthLib does not read that message yet. -/
  | unknownId (id : Nat)
  /-- The data is not RLP of the shape that the message asks for. -/
  | rlp (error : RlpError)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EthError.code : EthError → UInt32
  | .unknownId _ => 1
  | .rlp _ => 2

namespace Message

/-- The message ID. -/
def id : Message → Nat
  | status _ => STATUS_ID
  | blockRangeUpdate _ => BLOCK_RANGE_UPDATE_ID

/-- The data of the message, as one RLP item. -/
def toItem : Message → Item
  | status s => s.toItem
  | blockRangeUpdate r => Codec.toItem r

/-- The message with the ID `id` and the data `item`, on the version `version`.

BlockRangeUpdate exists from eth/69 on. -/
def ofItem (version : EthVersion) (id : Nat) (item : Item) : Except EthError Message :=
  if id = STATUS_ID then (status <$> Status.ofItem version item).mapError .rlp
  else if id = BLOCK_RANGE_UPDATE_ID ∧ EthVersion.eth69 ≤ version then
    (blockRangeUpdate <$> Codec.ofItem item).mapError .rlp
  else .error (.unknownId id)

/-- The message with the ID `id` whose data is the RLP encoding `data`. -/
def decode (version : EthVersion) (id : Nat) (data : ByteArray) : Except EthError Message := do
  ofItem version id (← (Serialization.Rlp.decode data).mapError .rlp)

/-- The RLP encoding of the data of a message. -/
def encode (m : Message) : Except EthError ByteArray :=
  (Serialization.Rlp.encode m.toItem).mapError .rlp

end Message

end EthLib.Execution.Network
