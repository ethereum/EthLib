module

public import EthLib.Networking.ReqResp.Encoding
public import EthLib.Networking.Snappy.Block

/-!
# `Networking.Gossip.Payload`

The payload of a gossip message, and the size limits on it.

The data field of a gossip message is the SSZ bytes of the message, as one Snappy block.

A client rejects data longer than the worst-case compression of the largest payload.

It also rejects a payload above the payload cap or the size bound of the message type.

The payload cap is a value of the network configuration, and the limits are the same at every fork.
-/

@[expose] public section

namespace EthLib.Networking.Gossip

open EthLib.Base (ArithError)
open EthLib.Networking.ReqResp (maxCompressedLen)

/-- Every way the data of a gossip message can be rejected. -/
inductive PayloadError where
  /-- The bound on the compressed size is 2^64 or more. -/
  | arith (error : ArithError)
  /-- The data is longer than the worst-case compression of the largest payload. -/
  | compressedTooLong (size bound : Nat)
  /-- The data is not a valid Snappy block. -/
  | snappy (error : Snappy.SnappyError)
  /-- The payload is above the payload cap or the size bound of the message type. -/
  | payloadTooLong (size bound : Nat)
  deriving Repr, DecidableEq

/--
The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning.
-/
def PayloadError.code : PayloadError → UInt32
  | .arith _ => 1
  | .compressedTooLong .. => 2
  | .snappy _ => 3
  | .payloadTooLong .. => 4

/--
The SSZ bytes of the data of a gossip message, given the payload cap and the size bound of its type.

The caller deserializes the bytes, since it knows their SSZ type.
-/
def decodePayload (maxPayloadSize typeBound : UInt64) (data : ByteArray) :
    Except PayloadError ByteArray := do
  -- The data has at most `32 + n + n / 6` bytes, for the payload cap `n`.
  let compressedBound ← (maxCompressedLen maxPayloadSize).mapError .arith
  if compressedBound.toNat < data.size then
    throw (.compressedTooLong data.size compressedBound.toNat)
  -- The bound on the payload is the smaller of the cap and the size bound of the type.
  let bound := (min typeBound maxPayloadSize).toNat
  -- The preamble declares the payload length, so a long payload is rejected unread.
  --
  -- This early check is EthLib's choice.
  --
  -- A valid block decompresses to exactly its declared length, so such data fails a later check.
  if let .ok declared := Snappy.declaredLength data then
    if bound < declared then throw (.payloadTooLong declared bound)
  -- The data is one Snappy block, which must decompress.
  let payload ← (Snappy.decompress data).mapError .snappy
  -- The payload has at most as many bytes as the bound.
  if bound < payload.size then throw (.payloadTooLong payload.size bound)
  return payload

end EthLib.Networking.Gossip
