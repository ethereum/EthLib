module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Gossip.MessageId
public import EthLib.Networking.Gossip.Payload

/-!
# `Exports.Gossip`

C-ABI exports for the gossip message ID and payload, callable from the Python C extension.

The message ID takes typed values: the name of a fork as a `str`, then the topic and the data.
-/

public section

namespace EthLib.Networking.Gossip.Exports

open EthLib.Exports (Result PyValue forkOfName pyExport)

/-- The message ID of a message on a topic of a named fork, from the topic and the data. -/
def messageIdOf (args : String × ByteArray × ByteArray) : Result ByteArray := do
  let (fork, topic, data) := args
  return messageId (← forkOfName fork.toUTF8) topic data

/-- The message ID of a message on a topic of a named fork.

The arguments are the name of the fork, the topic and the data. -/
@[export eth_gossip_message_id]
def messageIdExport (args : PyValue) : Result PyValue :=
  pyExport messageIdOf args

/-- The SSZ bytes of the data of a gossip message, given the size bound of its SSZ type. -/
@[export eth_gossip_decode_payload]
def decodePayloadExport (typeBound : UInt64) (data : ByteArray) : Result ByteArray :=
  (decodePayload typeBound data).mapError fun e =>
    (e.code, s!"gossip payload rejected: {reprStr e}")

end EthLib.Networking.Gossip.Exports
