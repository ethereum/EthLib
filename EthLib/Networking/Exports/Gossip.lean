module

public import EthLib.Base.Exports
public import EthLib.Networking.Gossip.MessageId
public import EthLib.Networking.Gossip.Payload

/-!
# `Exports.Gossip`

C-ABI exports for the gossip message ID and payload, callable from the Python C extension.
-/

public section

namespace EthLib.Networking.Gossip.Exports

open EthLib.Exports (Result forkOfName)

/-- The message ID of a message on a topic of a named fork, from the topic and the data. -/
@[export eth_gossip_message_id]
def messageIdExport (fork topic data : ByteArray) : Result ByteArray := do
  return messageId (← forkOfName fork) topic data

/-- The SSZ bytes of the data of a gossip message, given the size bound of its SSZ type. -/
@[export eth_gossip_decode_payload]
def decodePayloadExport (typeBound : UInt64) (data : ByteArray) : Result ByteArray :=
  (decodePayload typeBound data).mapError fun e =>
    (e.code, s!"gossip payload rejected: {reprStr e}")

end EthLib.Networking.Gossip.Exports
