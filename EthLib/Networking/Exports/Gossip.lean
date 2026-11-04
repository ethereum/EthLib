module

public import EthLib.Networking.Gossip.MessageId

/-!
# `Exports.Gossip`

C-ABI exports for the gossip message ID, callable from the Python C extension.
-/

public section

namespace EthLib.Networking.Gossip.Exports

/-- The message ID of Phase 0, from the data of the message. -/
@[export eth_gossip_message_id_phase0]
def messageIdPhase0Export (data : ByteArray) : IO ByteArray :=
  pure (Phase0.messageId data)

/-- The message ID from Altair on, from the topic and the data of the message. -/
@[export eth_gossip_message_id_altair]
def messageIdAltairExport (topic data : ByteArray) : IO ByteArray :=
  pure (Altair.messageId topic data)

end EthLib.Networking.Gossip.Exports
