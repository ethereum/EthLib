module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Gossip.MessageId
public import EthLib.Networking.Gossip.Payload
public import EthLib.Networking.Gossip.Rpc

/-!
# `Exports.Gossip`

C-ABI exports for the gossip message ID, payload and RPC, callable from the Python C extension.

The message ID takes typed values: the name of a fork as a `str`, then the topic and the data.

An RPC crosses as a `dict` whose keys are the field names of its Lean structure, in snake case.

Each nested message crosses the same way, and each list as a `list`.

Every field has its key, in both directions.
-/

public section

namespace EthLib.Networking.Gossip.Exports

open EthLib.Exports (Result PyValue forkOfName pyExport)

derive_py SubOpts
derive_py_laws SubOpts
derive_py Message
derive_py_laws Message
derive_py IHave
derive_py_laws IHave
derive_py IWant
derive_py_laws IWant
derive_py Graft
derive_py_laws Graft
derive_py PeerInfo
derive_py_laws PeerInfo
derive_py Prune
derive_py_laws Prune
derive_py IDontWant
derive_py_laws IDontWant
derive_py Control
derive_py_laws Control
derive_py Rpc
derive_py_laws Rpc

/-- The message ID of a message on a topic of a named fork, from the topic and the data. -/
def messageIdOf (args : String × ByteArray × ByteArray) : Result (Vector UInt8 20) := do
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

/-- The RPC that the bytes encode, under the `StrictNoSign` policy. -/
@[export eth_gossip_rpc_decode]
def rpcDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) =>
    (decodeRpc data).mapError fun e => (e.code, s!"gossip RPC rejected: {reprStr e}")) args

/-- The bytes of an RPC. -/
@[export eth_gossip_rpc_encode]
def rpcEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (rpc : Rpc) => (pure rpc.encode : Result ByteArray)) args

end EthLib.Networking.Gossip.Exports
