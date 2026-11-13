module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Gossip.MessageId
public import EthLib.Networking.Gossip.Payload
public import EthLib.Networking.Gossip.Router
public import EthLib.Networking.Gossip.Rpc

/-!
# `Exports.Gossip`

C-ABI exports for the gossip message ID, payload, RPC and router.

The router exports receive an RPC, join and leave a topic, publish, and run the heartbeat.

The Python C extension calls them.

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
derive_py ControlExtensions
derive_py_laws ControlExtensions
derive_py PartialMessagesExtension
derive_py_laws PartialMessagesExtension
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

derive_py GossipsubParameters
derive_py_laws GossipsubParameters
derive_py ValidationResult
derive_py_laws ValidationResult
derive_py Standing
derive_py_laws Standing
derive_py MessageCache
derive_py_laws MessageCache
derive_py SeenCache
derive_py_laws SeenCache
derive_py RouterState
derive_py_laws RouterState
derive_py Out
derive_py_laws Out

/-- The gossipsub parameters, from the slot duration in milliseconds and the slots per epoch. -/
@[export eth_gossip_parameters]
def parametersExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((slotDurationMs, slotsPerEpoch) : Nat × Nat) =>
    (pure (gossipsubParameters slotDurationMs slotsPerEpoch) : Result GossipsubParameters)) args

/-- The standing of a peer, from a table; a peer missing from it has every flag false.

The first entry for a peer counts. -/
def standingOf (standings : List (PeerId × Standing)) (peer : PeerId) : Standing :=
  (standings.lookup peer).getD {}

/-- What the router does with one RPC, with its client choices given as tables.

The arguments come in this order.

- The name of a fork, whose rule gives the ID of every message, whatever the digest of its topic.
- The gossipsub parameters, then the two durations in milliseconds that the router takes.
- The standing of some peers; any other peer has every flag false.
- The validation result of some message IDs; any other message is ignored.
- The time in milliseconds, the peer that sent the RPC, the RPC and the state.

In each table, the first entry for a key counts.

One rule for every message fits a router whose topics all carry digests of forks with that rule.

Phase 0 has one rule, and every fork from Altair on has another. -/
def receiveRpcOf (args : String × GossipsubParameters × Nat × Nat × List (PeerId × Standing) ×
    List (MessageId × ValidationResult) × Nat × PeerId × Rpc × RouterState) :
    Result (RouterState × Out) := do
  let (fork, p, backoffMs, pruneBackoffMs, standings, results, now, src, rpc, s) := args
  let fork ← forkOfName fork.toUTF8
  let msgId (m : Message) : MessageId := messageId fork m.topic.toUTF8 m.data
  let standing := standingOf standings
  let validate (m : Message) : ValidationResult :=
    (results.lookup (msgId m)).getD (.ignore "no validation result")
  return receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s

/-- What the router does with one RPC, given a fork name, the parameters and the tables.

The result is the new state, and what the router sends and delivers. -/
@[export eth_gossip_receive_rpc]
def receiveRpcExport (args : PyValue) : Result PyValue :=
  pyExport receiveRpcOf args

derive_py ClientChoices
derive_py_laws ClientChoices

/-- The order of the peers by score in the exports, from a list of peers, the best first.

A peer missing from the list ranks after every listed peer. -/
def rankOf (ranking : List PeerId) : Rank := fun a b => ranking.idxOf a ≤ ranking.idxOf b

/-- The client choices, when they keep the bounds of gossipsub v1.1 for the parameters. -/
def checkChoices (p : GossipsubParameters) (c : ClientChoices) : Result ClientChoices :=
  have : Decidable (c.Valid p) := by unfold ClientChoices.Valid; infer_instance
  if c.Valid p then pure c else throw (0, "client choices outside the bounds of gossipsub v1.1")

/-- The router after this node joins a topic, and the GRAFTs it sends.

The arguments are the parameters, some standings, the time in milliseconds, the topic and the state.

The mesh takes the first peers of each candidate list. -/
def joinOf (args : GossipsubParameters × List (PeerId × Standing) × Nat × String × RouterState) :
    Result (RouterState × Out) := do
  let (p, standings, now, topic, s) := args
  return join p Select.first (standingOf standings) now topic s

/-- The router after this node joins a topic, given the parameters and some standings. -/
@[export eth_gossip_join]
def joinExport (args : PyValue) : Result PyValue :=
  pyExport joinOf args

/-- The router after this node leaves a topic, and the PRUNEs it sends.

The arguments are the parameters, the choices, the time in milliseconds, the topic and the state.

The parameters serve only to check the client choices. -/
def leaveOf (args : GossipsubParameters × ClientChoices × Nat × String × RouterState) :
    Result (RouterState × Out) := do
  let (p, c, now, topic, s) := args
  let c ← checkChoices p c
  return leave c now topic s

/-- The router after this node leaves a topic, given the parameters and the client choices. -/
@[export eth_gossip_leave]
def leaveExport (args : PyValue) : Result PyValue :=
  pyExport leaveOf args

/-- The router after this node publishes a message, and where the message goes.

The arguments come in this order.

- The name of a fork, whose rule gives the ID of the message, whatever the digest of its topic.
- The parameters, the client choices and the standing of some peers.
- The time in milliseconds, the message and the state.

On a topic not joined, without flood publishing, an empty fanout takes the first peers.

They are peers of the topic, neither explicit nor below the publish threshold.

Client choices outside the bounds of gossipsub v1.1 are rejected. -/
def publishOf (args : String × GossipsubParameters × ClientChoices × List (PeerId × Standing) ×
    Nat × Message × RouterState) : Result (RouterState × Out) := do
  let (fork, p, c, standings, now, m, s) := args
  let fork ← forkOfName fork.toUTF8
  let c ← checkChoices p c
  let msgId (m : Message) : MessageId := messageId fork m.topic.toUTF8 m.data
  return publish p c Select.first (standingOf standings) msgId now m s

/-- The router after this node publishes a message, given a fork name and some standings. -/
@[export eth_gossip_publish]
def publishExport (args : PyValue) : Result PyValue :=
  pyExport publishOf args

/-- The router after one heartbeat, and the control messages it sends.

The arguments come in this order.

- The parameters and the client choices.
- The peers in the order of their score, the best first; the others come after them.
- The standing of some peers, the time in milliseconds and the state.

Every choice among candidate peers takes the first ones, in the order of the candidates.

Client choices outside the bounds of gossipsub v1.1 are rejected. -/
def heartbeatOf (args : GossipsubParameters × ClientChoices × List PeerId ×
    List (PeerId × Standing) × Nat × RouterState) : Result (RouterState × Out) := do
  let (p, c, ranking, standings, now, s) := args
  let c ← checkChoices p c
  return heartbeat p c Select.first (rankOf ranking) (standingOf standings) now s

/-- The router after one heartbeat, given the parameters, the choices, a ranking and standings.
-/
@[export eth_gossip_heartbeat]
def heartbeatExport (args : PyValue) : Result PyValue :=
  pyExport heartbeatOf args

end EthLib.Networking.Gossip.Exports
