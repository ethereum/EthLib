module

public import EthLib.Networking.Discv5.Distance
public import EthLib.Networking.Discv5.Message
public import EthLib.Networking.Enr.V4

/-!
# `Networking.Discv5.Exchange`

The rules that relate a discv5 answer to its request, from "Protocol Messages" of [the wire spec].

- The recipient of a request "must mirror" its request ID in the answer.
- PING is answered by PONG, FINDNODE by NODES, and TALKREQ by TALKRESP.
- The requester "should verify" that the records of NODES are at the requested distances.
- A node "may place a limit" on `total`, the number of NODES messages of one answer.
- A TALKREQ for an unknown protocol "must" get a TALKRESP with an empty response.

A distance is a logarithmic distance from the node that received the FINDNODE.

Distance 0 asks for the record of that node itself.

Topic discovery, with REGTOPIC and TOPICQUERY, is not covered here.

[the wire spec]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv5/discv5-wire.md#L156-L239
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Serialization.Rlp

namespace Message

/-- The type of the answer to a request.

It is none for a response, and for the topic requests, whose answers are not covered here. -/
def answerType : Message → Option UInt8
  | .ping .. => some 2
  | .findnode .. => some 4
  | .talkreq .. => some 6
  | _ => none

end Message

/-- Whether a message answers a request: it has the type of the answer and the same request ID.
-/
def answersRequest (request answer : Message) : Bool :=
  request.answerType == some answer.type && request.requestId == answer.requestId

/-- The node ID of a record in a message, when the record is a "v4" record that verifies. -/
def recordNodeId (item : Item) : Option NodeId :=
  match Enr.ofItem item with
  | .ok r => if Enr.verifyV4 r then (Enr.nodeId r).toOption else none
  | .error _ => none

/-- Whether the records of a NODES answer match the distances that the FINDNODE asked for.

Each record must verify, and its node ID must be at one of the distances from the recipient.

The recipient is the node that received the FINDNODE and sent the records. -/
def nodesMatch (recipient : NodeId) (distances : List Nat) (records : List Item) : Bool :=
  records.all fun item =>
    match recordNodeId item with
    | some id => distances.contains (logDistance recipient id)
    | none => false

/-- The NODES answers that a node keeps for its FINDNODE, among the messages that it receives.

It keeps only the messages that answer the request, in the order that they arrive.

The first one gives `total`, the number of NODES messages of the answer.

The node keeps at most the smaller of that total and its own limit, and ignores the rest.

So a total of 0 keeps nothing. -/
def acceptNodes (limit : Nat) (request : Message) (received : List Message) : List Message :=
  let answers := received.filter (answersRequest request)
  match answers with
  | .nodes _ total _ :: _ => answers.take (min total.toNat limit)
  | _ => []

/-- The TALKRESP that answers a TALKREQ, or none for another message.

A protocol that the node knows has a handler, which gives the response to a request.

A protocol that it does not know gets an empty response. -/
def talkResponse (handlers : ByteArray → Option (ByteArray → ByteArray)) :
    Message → Option Message
  | .talkreq id protocol request =>
    some (.talkresp id (((handlers protocol).map (· request)).getD .empty))
  | _ => none

end EthLib.Networking.Discv5
