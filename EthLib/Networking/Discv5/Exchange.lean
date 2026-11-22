module

public import EthLib.Networking.Discv5.Distance
public import EthLib.Networking.Discv5.Message
public import EthLib.Networking.Enr.V4

/-!
# `Networking.Discv5.Exchange`

The rules that relate a discv5 answer to its request.

The source is the section Protocol Messages of [the wire spec].

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
  -- PONG (0x02) is the reply to PING.
  | .ping .. => some 2
  -- NODES (0x04) is sent as a response to FINDNODE.
  | .findnode .. => some 4
  -- TALKRESP (0x06) is the response to TALKREQ.
  | .talkreq .. => some 6
  -- A response answers nothing; NODES also answers REGTOPIC and TOPICQUERY, left out here.
  | _ => none

end Message

/-- Whether a message answers a request: it has the type of the answer and the same request ID.
-/
def answersRequest (request answer : Message) : Bool :=
  -- The recipient must mirror the `request-id` of the request in the response.
  request.answerType == some answer.type && request.requestId == answer.requestId

/-- The node ID of a record in a message, when it is a record of the scheme v4 that verifies. -/
def recordNodeId (item : Item) : Option NodeId :=
  -- EIP-778: a record whose signature verifies under the scheme v4 gives its node ID.
  match Enr.ofItem item with
  | .ok r => if Enr.verifyV4 r then (Enr.nodeId r).toOption else none
  | .error _ => none

/-- Whether the records of a NODES answer match the distances that the FINDNODE asked for.

The recipient is the node that received the FINDNODE and sent the records. -/
def nodesMatch (recipient : NodeId) (distances : List Nat) (records : List Item) : Bool :=
  -- NODES: the requester should verify that the received nodes match the requested distances.
  records.all fun item =>
    match recordNodeId item with
    -- `logdistance(recipient, id)` is one of the requested distances.
    | some id => distances.contains (logDistance recipient id)
    -- Not in the source: a record that cannot be read, or does not verify, matches no distance.
    | none => false

/-- The NODES answers that a node keeps for its FINDNODE, among the messages that it receives.

A total of 0 keeps nothing. -/
def acceptNodes (limit : Nat) (request : Message) (received : List Message) : List Message :=
  -- Only the messages that answer the request, in the order that they arrive.
  let answers := received.filter (answersRequest request)
  match answers with
  -- `total` is the total number of responses to the request.
  --
  -- The source does not say which NODES message gives it; EthLib reads the first one.
  --
  -- Implementations may place a limit on `total`; past it, additional responses may be ignored.
  --
  -- Not in the source: answers past `total` are ignored too, so the node keeps `min(total, limit)`.
  | .nodes _ total _ :: _ => answers.take (min total.toNat limit)
  -- No answer, so nothing is kept.
  | _ => []

/-- The TALKRESP that answers a TALKREQ, or none for another message.

A protocol that the node knows has a handler, which gives the response to a request. -/
def talkResponse (handlers : ByteArray → Option (ByteArray → ByteArray)) :
    Message → Option Message
  -- The recipient must respond with a TALKRESP, whose `request-id` is that of the TALKREQ.
  --
  -- A known `protocol` gives the response of its handler.
  --
  -- An unknown `protocol` gets a TALKRESP with empty `response` data.
  | .talkreq id protocol request =>
    some (.talkresp id (((handlers protocol).map (· request)).getD .empty))
  -- Only a TALKREQ gets a TALKRESP.
  | _ => none

end EthLib.Networking.Discv5
