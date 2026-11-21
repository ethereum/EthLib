module

public import EthLib.Networking.Discv4.Packet

/-!
# `Networking.Discv4.Exchange`

When a node of discv4 answers a packet, from "Endpoint Proof" and the packets of [discv4].

A node answers a query only from an endpoint that has proved that it takes part in discovery.

That guards against traffic amplification: a forged source address gets no large answer.

An endpoint is proved when it sent a Pong with the hash of this node's most recent Ping to it.

The proof lasts 12 hours, and 12 hours exactly still counts.

The source states that check as a "must", which applies to FindNode and ENRRequest.

It states the other rules as "should" or "may", and this module makes them rules.

- A packet whose expiration lies in the past is not processed.
- A Ping gets a Pong that carries the hash of that Ping.
- A Pong without the hash of the most recent Ping is ignored.
- FindNode gets Neighbors, and ENRRequest gets ENRResponse, only from a proved endpoint.

An ENRResponse holds the hash of its ENRRequest, and its record should be signed by its sender.

The source keys the proof by "the sender", which this module reads as its IP address and UDP port.

The node's own Ping, after 12 hours without contact, is left to the caller.

[discv4]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/discv4.md#L48-L170
-/

@[expose] public section

namespace EthLib.Networking.Discv4

open EthLib.Serialization.Rlp

/-- How long an endpoint proof lasts, in seconds: 12 hours. -/
def ENDPOINT_PROOF_SECONDS : Nat := 12 * 3600

/-- Where a packet comes from: its IP address and UDP port. -/
structure Address where
  /-- The IP address: 4 bytes for IPv4, 16 for IPv6. -/
  ip : ByteArray
  /-- The UDP port. -/
  port : UInt16
  deriving DecidableEq

/-- What a node remembers of one address. -/
structure Peer where
  /-- The hash of the most recent Ping that the node sent there, if any. -/
  lastPing : Option (Vector UInt8 32)
  /-- The time of the last Pong from there that carried the hash of the node's Ping then. -/
  lastPong : Option Nat
  deriving DecidableEq

/-- What a node remembers of every address; an address it never met has nothing. -/
abbrev PeerState := Address → Peer

/-- The state of a node that has met no address. -/
def PeerState.empty : PeerState := fun _ => ⟨none, none⟩

/-- The state with the peer of one address replaced. -/
def PeerState.set (state : PeerState) (address : Address) (peer : Peer) : PeerState :=
  fun a => if a = address then peer else state a

/-- What a node puts into the packets that it sends. -/
structure Local where
  /-- The expiration of each packet that it sends, a UNIX time. -/
  expiration : Nat
  /-- Its record sequence number, which its Pong carries. -/
  enrSeq : Option UInt64
  /-- The nodes of its table that it gives for a target. -/
  neighbors : Vector UInt8 64 → List Node
  /-- Its node record, as an RLP item. -/
  record : Item

/-- Whether an address has proved its endpoint at a time.

It has, when its last Pong with the hash of the node's Ping came at most 12 hours earlier. -/
def proven (now : Nat) (state : PeerState) (address : Address) : Bool :=
  match (state address).lastPong with
  | some time => time ≤ now && now ≤ time + ENDPOINT_PROOF_SECONDS
  | none => false

/-- The most nodes of one Neighbors packet.

Twelve IPv6 nodes, with ports of two bytes and an expiration of four, make 1201 bytes.

Thirteen such nodes make 1292 bytes, more than the limit of 1280. -/
def MAX_NEIGHBORS : Nat := 12

/-- The Neighbors packets that carry a list of nodes, at most twelve nodes each.

The source asks for the closest 16 nodes, so they take two packets. -/
def neighborsPackets (expiration : Nat) (nodes : List Node) : List Packet :=
  if nodes.length ≤ MAX_NEIGHBORS then [.neighbors nodes expiration]
  else .neighbors (nodes.take MAX_NEIGHBORS) expiration ::
    neighborsPackets expiration (nodes.drop MAX_NEIGHBORS)
termination_by nodes.length
decreasing_by simp only [List.length_drop, MAX_NEIGHBORS] at *; omega

/-- The state after the node sends a Ping with a hash to an address. -/
def sendPing (state : PeerState) (address : Address) (hash : Vector UInt8 32) : PeerState :=
  state.set address { state address with lastPing := some hash }

/-- The expiration of a packet; an ENRResponse has none. -/
def Packet.expiration? : Packet → Option Nat
  | .ping _ _ _ e _ | .pong _ _ e _ | .findNode _ e | .neighbors _ e | .enrRequest e => some e
  | .enrResponse .. => none

/-- Whether a packet has expired at a time: its expiration lies in the past. -/
def Packet.expired (now : Nat) (p : Packet) : Bool :=
  match p.expiration? with
  | some e => e < now
  | none => false

/-- The state of a node after it receives a packet from an address, and the packets it sends back.

An expired packet changes nothing and gets no answer.

A Ping gets a Pong with the hash of the Ping, addressed to the IP and port it came from.

A Pong with the hash of the most recent Ping records the time; any other Pong changes nothing.

FindNode and ENRRequest get an answer only from an address that is proven at that time.

Neighbors and ENRResponse are answers, which the node checks on their own. -/
def receive (node : Local) (now : Nat) (state : PeerState) (address : Address)
    (received : Received) :
    PeerState × List Packet :=
  if received.packet.expired now then (state, [])
  else
    match received.packet with
    | .ping _ sender _ _ _ =>
      (state, [.pong ⟨address.ip, address.port, sender.tcpPort⟩ received.hash node.expiration
        node.enrSeq])
    | .pong _ hash _ _ =>
      if (state address).lastPing = some hash then
        (state.set address { state address with lastPong := some now }, [])
      else (state, [])
    | .findNode target _ =>
      (state, if proven now state address then
        neighborsPackets node.expiration (node.neighbors target) else [])
    | .enrRequest _ =>
      (state, if proven now state address then [.enrResponse received.hash node.record] else [])
    | .neighbors .. | .enrResponse .. => (state, [])

/-- Whether an ENRResponse answers an ENRRequest that the node sent.

It holds the hash of the whole ENRRequest packet.

The node should verify that its record is signed by the key that signed the response. -/
def acceptEnrResponse (request response : Received) : Bool :=
  match request.packet, response.packet with
  | .enrRequest _, .enrResponse hash record =>
    hash == request.hash && recordSignedBy response.sender record
  | _, _ => false

/-- An event of a node: a Ping that it sends, or a packet that it receives. -/
inductive Event where
  /-- The node sends a Ping with a hash to an address. -/
  | sent (address : Address) (hash : Vector UInt8 32)
  /-- The node receives a packet from an address at a time. -/
  | received (now : Nat) (address : Address) (packet : Received)

/-- The state of a node after an event, and the packets that it sends back. -/
def step (node : Local) (state : PeerState) : Event → PeerState × List Packet
  | .sent address hash => (sendPing state address hash, [])
  | .received now address packet => receive node now state address packet

/-- The state of a node after a run of events, from a node that has met no address. -/
def run (node : Local) (events : List Event) : PeerState :=
  events.foldl (fun state event => (step node state event).1) PeerState.empty

end EthLib.Networking.Discv4
