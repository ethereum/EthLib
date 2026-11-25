module

public import EthLib.Networking.Encoding.ByteReader
public import EthLib.Networking.Encoding.Uvarint

/-!
# multistream-select 1.0

Two peers agree on a protocol by name: one proposes it, and the other echoes it or answers `na`.

The optional listing of protocols is not modelled, so `ls` is an ordinary proposal.

The source is the section Protocol of [multistream-select][mss].

The two peers of a negotiation follow the section multistream-select of [libp2p connections][conn].

The dialer also follows the section Implementation Recommendations of [multistream-select][rec].

[mss]: https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol
[conn]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/connections/README.md#multistream-select
[rec]: https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#implementation-recommendations
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Multistream

open EthLib.Networking.Encoding

/-- The name of multistream-select 1.0, which both peers send first. -/
def protocolId : ByteArray := "/multistream/1.0.0".toUTF8

/-- The answer to a protocol that the peer does not support: "not available". -/
def notAvailable : ByteArray := "na".toUTF8

/-- The newline byte that ends every message. -/
def newline : UInt8 := 0x0a

/-- Why the message at the start of an input was refused. -/
inductive MultistreamError where
  /-- The length is not an unsigned varint. -/
  | length (error : Uvarint.UvarintError)
  /-- The length is zero, so it leaves no room for the newline. -/
  | empty
  /-- The input ends before the bytes that the length counts. -/
  | truncated (length available : Nat)
  /-- The last byte that the length counts is `last`, not a newline. -/
  | missingNewline (last : UInt8)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def MultistreamError.code : MultistreamError → UInt32
  | .length _ => 1
  | .empty => 2
  | .truncated _ _ => 3
  | .missingNewline _ => 4

/-- The bytes of one message: its length, its bytes, then the newline.

The message must be shorter than `2^63 - 1` bytes, so that its length fits an unsigned varint. -/
def encode (message : ByteArray) : List UInt8 :=
  -- Note 1: the message is prefixed by a varint that describes its size.
  --
  -- Note 2: a newline ends the message, and the size counts it.
  Uvarint.encode (message.size + 1) ++ message.data.toList ++ [newline]

/-- The message at the start of the input, without its newline, and the bytes after it. -/
def decode (bytes : List UInt8) : Except MultistreamError (ByteArray × List UInt8) := do
  -- The length, by the rules of the multiformats unsigned varint spec.
  let (length, rest) ← (Uvarint.decode bytes).mapError .length
  -- Not in the sources: a length of zero leaves no room for the newline, so it is refused.
  if length = 0 then throw .empty
  -- The bytes that the length counts.
  let (body, after) ← ByteReader.bytes (.truncated length) length rest
  -- Messages are always followed by a newline, the last byte that the length counts.
  if body[length - 1]? ≠ some newline then throw (.missingNewline (body[length - 1]?.getD 0))
  -- Messages are sent as UTF-8, but the framing reads any bytes, and leaves the name to the caller.
  return (⟨(body.take (length - 1)).toArray⟩, after)

/-- The answer to a proposed protocol: the protocol itself if supported, else `na`. -/
def respond (supported : List ByteArray) (proposal : ByteArray) : ByteArray :=
  -- A Responder that supports the protocol echoes back its protocol id, else it answers na.
  if proposal.data ∈ supported.map (·.data) then proposal else notAvailable

/-- Whether a protocol is in a list, compared byte for byte. -/
def supports (supported : List ByteArray) (protocol : ByteArray) : Bool :=
  -- Protocol Negotiation: by default, libp2p routes a protocol id by exact literal matching.
  protocol.data ∈ supported.map (·.data)

/-- The state of the peer that accepts a channel and answers proposals. -/
inductive Listener where
  /-- Waiting for the header of the dialer, with the protocols this peer supports. -/
  | awaitHeader (supported : List ByteArray)
  /-- Waiting for a proposal, with the protocols this peer supports. -/
  | awaitProposal (supported : List ByteArray)
  /-- This peer uses the protocol from now on. -/
  | agreed (protocol : ByteArray)
  /-- The first message was not the header, so the negotiation stops. -/
  | aborted
  deriving DecidableEq

/-- The listener at the start, with the messages it sends then: its header. -/
def Listener.start (supported : List ByteArray) : Listener × List ByteArray :=
  -- Both peers send the multistream protocol id, without waiting for the other side.
  (.awaitHeader supported, [protocolId])

/-- The next state of the listener on one received message, and the messages it sends. -/
def listen : Listener → ByteArray → Listener × List ByteArray
  -- A first message other than the multistream protocol id aborts the negotiation.
  | .awaitHeader supported, message =>
    if message = protocolId then (.awaitProposal supported, []) else (.aborted, [])
  -- The Responder echoes back a protocol id it supports, which signals agreement.
  --
  -- It answers na to any other, and waits for the next proposal.
  | .awaitProposal supported, message =>
    if supports supported message then (.agreed message, [message])
    else (.awaitProposal supported, [notAvailable])
  -- After an agreement, the traffic follows the agreed protocol, so the listener reads no more.
  --
  -- An aborted listener reads no more either.
  | state, _ => (state, [])

/-- The state of the peer that opens a channel and proposes protocols. -/
inductive Dialer where
  /-- Waiting for the header of the listener, with one proposal sent and the next ones. -/
  | awaitHeader (proposed : ByteArray) (rest : List ByteArray)
  /-- Waiting for the answer to a proposal, with the proposals not yet sent. -/
  | awaitAnswer (proposed : ByteArray) (rest : List ByteArray)
  /-- This peer uses the protocol from now on. -/
  | agreed (protocol : ByteArray)
  /-- The listener supports no proposal, or there was none, so the dialer closes the channel.

  A dialer with no proposal closes it before it sends anything, a case the sources leave open. -/
  | failed
  /-- The answer was neither the proposal nor `na`, and the sources fix no reaction to it. -/
  | unexpected (reply : ByteArray)
  /-- The first message was not the header, so the negotiation stops. -/
  | aborted
  deriving DecidableEq

/-- The dialer at the start, with the messages it sends then. -/
def Dialer.start : List ByteArray → Dialer × List ByteArray
  -- Not in the sources: a dialer with no proposal sends nothing and fails.
  | [] => (.failed, [])
  -- Implementation Recommendations: the initiator sends the multistream protocol and its proposal.
  --
  -- It sends both in the same packet, without waiting for the header of the listener.
  | proposed :: rest => (.awaitHeader proposed rest, [protocolId, proposed])

/-- The next state of the dialer on one received message, and the messages it sends. -/
def dial : Dialer → ByteArray → Dialer × List ByteArray
  -- A first message other than the multistream protocol id aborts the negotiation.
  | .awaitHeader proposed rest, message =>
    if message = protocolId then (.awaitAnswer proposed rest, []) else (.aborted, [])
  | .awaitAnswer proposed rest, message =>
    -- An echo of the proposed protocol id signals agreement.
    if message = proposed then (.agreed proposed, [])
    -- On na, the Initiator tries its next protocol id.
    --
    -- When none is left, it fails: the source says that it closes the channel.
    else if message = notAvailable then
      match rest with
      | [] => (.failed, [])
      | next :: rest => (.awaitAnswer next rest, [next])
    -- Not in the sources: any other answer stops the dialer, in a state that keeps the answer.
    else (.unexpected message, [])
  -- A dialer that has agreed, failed, stopped or aborted reads no more.
  | state, _ => (state, [])

/-- Both peers after they read the messages in flight, one message per unit of fuel.

The first list holds the messages to the listener, the second those to the dialer, oldest first.

Each peer reads its own messages in order, and the listener reads first. -/
def exchange : Nat → Dialer → Listener → List ByteArray → List ByteArray → Dialer × Listener
  | 0, dialer, listener, _, _ => (dialer, listener)
  | fuel + 1, dialer, listener, message :: toListener, toDialer =>
    let (listener, sent) := listen listener message
    exchange fuel dialer listener toListener (toDialer ++ sent)
  | fuel + 1, dialer, listener, [], message :: toDialer =>
    let (dialer, sent) := dial dialer message
    exchange fuel dialer listener sent toDialer
  | _ + 1, dialer, listener, [], [] => (dialer, listener)

/-- Both peers at the end of a negotiation, from their starts.

The dialer sends at most one header and one message per proposal, and the listener as many.

So the fuel lets every message in flight be read. -/
def run (proposals supported : List ByteArray) : Dialer × Listener :=
  let (dialer, toListener) := Dialer.start proposals
  let (listener, toDialer) := Listener.start supported
  exchange (2 * proposals.length + 2) dialer listener toListener toDialer

/-- The protocol that the dialer agrees on, if any, when it proposes in order.

The listener agrees on it too when no proposal is `na`. -/
def negotiate (proposals supported : List ByteArray) : Option ByteArray :=
  match (run proposals supported).1 with
  | .agreed protocol => some protocol
  | _ => none

end EthLib.Networking.Libp2p.Multistream
