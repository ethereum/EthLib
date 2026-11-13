module

public import EthLib.Networking.Encoding.Uvarint

/-!
# multistream-select 1.0

Two peers agree on a protocol by name: one proposes it, and the other echoes it or answers `na`.

Both peers first send the name of multistream-select itself.

Each message is a varint length, the bytes of the message, then a newline.

The length is read as a multiformats unsigned varint, the varint of libp2p.

The length counts the newline.

A protocol name is sent as its UTF-8 bytes, but the framing reads any bytes.

The optional listing of protocols is not modelled, so `ls` is an ordinary proposal.

The source is [multistream-select, "Protocol"][mss].

The two peers of a negotiation follow [libp2p connections, "multistream-select"][conn].

The dialer sends its first proposal without waiting for the header of the listener.

[multistream-select, "Implementation Recommendations"][rec] asks for that.

A dialer that gets an answer that is neither its proposal nor `na` stops in a state that keeps it.

The sources fix no reaction to such an answer.

[mss]: https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol
[conn]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#multistream-select
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
  /-- The last byte that the length counts is not a newline. -/
  | missingNewline
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def MultistreamError.code : MultistreamError → UInt32
  | .length _ => 1
  | .empty => 2
  | .truncated _ _ => 3
  | .missingNewline => 4

/-- The bytes of one message: its length, its bytes, then the newline.

The message must be shorter than `2^63 - 1` bytes, so that its length fits an unsigned varint. -/
def encode (message : ByteArray) : List UInt8 :=
  Uvarint.encode (message.size + 1) ++ message.data.toList ++ [newline]

/-- The message at the start of the input, without its newline, and the bytes after it. -/
def decode (bytes : List UInt8) : Except MultistreamError (ByteArray × List UInt8) := do
  let (length, rest) ← (Uvarint.decode bytes).mapError .length
  if length = 0 then throw .empty
  let body := rest.take length
  if body.length < length then throw (.truncated length body.length)
  if body[length - 1]? ≠ some newline then throw .missingNewline
  return (⟨(body.take (length - 1)).toArray⟩, rest.drop length)

/-- The answer to a proposed protocol: the protocol itself if supported, else `na`. -/
def respond (supported : List ByteArray) (proposal : ByteArray) : ByteArray :=
  if proposal.data ∈ supported.map (·.data) then proposal else notAvailable

/-- Whether a protocol is in a list, compared byte for byte. -/
def supports (supported : List ByteArray) (protocol : ByteArray) : Bool :=
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
  (.awaitHeader supported, [protocolId])

/-- The next state of the listener on one received message, and the messages it sends.

A listener that has agreed or aborted ignores the message. -/
def listen : Listener → ByteArray → Listener × List ByteArray
  | .awaitHeader supported, message =>
    if message = protocolId then (.awaitProposal supported, []) else (.aborted, [])
  | .awaitProposal supported, message =>
    if supports supported message then (.agreed message, [message])
    else (.awaitProposal supported, [notAvailable])
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

/-- The dialer at the start, with the messages it sends then.

It sends its header and its first proposal, or nothing when it has no proposal. -/
def Dialer.start : List ByteArray → Dialer × List ByteArray
  | [] => (.failed, [])
  | proposed :: rest => (.awaitHeader proposed rest, [protocolId, proposed])

/-- The next state of the dialer on one received message, and the messages it sends.

The header of the listener moves the dialer on, and any other first message aborts.

An echo of the proposal agrees on it.

On `na`, the dialer sends its next proposal, or fails when none is left.

Any other answer stops the dialer in the state that keeps that answer.

A dialer that has agreed, failed, stopped or aborted ignores the message. -/
def dial : Dialer → ByteArray → Dialer × List ByteArray
  | .awaitHeader proposed rest, message =>
    if message = protocolId then (.awaitAnswer proposed rest, []) else (.aborted, [])
  | .awaitAnswer proposed rest, message =>
    if message = proposed then (.agreed proposed, [])
    else if message = notAvailable then
      match rest with
      | [] => (.failed, [])
      | next :: rest => (.awaitAnswer next rest, [next])
    else (.unexpected message, [])
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
