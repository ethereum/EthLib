module

public import EthLib.Networking.Devp2p.P2p

/-!
# `Networking.Devp2p.Session`

The life of an RLPx session after the handshake, from the "p2p" capability of [`rlpx.md`][p2p].

[p2p]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#p2p-capability

The frame layer hands the session the data of each frame: the message ID, then the message.

Each side sends Hello or Disconnect first, and no other message until it has received a Hello.

Once the peer's Hello arrives, the session is active, and any other message may come.

A Ping asks for an immediate Pong, and a Disconnect may come at any time.

The Hello is never compressed.

From version 5 of both peers, every later message is compressed with Snappy ([EIP-706][eip706]).

[eip706]: https://eips.ethereum.org/EIPS/eip-706

The IDs from `0x10` on belong to the capabilities that both peers share.

[Message ID-based Multiplexing][mux] gives their order.

[mux]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#message-id-based-multiplexing

The source leaves three points open, and this module reads them as follows.

It reads a Disconnect before Hello uncompressed, as it reads Hello, since no Hello has passed yet.

It never rejects a Hello for its version, since the source asks to ignore any difference.

It does not check the identities that some reasons of Disconnect name.
-/

@[expose] public section

namespace EthLib.Networking.Devp2p

/-- A reason of Disconnect, from the table of [Disconnect (0x01)][disc].

[disc]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#disconnect-0x01
-/
inductive DisconnectReason where
  /-- `0x00`: the disconnection was requested. -/
  | requested
  /-- `0x01`: an error of the TCP sub-system. -/
  | tcpError
  /-- `0x02`: a breach of protocol, such as a malformed message or bad RLP. -/
  | breachOfProtocol
  /-- `0x03`: the peer is useless. -/
  | uselessPeer
  /-- `0x04`: too many peers. -/
  | tooManyPeers
  /-- `0x05`: already connected. -/
  | alreadyConnected
  /-- `0x06`: an incompatible version of the "p2p" capability. -/
  | incompatibleVersion
  /-- `0x07`: a null node identity was received. -/
  | nullIdentity
  /-- `0x08`: the client is quitting. -/
  | clientQuitting
  /-- `0x09`: an unexpected identity in the handshake. -/
  | unexpectedIdentity
  /-- `0x0a`: the identity is that of this node, which is connected to itself. -/
  | sameIdentity
  /-- `0x0b`: a Ping timed out. -/
  | pingTimeout
  /-- `0x10`: some other reason, specific to a capability. -/
  | other
deriving DecidableEq, Repr

/-- The number of a reason. -/
def DisconnectReason.toNat : DisconnectReason → Nat
  | .requested => 0x00
  | .tcpError => 0x01
  | .breachOfProtocol => 0x02
  | .uselessPeer => 0x03
  | .tooManyPeers => 0x04
  | .alreadyConnected => 0x05
  | .incompatibleVersion => 0x06
  | .nullIdentity => 0x07
  | .clientQuitting => 0x08
  | .unexpectedIdentity => 0x09
  | .sameIdentity => 0x0a
  | .pingTimeout => 0x0b
  | .other => 0x10

/-- The reason of a number, if the table has one.

A Disconnect keeps its number, so a number that the table lacks still decodes. -/
def DisconnectReason.ofNat? : Nat → Option DisconnectReason
  | 0x00 => some .requested
  | 0x01 => some .tcpError
  | 0x02 => some .breachOfProtocol
  | 0x03 => some .uselessPeer
  | 0x04 => some .tooManyPeers
  | 0x05 => some .alreadyConnected
  | 0x06 => some .incompatibleVersion
  | 0x07 => some .nullIdentity
  | 0x08 => some .clientQuitting
  | 0x09 => some .unexpectedIdentity
  | 0x0a => some .sameIdentity
  | 0x0b => some .pingTimeout
  | 0x10 => some .other
  | _ => none

/-- The phase of a session. -/
inductive Phase where
  /-- No Hello has been received yet. -/
  | awaitHello
  /-- Both Hello messages have passed.

  The flag says whether later messages are compressed.

  The list gives the first ID of each shared capability. -/
  | active (ours theirs : Hello) (snappy : Bool) (offsets : List (Capability × Nat))
  /-- A Disconnect has been received, with its reason if it had one. -/
  | closed (reason : Option Nat)

/-- The phase that the peer's Hello opens, given our own Hello and the IDs each capability takes. -/
def Phase.opened (length : Capability → Nat) (ours theirs : Hello) : Phase :=
  .active ours theirs (snappyEnabled ours.protocolVersion theirs.protocolVersion)
    (negotiate length ours.capabilities theirs.capabilities)

/-- The shared capability that holds a message ID, with the ID relative to its first one.

A capability with first ID `b` holds the IDs from `b` on, below `b` plus the number it needs. -/
def route (length : Capability → Nat) (offsets : List (Capability × Nat)) (id : Nat) :
    Option (Capability × Nat) :=
  (offsets.find? fun entry => entry.2 ≤ id && id < entry.2 + length entry.1).map fun entry =>
    (entry.1, id - entry.2)

/-- What a received frame carries. -/
inductive Event where
  /-- A message of the "p2p" capability. -/
  | p2p (message : Message)
  /-- A message of a shared capability: its ID relative to the capability, and its data.

  The data is the RLP of the message, decompressed when the session uses Snappy. -/
  | capability (capability : Capability) (relativeId : Nat) (data : ByteArray)

/-- What the session sends back. -/
inductive Action where
  /-- A Pong, which a Ping asks for. -/
  | sendPong
deriving DecidableEq, Repr

/-- Every way the session rejects a frame. -/
inductive SessionError where
  /-- A message other than Hello or Disconnect came before the peer's Hello. -/
  | beforeHello (id : Nat)
  /-- A second Hello came in an active session. -/
  | secondHello
  /-- No message of the "p2p" capability or of a shared capability has the ID. -/
  | unknownId (id : Nat)
  /-- A frame came after a Disconnect. -/
  | closed
  /-- The data of a capability message has `size` bytes, more than 16 MiB. -/
  | tooLarge (size : Nat)
  /-- The frame data did not decode. -/
  | message (error : P2pError)
deriving Repr

/--
The stable code of an error, for the C exports.

A decoding error carries the code of its own error type, plus 10.
-/
def SessionError.code : SessionError → UInt32
  | .beforeHello _ => 1
  | .secondHello => 2
  | .unknownId _ => 3
  | .closed => 4
  | .tooLarge _ => 5
  | .message e => 10 + e.code

/--
The session after one frame, with what the frame carries and what to send back.

Before the peer's Hello, only Hello and Disconnect pass, and neither is compressed.

Hello opens the session, and Disconnect closes it.

In an active session, a Ping asks for a Pong, and a Disconnect closes the session.

A second Hello is rejected.

An ID from `0x10` on goes to the shared capability that holds it.

Its data is decompressed when the session uses Snappy.

Any other ID is rejected.

Data of more than 16 MiB is rejected, as the source asks of every message.

Compressed data is rejected when it declares that size, before it is decompressed.

After a Disconnect, every frame is rejected.
-/
def receive (length : Capability → Nat) (ours : Hello) (phase : Phase) (frameData : ByteArray) :
    Except SessionError (Phase × Option Event × List Action) := do
  match phase with
  | .closed _ => throw .closed
  | .awaitHello =>
    let (id, rest) ← (splitFrame frameData).mapError .message
    if id != 0x00 && id != 0x01 then throw (.beforeHello id)
    match ← (decodeBody false id rest).mapError .message with
    | .hello theirs => return (.opened length ours theirs, some (.p2p (.hello theirs)), [])
    | .disconnect reason => return (.closed reason, some (.p2p (.disconnect reason)), [])
    | _ => throw (.beforeHello id)
  | .active _ _ snappy offsets =>
    let (id, rest) ← (splitFrame frameData).mapError .message
    if id < 0x04 then
      match ← (decodeBody snappy id rest).mapError .message with
      | .hello _ => throw .secondHello
      | .ping => return (phase, some (.p2p .ping), [.sendPong])
      | .disconnect reason => return (.closed reason, some (.p2p (.disconnect reason)), [])
      | .pong => return (phase, some (.p2p .pong), [])
    else if id < BASE_PROTOCOL_LENGTH then throw (.unknownId id)
    else
      let some (capability, relativeId) := route length offsets id | throw (.unknownId id)
      let data ← (messageData snappy rest).mapError .message
      if MAX_MESSAGE_SIZE < data.size then throw (.tooLarge data.size)
      return (phase, some (.capability capability relativeId data), [])

end EthLib.Networking.Devp2p
