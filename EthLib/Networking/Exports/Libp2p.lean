module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Libp2p.Mplex
public import EthLib.Networking.Libp2p.MplexSession
public import EthLib.Networking.Libp2p.Multistream
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Networking.Libp2p.Upgrade
public import EthLib.Networking.Libp2p.Yamux

/-!
# Exports: libp2p framing and peer IDs

C-ABI exports for the libp2p codecs, callable from the Python C extension.

They cover multistream-select messages, mplex and yamux frames, and secp256k1 peer IDs.

They also run each peer of a multistream-select negotiation, and the upgrade of a TCP connection.

A peer of a negotiation reads the messages at the start of its input until it stops.

It returns its state, its protocol, the bytes it sent from its start, and the unread bytes.

The state crosses as its name in snake case, such as `await_proposal`.

The protocol is the agreed one, or the reply that a dialer did not expect, else empty.

A decoder returns the value at the start of its input and the bytes after it.

An mplex frame crosses as a `dict` of its stream ID, its flag and its data.

A yamux frame crosses as a `dict` of its kind, flags, stream ID, length and data.

An mplex flag or a yamux kind crosses as its name in snake case, such as `new_stream`.

The yamux flags cross as an `int`.

The multistream-select and mplex encoders refuse an input outside the format, with code 0.

The yamux encoder refuses, with code 0, data whose size is not the one its kind and length give.

Each such input breaks a rule of its source, so it has no bytes.

Another export module that passes a frame imports its conversions from this module.

The keys of a frame `dict` are the field names of its Lean structure, in snake case.

The mplex streams of one side cross as a list of an ID, who opened it, and a state name.
-/

public section

namespace EthLib.Networking.Libp2p.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Networking.Encoding
open EthLib.Cryptography.Secp256k1 (Fn)

derive_py Mplex.Flag
derive_py_laws Mplex.Flag
derive_py Mplex.Frame
derive_py_laws Mplex.Frame
derive_py Yamux.Kind
derive_py_laws Yamux.Kind
derive_py Yamux.Frame
derive_py_laws Yamux.Frame

/-- The bytes of one multistream-select message: its length, its bytes, then a newline.

The length counts the newline.

The message must be shorter than `2^63 - 1` bytes, so that its length fits an unsigned varint. -/
@[export eth_multistream_encode]
def multistreamEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (message : ByteArray) => do
    if Uvarint.bound ≤ message.size + 1 then
      throw (0, "message must be shorter than 2^63 - 1 bytes")
    return (⟨(Multistream.encode message).toArray⟩ : ByteArray)) args

/-- The multistream-select message at the start of the bytes, and the bytes after it. -/
@[export eth_multistream_decode]
def multistreamDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (message, rest) ← (Multistream.decode data.data.toList).mapError
      fun e => (e.code, s!"multistream message rejected: {reprStr e}")
    return (message, (⟨rest.toArray⟩ : ByteArray))) args

/-- The bytes of a list of messages, each encoded in turn. -/
def encodeAll (messages : List ByteArray) : ByteArray :=
  ⟨(messages.flatMap Multistream.encode).toArray⟩

/-- The name and the protocol of a listener state. -/
def listenerView : Multistream.Listener → String × ByteArray
  | .awaitHeader _ => ("await_header", .empty)
  | .awaitProposal _ => ("await_proposal", .empty)
  | .agreed protocol => ("agreed", protocol)
  | .aborted => ("aborted", .empty)

/-- The name and the protocol of a dialer state. -/
def dialerView : Multistream.Dialer → String × ByteArray
  | .awaitHeader _ _ => ("await_header", .empty)
  | .awaitAnswer _ _ => ("await_answer", .empty)
  | .agreed protocol => ("agreed", protocol)
  | .failed => ("failed", .empty)
  | .unexpected reply => ("unexpected", reply)
  | .aborted => ("aborted", .empty)

/-- A peer of a negotiation that reads the messages at the start of the bytes in turn.

It stops when its state is not waiting, or when the bytes end.

Each message is at least two bytes long, so the size of the input bounds the steps. -/
def runPeer {σ : Type} (step : σ → ByteArray → σ × List ByteArray) (waiting : σ → Bool)
    (view : σ → String × ByteArray) (start : σ × List ByteArray) (data : ByteArray) :
    Result (String × ByteArray × ByteArray × ByteArray) := do
  let (first, opening) := start
  let mut state := first
  let mut sent := opening
  let mut rest := data.data.toList
  for index in List.range data.size do
    if !waiting state || rest.isEmpty then break
    let (message, after) ← (Multistream.decode rest).mapError
      fun e => (e.code, s!"message {index} rejected: {reprStr e}")
    let (next, out) := step state message
    state := next
    sent := sent ++ out
    rest := after
  let (name, protocol) := view state
  return (name, protocol, encodeAll sent, ⟨rest.toArray⟩)

/-- What a listener does with the bytes it receives, from its start.

It returns its state, the agreed protocol or empty, the bytes it sent, and the unread bytes.

A message that does not decode raises its error, and names its index. -/
@[export eth_multistream_listen]
def multistreamListenExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((supported, data) : List ByteArray × ByteArray) =>
    runPeer Multistream.listen
      (fun | .awaitHeader _ | .awaitProposal _ => true | _ => false)
      listenerView (Multistream.Listener.start supported) data) args

/-- What a dialer does with the bytes it receives, from its start.

It proposes the protocols in order.

It returns its state, its protocol, the bytes it sent, and the unread bytes.

The protocol is the agreed one, or an answer that is neither its proposal nor `na`, else empty.

A message that does not decode raises its error, and names its index. -/
@[export eth_multistream_dial]
def multistreamDialExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((proposals, data) : List ByteArray × ByteArray) =>
    runPeer Multistream.dial
      (fun | .awaitHeader _ _ | .awaitAnswer _ _ => true | _ => false)
      dialerView (Multistream.Dialer.start proposals) data) args

/-- The security protocol and the multiplexer of a TCP connection between consensus nodes.

Each node says whether it supports yamux, the dialer first.

Two such nodes always agree, so the upgrade never fails. -/
@[export eth_libp2p_upgrade]
def upgradeExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((dialer, listener) : Bool × Bool) => do
    let some agreed := Upgrade.upgrade ⟨dialer⟩ ⟨listener⟩
      | throw (0, "the upgrade found no common protocol")
    return agreed) args

/-- The bytes of a valid mplex frame. -/
@[export eth_mplex_encode]
def mplexEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Mplex.Frame) => do
    unless decide frame.Valid do
      throw (0, "frame must have a stream ID below 2^60, at most 1 MiB of data, " ++
        "and no data on a close or a reset")
    return (⟨(Mplex.encode frame).toArray⟩ : ByteArray)) args

/-- The mplex frame at the start of the bytes, and the bytes after it. -/
@[export eth_mplex_decode]
def mplexDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (frame, rest) ← (Mplex.decode data.data.toList).mapError
      fun e => (e.code, s!"mplex frame rejected: {reprStr e}")
    return (frame, (⟨rest.toArray⟩ : ByteArray))) args

/-- The name of a stream state in snake case, such as `remote_closed+local_reset`.

The name says which sides closed the stream, then which sides reset it. -/
def mplexStateName (s : Mplex.StreamState) : String :=
  let closed := match s.localClosed, s.remoteClosed with
    | false, false => "open"
    | true, false => "local_closed"
    | false, true => "remote_closed"
    | true, true => "closed"
  closed ++ (if s.localReset then "+local_reset" else "") ++
    (if s.remoteReset then "+remote_reset" else "")

/-- A message for a refused frame, phrased for someone reading a Python traceback. -/
def mplexSessionMessage : Mplex.MplexSessionError → String
  | .reusedId i l => s!"stream {i} (opened locally: {l}) was opened before"
  | .unknownStream i l => s!"stream {i} (opened locally: {l}) is unknown"
  | .writeAfterClose i l => s!"write on stream {i} (opened locally: {l}) after its close or reset"

/-- The mplex frames at the start of the bytes, until the bytes end. -/
def mplexFrames (data : List UInt8) : Except Mplex.MplexError (List Mplex.Frame) := do
  let mut rest := data
  let mut frames := #[]
  for _ in List.range data.length do
    if rest.isEmpty then break
    let (frame, after) ← Mplex.decode rest
    frames := frames.push frame
    rest := after
  return frames.toList

/-- The streams of one side after the frames it receives and sends, from an empty table.

Each event says whether this side receives its bytes, and holds whole frames.

The streams come as their ID, whether this side opened them, and their state.

A frame that does not decode, or that the side refuses, raises its error.

The error names the index of the event. -/
@[export eth_mplex_session]
def mplexSessionExport (args : PyValue) : Result PyValue :=
  pyExport (fun (events : List (Bool × ByteArray)) => do
    let mut streams : Mplex.Streams := []
    for ((received, data), index) in events.zipIdx do
      let frames ← (mplexFrames data.data.toList).mapError
        fun e => (e.code, s!"event {index}: mplex frame rejected: {reprStr e}")
      for frame in frames do
        streams ← (Mplex.step received streams frame).mapError
          fun e => (e.code, s!"event {index}: {mplexSessionMessage e}")
    return streams.map fun ((id, opened), state) => (id, opened, mplexStateName state)) args

/-- The bytes of a valid yamux frame. -/
@[export eth_yamux_encode]
def yamuxEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Yamux.Frame) => do
    unless decide frame.Valid do
      throw (0, "frame must carry as many bytes as its length for data, else none")
    return (⟨(Yamux.encode frame).toArray⟩ : ByteArray)) args

/-- The yamux frame at the start of the bytes, and the bytes after it. -/
@[export eth_yamux_decode]
def yamuxDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (frame, rest) ← (Yamux.decode data.data.toList).mapError
      fun e => (e.code, s!"yamux frame rejected: {reprStr e}")
    return (frame, (⟨rest.toArray⟩ : ByteArray))) args

/-- The result of a function on peer identities, with the code of its error. -/
def identityResult {α : Type} (r : Except IdentityError α) : Result α :=
  r.mapError fun e => (e.code, s!"libp2p identity rejected: {reprStr e}")

/-- Read 32 big-endian bytes as a secp256k1 scalar, whose value must be below the group order.

A value at least the group order gives the private-key error; the functions that take it reject 0.

The secret key must stay private, and this function makes no constant-time claim. -/
def secretOfBytes (bytes : Vector UInt8 32) : Except IdentityError Fn :=
  let n := EthLib.Base.bytesToNat bytes.toList
  if h : n < Fn.modulus then .ok ⟨n, h⟩ else .error .privateKey

/-- The public-key protobuf of a 32-byte big-endian secp256k1 secret in [1, n).

Here n is the order of the group.

The secret key must stay private, and this function makes no constant-time claim. -/
@[export eth_libp2p_public_key]
def publicKeyExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret : Vector UInt8 32) => identityResult do
    publicKey (← secretOfBytes secret)) args

/-- The peer ID of a canonical secp256k1 key protobuf. -/
@[export eth_libp2p_peer_id]
def peerIdExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key : ByteArray) => identityResult do
    return peerId (← decodePublicKey key)) args

/-- The key protobuf that a binary secp256k1 peer ID names. -/
@[export eth_libp2p_decode_peer_id]
def decodePeerIdExport (args : PyValue) : Result PyValue :=
  pyExport (fun (id : ByteArray) => identityResult do
    return encodePublicKey (← decodePeerId id)) args

end EthLib.Networking.Libp2p.Exports
