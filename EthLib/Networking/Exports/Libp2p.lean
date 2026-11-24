module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.PyValue
public import EthLib.Networking.Libp2p.Mplex
public import EthLib.Networking.Libp2p.MplexSession
public import EthLib.Networking.Libp2p.Multistream
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Networking.Libp2p.Upgrade
public import EthLib.Networking.Libp2p.Yamux
public import EthLib.Networking.Libp2p.YamuxSession

/-!
# Exports: libp2p framing and peer IDs

C-ABI exports for the libp2p codecs, callable from the Python C extension.

They cover multistream-select messages, mplex and yamux frames, and secp256k1 peer IDs.

They also run each peer of a multistream-select negotiation, and the upgrade of a TCP connection.

A decoder returns the value at the start of its input and the bytes after it.
-/

public section

namespace EthLib.Networking.Libp2p.Exports

open EthLib.Exports (ExportError Result PyValue pyExport rejectArgument toResult)
open EthLib.Networking.Encoding
open EthLib.Cryptography.Secp256k1 (Fn)

-- Another export module that passes a frame imports these conversions from this module.
--
-- The keys of a frame `dict` are the field names of its Lean structure, in snake case.
--
-- An mplex flag crosses as its name in snake case, such as `new_stream`.
derive_py Mplex.Flag
derive_py_laws Mplex.Flag
-- An mplex frame crosses as a `dict` of its stream ID, its flag and its data.
derive_py Mplex.Frame
derive_py_laws Mplex.Frame
-- A yamux kind crosses as its name in snake case.
derive_py Yamux.Kind
derive_py_laws Yamux.Kind
-- A yamux frame crosses as a `dict` of its kind, flags, stream ID, length and data.
--
-- The yamux flags cross as an `int`.
derive_py Yamux.Frame
derive_py_laws Yamux.Frame

/-- A rejected multistream-select message reaches Python with its code, and the printed error. -/
instance : ExportError Multistream.MultistreamError where
  code := Multistream.MultistreamError.code
  message := reprStr

/-- A rejected mplex frame reaches Python with its code, and its message is the printed error. -/
instance : ExportError Mplex.MplexError where
  code := Mplex.MplexError.code
  message := reprStr

/-- A rejected yamux frame reaches Python with its code, and its message is the printed error. -/
instance : ExportError Yamux.YamuxError where
  code := Yamux.YamuxError.code
  message := reprStr

/-- The bytes of one multistream-select message: its length, its bytes, then a newline.

The length counts the newline.

The message must be shorter than `2^63 - 1` bytes, so that its length fits an unsigned varint. -/
@[export eth_multistream_encode]
def multistreamEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (message : ByteArray) => do
    -- A message outside the format breaks a rule of its source, so it has no bytes: code 0.
    if Uvarint.bound ≤ message.size + 1 then
      rejectArgument none "message must be shorter than 2^63 - 1 bytes"
    return (⟨(Multistream.encode message).toArray⟩ : ByteArray)) args

/-- The multistream-select message at the start of the bytes, and the bytes after it. -/
@[export eth_multistream_decode]
def multistreamDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (message, rest) ←
      toResult "multistream message rejected" (Multistream.decode data.data.toList)
    return (message, (⟨rest.toArray⟩ : ByteArray))) args

/-- The bytes of a list of messages, each encoded in turn. -/
def encodeAll (messages : List ByteArray) : ByteArray :=
  ⟨(messages.flatMap Multistream.encode).toArray⟩

/-- The name and the protocol of a listener state.

The state crosses as its name in snake case, such as `await_proposal`. -/
def listenerView : Multistream.Listener → String × ByteArray
  | .awaitHeader _ => ("await_header", .empty)
  | .awaitProposal _ => ("await_proposal", .empty)
  | .agreed protocol => ("agreed", protocol)
  | .aborted => ("aborted", .empty)

/-- The name and the protocol of a dialer state.

The protocol is the agreed one, or the reply that the dialer did not expect, else empty. -/
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
    let (message, after) ← toResult s!"message {index} rejected" (Multistream.decode rest)
    let (next, out) := step state message
    state := next
    sent := sent ++ out
    rest := after
  let (name, protocol) := view state
  -- The state, the protocol, the bytes sent from the start, and the unread bytes.
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

It returns its state, its protocol, the bytes it sent, and the unread bytes.

A message that does not decode raises its error, and names its index. -/
@[export eth_multistream_dial]
def multistreamDialExport (args : PyValue) : Result PyValue :=
  -- The dialer proposes the protocols in order.
  --
  -- Its protocol is the agreed one, or an answer that is neither its proposal nor `na`, else empty.
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
      | rejectArgument none "the upgrade found no common protocol"
    return agreed) args

/-- The bytes of a valid mplex frame. -/
@[export eth_mplex_encode]
def mplexEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Mplex.Frame) => do
    -- A frame outside the format breaks a rule of its source, so it has no bytes: code 0.
    unless decide frame.Valid do
      rejectArgument none ("frame must have a stream ID below 2^60, at most 1 MiB of data, " ++
        "and no data on a close or a reset")
    return (⟨(Mplex.encode frame).toArray⟩ : ByteArray)) args

/-- The mplex frame at the start of the bytes, and the bytes after it. -/
@[export eth_mplex_decode]
def mplexDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (frame, rest) ← toResult "mplex frame rejected" (Mplex.decode data.data.toList)
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

/-- A refused mplex frame reaches Python with its code, and its message names the fault. -/
instance : ExportError Mplex.MplexSessionError where
  code := Mplex.MplexSessionError.code
  message := mplexSessionMessage

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

A frame that does not decode, or that the side refuses, raises an error naming its event. -/
@[export eth_mplex_session]
def mplexSessionExport (args : PyValue) : Result PyValue :=
  pyExport (fun (events : List (Bool × ByteArray)) => do
    let mut streams : Mplex.Streams := []
    -- Each event says whether this side receives its bytes, and holds whole frames.
    for ((received, data), index) in events.zipIdx do
      let frames ← toResult s!"event {index}: mplex frame rejected" (mplexFrames data.data.toList)
      for frame in frames do
        streams ← toResult s!"event {index}" (Mplex.step received streams frame)
    -- Each stream crosses as its ID, whether this side opened it, and its state name.
    return streams.map fun ((id, opened), state) => (id, opened, mplexStateName state)) args

/-- The bytes of a valid yamux frame. -/
@[export eth_yamux_encode]
def yamuxEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Yamux.Frame) => do
    -- Data whose size is not the one its kind and length give breaks a rule of its source.
    --
    -- So it has no bytes, and the encoder refuses it with code 0.
    unless decide frame.Valid do
      rejectArgument none "frame must carry as many bytes as its length for data, else none"
    return (⟨(Yamux.encode frame).toArray⟩ : ByteArray)) args

/-- The yamux frame at the start of the bytes, and the bytes after it. -/
@[export eth_yamux_decode]
def yamuxDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (frame, rest) ← toResult "yamux frame rejected" (Yamux.decode data.data.toList)
    return (frame, (⟨rest.toArray⟩ : ByteArray))) args

/-- The name of a yamux stream state in snake case, such as `syn_sent`. -/
def yamuxStateName : Yamux.StreamState → String
  | .synSent => "syn_sent"
  | .synReceived => "syn_received"
  | .established => "established"
  | .localClosed => "local_closed"
  | .remoteClosed => "remote_closed"
  | .closed => "closed"
  | .reset => "reset"

/-- A message for a refused yamux frame, phrased for someone reading a Python traceback. -/
def yamuxSessionMessage : Yamux.YamuxSessionError → String
  | .sessionStream => "data or window update on stream 0, which names the session"
  | .wrongParity i => s!"stream {i} has the parity of the other side"
  | .reusedId i => s!"stream {i} was opened before"
  | .unknownStream i => s!"stream {i} is unknown"
  | .unexpectedAck i => s!"unexpected ACK on stream {i}"
  | .afterReset i => s!"frame on stream {i} after its reset"
  | .afterFin i => s!"data or FIN on stream {i} after its writer's FIN"
  | .windowExceeded i l w => s!"data of {l} bytes on stream {i} exceeds its window of {w}"
  | .missingAck i => s!"frame on stream {i} without ACK or RST before its ACK"

/-- A refused yamux frame reaches Python with its code, and its message names the fault. -/
instance : ExportError Yamux.YamuxSessionError where
  code := Yamux.YamuxSessionError.code
  message := yamuxSessionMessage

/-- The yamux frames at the start of the bytes, until the bytes end. -/
def yamuxFrames (data : List UInt8) : Except Yamux.YamuxError (List Yamux.Frame) := do
  let mut rest := data
  let mut frames := #[]
  for _ in List.range data.length do
    if rest.isEmpty then break
    let (frame, after) ← Yamux.decode rest
    frames := frames.push frame
    rest := after
  return frames.toList

/-- One side of a yamux session after the frames it receives and sends, from no stream.

A frame that does not decode, or that the side refuses, raises an error naming its event. -/
@[export eth_yamux_session]
def yamuxSessionExport (args : PyValue) : Result PyValue :=
  -- The first argument says whether this side is the client.
  pyExport (fun ((isClient, events) : Bool × List (Bool × ByteArray)) => do
    let mut session : Yamux.Session := { isClient }
    let mut replies : Array ByteArray := #[]
    -- Each event says whether this side receives its bytes, and holds whole frames.
    for ((received, data), index) in events.zipIdx do
      let frames ← toResult s!"event {index}: yamux frame rejected" (yamuxFrames data.data.toList)
      for frame in frames do
        session ← toResult s!"event {index}" (Yamux.step received session frame)
        if received then
          replies := replies ++ (Yamux.reply frame).toArray.map
            fun r => (⟨(Yamux.encode r).toArray⟩ : ByteArray)
    -- Each stream crosses as its ID, its state name, and the windows to send and to receive.
    let streams := session.streams.map fun ((id, s) : UInt32 × Yamux.Stream) =>
      (id.toNat, yamuxStateName s.state, s.sendWindow, s.recvWindow)
    -- Then come whether the side received Go Away, and the bytes of the frames it sends back.
    return (streams, session.goneAway, replies.toList)) args

/-- A rejected peer identity reaches Python with its code, and its message is the printed error. -/
instance : ExportError IdentityError where
  code := IdentityError.code
  message := reprStr

/-- Read 32 big-endian bytes as a secp256k1 scalar, whose value must be below the group order.

A value at least the group order gives the private-key error; the functions that take it reject 0.

The secret key must stay private, and this function makes no constant-time claim. -/
def secretOfBytes (bytes : Vector UInt8 32) : Except IdentityError Fn :=
  match Cryptography.Secp256k1.Fn.ofBytes? bytes.toList with
  | some d => .ok d
  | none => .error .privateKey

/-- The public-key protobuf of a 32-byte big-endian secp256k1 secret in [1, n).

Here n is the order of the group.

The secret key must stay private, and this function makes no constant-time claim. -/
@[export eth_libp2p_public_key]
def publicKeyExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret : Vector UInt8 32) => toResult "libp2p identity rejected" do
    publicKey (← secretOfBytes secret)) args

/-- The peer ID of a canonical secp256k1 key protobuf. -/
@[export eth_libp2p_peer_id]
def peerIdExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key : ByteArray) => toResult "libp2p identity rejected" do
    return peerId (← decodePublicKey key)) args

/-- The key protobuf that a binary secp256k1 peer ID names. -/
@[export eth_libp2p_decode_peer_id]
def decodePeerIdExport (args : PyValue) : Result PyValue :=
  pyExport (fun (id : ByteArray) => toResult "libp2p identity rejected" do
    return encodePublicKey (← decodePeerId id)) args

end EthLib.Networking.Libp2p.Exports
