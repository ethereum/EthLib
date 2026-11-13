module

public import EthLib.Networking.Libp2p.Yamux

/-!
# The streams of a yamux session

Each side keeps a table of the streams on one session, and checks each frame against it.

The client opens odd IDs and the server even ones, by [yamux, "StreamID Field"][ids].

A Data or Window Update frame with SYN opens a stream, and data may follow before the ACK.

The other side accepts it with ACK or rejects it with RST, by [yamux, "Message Flow"][flow].

FIN closes one direction, and RST closes the stream at once.

Each stream starts with a window of 256 KiB in each direction, by [yamux, "Flow Control"][window].

Data spends the window of its direction, and a Window Update adds to the other direction.

The cases that the source leaves open, and the choices made for them, are listed in SOUNDNESS.md.

[ids]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#streamid-field
[flow]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#message-flow
[window]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/yamux/README.md#flow-control
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Yamux

/-- Whether a frame carries a flag. -/
def Frame.hasFlag (frame : Frame) (flag : UInt16) : Bool :=
  frame.flags &&& flag != 0

/-- One stream, as one side sees it. -/
structure Stream where
  /-- This side opened the stream. -/
  localOpened : Bool
  /-- The side that did not open the stream has sent its ACK. -/
  acked : Bool := false
  /-- This side has sent FIN. -/
  localClosed : Bool := false
  /-- This side has received FIN. -/
  remoteClosed : Bool := false
  /-- This side has sent RST. -/
  localReset : Bool := false
  /-- This side has received RST before it sent one. -/
  remoteReset : Bool := false
  /-- The bytes of data that this side may still send. -/
  sendWindow : Nat := initialWindow
  /-- The bytes of data that this side still accepts. -/
  recvWindow : Nat := initialWindow
  deriving DecidableEq, Repr

/-- The state of a stream, as the source names it. -/
inductive StreamState where
  /-- This side opened the stream, and no ACK has arrived. -/
  | synSent
  /-- The peer opened the stream, and this side has not sent ACK. -/
  | synReceived
  /-- The stream is acknowledged and open in both directions. -/
  | established
  /-- This side has sent FIN, and the peer has not. -/
  | localClosed
  /-- The peer has sent FIN, and this side has not. -/
  | remoteClosed
  /-- Both sides have sent FIN. -/
  | closed
  /-- A side has sent RST. -/
  | reset
  deriving DecidableEq, Repr

/-- The state of a stream: a reset first, then the closes, then whether it is acknowledged. -/
def Stream.state (s : Stream) : StreamState :=
  if s.localReset || s.remoteReset then .reset
  else if s.localClosed && s.remoteClosed then .closed
  else if s.localClosed then .localClosed
  else if s.remoteClosed then .remoteClosed
  else if s.acked then .established
  else if s.localOpened then .synSent
  else .synReceived

/-- The streams of one side of a session. -/
structure Session where
  /-- This side is the client, which opens streams with odd IDs. -/
  isClient : Bool
  /-- Each stream with its ID, in the order they opened. -/
  streams : List (UInt32 × Stream) := []
  /-- This side has received Go Away; no rule reads it, so it informs the caller only. -/
  goneAway : Bool := false
  deriving DecidableEq, Repr

/-- The stream of an ID, if the table has it. -/
def Session.find? (session : Session) (id : UInt32) : Option Stream :=
  session.streams.lookup id

/-- The session with the stream of an ID set, in place if the table has it, else at the end. -/
def Session.set (session : Session) (id : UInt32) (s : Stream) : Session :=
  { session with
    streams :=
      if session.streams.any (·.1 = id) then
        session.streams.map fun e => if e.1 = id then (id, s) else e
      else session.streams ++ [(id, s)] }

/-- Whether this side opens the streams of an ID: odd IDs for the client, even for the server. -/
def Session.ownsId (session : Session) (id : UInt32) : Bool :=
  (id.toNat % 2 == 1) == session.isClient

/-- Why a side refuses a frame. -/
inductive YamuxSessionError where
  /-- A Data or Window Update frame names stream 0, which the source reserves for the session. -/
  | sessionStream
  /-- A frame opens a stream whose ID has the parity of the other side. -/
  | wrongParity (id : UInt32)
  /-- A frame opens a stream that the table already has. -/
  | reusedId (id : UInt32)
  /-- A frame without SYN names a stream that the table does not have. -/
  | unknownStream (id : UInt32)
  /-- An ACK from the side that opened the stream, or a second ACK. -/
  | unexpectedAck (id : UInt32)
  /-- A frame of the side that did not open the stream, with neither ACK nor RST, before its ACK. -/
  | missingAck (id : UInt32)
  /-- A frame from this side after either reset, or from the peer after its own reset. -/
  | afterReset (id : UInt32)
  /-- Data or FIN from a side that has sent FIN. -/
  | afterFin (id : UInt32)
  /-- Data longer than the window of its direction; the source names no reaction. -/
  | windowExceeded (id : UInt32) (length window : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, from 101. -/
def YamuxSessionError.code : YamuxSessionError → UInt32
  | .sessionStream => 101
  | .wrongParity _ => 102
  | .reusedId _ => 103
  | .unknownStream _ => 104
  | .unexpectedAck _ => 105
  | .afterReset _ => 106
  | .afterFin _ => 107
  | .windowExceeded _ _ _ => 108
  | .missingAck _ => 109

/-- The stream after the flags and the length of one Data or Window Update frame.

The frame was written by the other side when the first argument is true, else by this side.

Until the side that did not open the stream has sent ACK, its frames must carry ACK or RST.

ACK comes first, then the data or the window delta, then FIN, then RST. -/
def Stream.apply (remote : Bool) (id : UInt32) (s : Stream) (frame : Frame) :
    Except YamuxSessionError Stream := do
  if !s.acked && s.localOpened == remote && !frame.hasFlag ack && !frame.hasFlag rst then
    throw (.missingAck id)
  let s ← if frame.hasFlag ack then
      if s.acked || s.localOpened != remote then throw (.unexpectedAck id)
      pure { s with acked := true }
    else pure s
  let finSent := if remote then s.remoteClosed else s.localClosed
  let length := frame.length.toNat
  let s ← if frame.kind = .data then
      if finSent && 0 < length then throw (.afterFin id)
      let window := if remote then s.recvWindow else s.sendWindow
      if window < length then throw (.windowExceeded id length window)
      pure (if remote then { s with recvWindow := window - length }
        else { s with sendWindow := window - length })
    else
      pure (if remote then { s with sendWindow := s.sendWindow + length }
        else { s with recvWindow := s.recvWindow + length })
  let s ← if frame.hasFlag fin then
      if finSent then throw (.afterFin id)
      pure (if remote then { s with remoteClosed := true } else { s with localClosed := true })
    else pure s
  return if frame.hasFlag rst then
      (if remote then { s with remoteReset := true } else { s with localReset := true })
    else s

/-- The session after one frame, written by the other side when the first argument is true.

A Go Away from the other side marks the session, and a Ping changes nothing.

A Data or Window Update frame with SYN opens a stream, with a new nonzero ID of its writer's parity.

Any other such frame needs a stream in the table.

A frame without SYN from the peer on a stream that this side has reset is dropped, even a reset.

The caller passes a frame that the decoder accepts, so its data is not checked here. -/
def step (remote : Bool) (session : Session) (frame : Frame) :
    Except YamuxSessionError Session := do
  match frame.kind with
  | .ping => return session
  | .goAway => return if remote then { session with goneAway := true } else session
  | .data | .windowUpdate =>
    let id := frame.streamId
    if id = 0 then throw .sessionStream
    let s ← if frame.hasFlag syn then
        if (session.find? id).isSome then throw (.reusedId id)
        if session.ownsId id == remote then throw (.wrongParity id)
        pure ({ localOpened := !remote } : Stream)
      else match session.find? id with
        | none => throw (.unknownStream id)
        | some s => pure s
    if remote && s.localReset then return session
    if s.remoteReset || (!remote && s.localReset) then throw (.afterReset id)
    let s ← s.apply remote id frame
    return session.set id s

/-- The reply to a received frame: a Ping with ACK and the same value for a Ping with SYN.

A Ping with both SYN and ACK is answered too. -/
def reply (frame : Frame) : List Frame :=
  if frame.kind = .ping && frame.hasFlag syn then
    [{ kind := .ping, flags := ack, streamId := 0, length := frame.length, data := .empty }]
  else []

/-- The session after a frame that this side received, and the frames that it sends back.

An ACK or a RST in answer to a new stream is the choice of this side, so it is not among them. -/
def receive (session : Session) (frame : Frame) : Except YamuxSessionError (Session × List Frame) :=
  return (← step true session frame, reply frame)

/-- The session after a frame that this side sends. -/
def send (session : Session) (frame : Frame) : Except YamuxSessionError Session :=
  step false session frame

/-- The session after frames in turn: a frame paired with true is received, else it is sent. -/
def run (session : Session) (events : List (Bool × Frame)) : Except YamuxSessionError Session :=
  events.foldlM (fun session (remote, frame) => step remote session frame) session

end EthLib.Networking.Libp2p.Yamux
