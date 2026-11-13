module

public import EthLib.Networking.Libp2p.Mplex

/-!
# The streams of an mplex connection

Each side keeps a table of the streams on one connection, and checks each frame against it.

Both sides may open a stream with the same ID, so a stream is known by its ID and by who opened it.

The flag of a frame says whether its writer opened the stream.

A side closes a stream for its own writing, and the stream is closed once both sides have.

A reset closes both directions at once.

Writing after a close or a reset is a protocol violation, as [mplex, "Protocol"][mplex] says.

The source fixes no reaction to an ID used again, nor to a frame on an unknown stream.

Each of these cases gets its own error.

Each side has its own close and its own reset, so neither ends the other's.

A side may reset a stream after it closed it, but writes nothing after its own reset.

A side also writes nothing after it has received the other side's reset.

Frames that the peer wrote before it learned of a reset by this side may still arrive.

So this side accepts and drops them, until the peer closes or resets.

A closed or reset stream stays in the table, so its ID and opener cannot open a stream again.

[mplex]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/mplex/README.md#protocol
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Mplex

/-- A stream on a connection: its ID, and whether this side opened it. -/
abbrev StreamKey := Nat × Bool

/-- How far a stream is closed, as this side sees it. -/
structure StreamState where
  /-- This side has closed the stream for its writing. -/
  localClosed : Bool := false
  /-- The other side has closed the stream for its writing. -/
  remoteClosed : Bool := false
  /-- This side has reset the stream. -/
  localReset : Bool := false
  /-- The other side has reset the stream. -/
  remoteReset : Bool := false
  deriving DecidableEq, Repr

/-- Why a side refuses a frame. -/
inductive MplexSessionError where
  /-- A stream with this ID and opener is already in the table; the source leaves the case open. -/
  | reusedId (id : Nat) (localOpened : Bool)
  /-- The frame is for a stream that is not in the table; the source fixes no reaction. -/
  | unknownStream (id : Nat) (localOpened : Bool)
  /-- The writer of the frame has closed the stream, or the stream was reset. -/
  | writeAfterClose (id : Nat) (localOpened : Bool)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor. -/
def MplexSessionError.code : MplexSessionError → UInt32
  | .reusedId _ _ => 101
  | .unknownStream _ _ => 102
  | .writeAfterClose _ _ => 103

/-- Whether a frame of this flag is written by the side that opened its stream. -/
def Flag.initiator : Flag → Bool
  | .newStream | .messageInitiator | .closeInitiator | .resetInitiator => true
  | _ => false

/-- The stream of a frame, as seen by the side that wrote it, or by the side that received it. -/
def streamKey (remote : Bool) (frame : Frame) : StreamKey :=
  (frame.streamId, frame.flag.initiator != remote)

/-- The table of streams of one side, each with its state. -/
abbrev Streams := List (StreamKey × StreamState)

/-- The state of a stream, if the table has it. -/
def Streams.find? (streams : Streams) (key : StreamKey) : Option StreamState :=
  (List.find? (·.1 = key) streams).map (·.2)

/-- The table with the state of a stream set, in place if the table has it, else at the end. -/
def Streams.set (streams : Streams) (key : StreamKey) (state : StreamState) : Streams :=
  if streams.any (·.1 = key) then streams.map fun e => if e.1 = key then (key, state) else e
  else streams ++ [(key, state)]

/-- The table after one frame, written by the other side or by this side.

A new stream needs a key that the table does not have.

A data frame changes nothing, and a close or a reset marks its writer's half.

The other side may not write after its close or its reset.

This side may not write after its close or after a reset by either side.

A reset may follow a close, but not a reset of the same side, nor one this side received.

The caller passes a frame that the decoder accepts, so its size and data are not checked here. -/
def step (remote : Bool) (streams : Streams) (frame : Frame) :
    Except MplexSessionError Streams :=
  let key := streamKey remote frame
  let refuse : Except MplexSessionError Streams := .error (.writeAfterClose key.1 key.2)
  match frame.flag, streams.find? key with
  | .newStream, none => .ok (streams.set key {})
  | .newStream, some _ => .error (.reusedId key.1 key.2)
  | _, none => .error (.unknownStream key.1 key.2)
  | .messageReceiver, some s | .messageInitiator, some s =>
    if remote then
      if s.remoteClosed || s.remoteReset then refuse else .ok streams
    else if s.localClosed || s.localReset || s.remoteReset then refuse else .ok streams
  | .closeReceiver, some s | .closeInitiator, some s =>
    if remote then
      if s.remoteClosed || s.remoteReset then refuse
      else .ok (streams.set key { s with remoteClosed := true })
    else if s.localClosed || s.localReset || s.remoteReset then refuse
    else .ok (streams.set key { s with localClosed := true })
  | .resetReceiver, some s | .resetInitiator, some s =>
    if remote then
      if s.remoteReset then refuse else .ok (streams.set key { s with remoteReset := true })
    else if s.localReset || s.remoteReset then refuse
    else .ok (streams.set key { s with localReset := true })

/-- The table after a frame that this side received. -/
def receive (streams : Streams) (frame : Frame) : Except MplexSessionError Streams :=
  step true streams frame

/-- The table after a frame that this side sends. -/
def send (streams : Streams) (frame : Frame) : Except MplexSessionError Streams :=
  step false streams frame

/-- The table after frames in turn: a frame paired with true is received, else it is sent. -/
def run (streams : Streams) (events : List (Bool × Frame)) : Except MplexSessionError Streams :=
  events.foldlM (fun streams (remote, frame) => step remote streams frame) streams

end EthLib.Networking.Libp2p.Mplex
