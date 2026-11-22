module

public import EthLib.Networking.Libp2p.Mplex

/-!
# The streams of an mplex connection

Each side keeps a table of the streams on one connection, and checks each frame against it.

The rules are those of the section Protocol of [mplex][mplex].

The source fixes no reaction to an ID used again, nor to a frame on an unknown stream.

Each of these cases gets its own error.

A closed or reset stream stays in the table, so its ID and opener cannot open a stream again.

[mplex]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/mplex/README.md#protocol
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
  -- The party that opens a stream is the stream initiator, which writes NewStream.
  --
  -- MessageInitiator, CloseInitiator and ResetInitiator are the flags of its later frames.
  | .newStream | .messageInitiator | .closeInitiator | .resetInitiator => true
  | _ => false

/-- The stream of a frame, as seen by the side that wrote it, or by the side that received it. -/
def streamKey (remote : Bool) (frame : Frame) : StreamKey :=
  -- This side opened the stream when it writes an initiator flag or receives a receiver flag.
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

The caller passes a frame that the decoder accepts, so its size and data are not checked here. -/
def step (remote : Bool) (streams : Streams) (frame : Frame) :
    Except MplexSessionError Streams :=
  -- Opening a new stream: both parties can open a stream with the same ID.
  --
  -- So a stream is known by its ID and by whether this side opened it, which the flag says.
  let key := streamKey remote frame
  -- Closing and Resetting a stream: writing after a close or a reset is a protocol violation.
  let refuse : Except MplexSessionError Streams := .error (.writeAfterClose key.1 key.2)
  match frame.flag, streams.find? key with
  -- Opening a new stream: NewStream with a newly allocated ID; the stream name is not read.
  | .newStream, none => .ok (streams.set key {})
  -- Not in the source, which says only that reusing an ID after a close may be undefined.
  --
  -- A NewStream on an ID and opener already in the table is refused.
  | .newStream, some _ => .error (.reusedId key.1 key.2)
  -- Not in the source: a frame on a stream not in the table is refused.
  | _, none => .error (.unknownStream key.1 key.2)
  -- Writing to a stream: MessageReceiver (1) or MessageInitiator (2); the table does not change.
  | .messageReceiver, some s | .messageInitiator, some s =>
    -- The other side writes nothing after its own close or its own reset.
    --
    -- Not in the source: its frames may cross a reset by this side.
    --
    -- So they are accepted and dropped.
    if remote then
      if s.remoteClosed || s.remoteReset then refuse else .ok streams
    -- This side writes nothing after its own close, its own reset, or a reset it received.
    else if s.localClosed || s.localReset || s.remoteReset then refuse else .ok streams
  -- Closing a stream: CloseReceiver (3) or CloseInitiator (4) closes it for writing by its writer.
  --
  -- Writing in the other direction goes on, as with a half-closed stream.
  | .closeReceiver, some s | .closeInitiator, some s =>
    -- A second close is a write after a close, and so is a close after a reset.
    if remote then
      if s.remoteClosed || s.remoteReset then refuse
      else .ok (streams.set key { s with remoteClosed := true })
    else if s.localClosed || s.localReset || s.remoteReset then refuse
    else .ok (streams.set key { s with localClosed := true })
  -- Resetting a stream: ResetReceiver (5) or ResetInitiator (6) closes both ends at once.
  | .resetReceiver, some s | .resetInitiator, some s =>
    -- Each side has its own reset, which may follow its own close but not its own reset.
    if remote then
      if s.remoteReset then refuse else .ok (streams.set key { s with remoteReset := true })
    -- This side also writes no reset after a reset it received.
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
