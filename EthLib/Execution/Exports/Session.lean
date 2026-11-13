module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Execution.Exports.Network
public import EthLib.Execution.Network.Session
public import EthLib.Execution.Network.Snap
public import EthLib.Networking.Devp2p.Session
public import EthLib.Networking.Exports.Devp2p

/-!
# `Exports.Session`

C-ABI exports for the session of an RLPx connection, with the eth and snap capabilities.

The exports take the tuple of their arguments as typed Python values.

A capability crosses the boundary as its name and version.

An eth or snap capability takes the IDs its version needs, and any other capability takes none.

A rejected frame has the code of its session error.

A bad argument, such as our own Hello that does not decode, has code 0.

The eth session takes its messages as events, each sent or received, in order.

A rejected eth message has the code of its message error or of its session error.
-/

public section

namespace EthLib.Execution.Network.Exports

open EthLib.Networking.Devp2p
open EthLib.Exports (Result PyValue pyExport)

/-- A message for a rejected frame, phrased for someone reading a Python traceback. -/
def sessionMessage : SessionError → String
  | .beforeHello id => s!"message ID {id} came before the peer's Hello"
  | .secondHello => "a second Hello came in an active session"
  | .unknownId id => s!"message ID {id} belongs to no shared capability"
  | .closed => "a frame came after a Disconnect"
  | .tooLarge size => s!"message data has {size} bytes, more than {MAX_MESSAGE_SIZE}"
  | .message e => Networking.Devp2p.Exports.message e

/-- The capabilities of a list of names and versions. -/
def capabilitiesOf (capabilities : List (ByteArray × Nat)) : List Capability :=
  capabilities.map fun (name, version) => ⟨name, version⟩

/-- The shared capability that holds a message ID, given both lists of capabilities. -/
def routeOf (args : List (ByteArray × Nat) × List (ByteArray × Nat) × Nat) :
    Result (Option (ByteArray × Nat × Nat)) := do
  let (ours, theirs, id) := args
  let offsets := negotiate capabilityLength (capabilitiesOf ours) (capabilitiesOf theirs)
  return (route capabilityLength offsets id).map fun (capability, relativeId) =>
    (capability.name, capability.version, relativeId)

/-- The shared capability that holds a message ID, given both lists of capabilities.

It gives the name and version of the capability, and the ID relative to its first one.

`None` when no shared capability holds the ID. -/
@[export eth_devp2p_route]
def routeExport (args : PyValue) : Result PyValue := pyExport routeOf args

/-- The name of a phase. -/
def phaseName : Phase → String
  | .awaitHello => "await_hello"
  | .active .. => "active"
  | .closed _ => "closed"

/-- One frame's outcome: the phase after it, what it carries, and whether to send a Pong.

A message of the "p2p" capability gives its ID and its RLP data, with an empty capability. -/
def outcomeOf (phase : Phase) (event : Option Event) (actions : List Action) :
    Result (String × String × ByteArray × Nat × Nat × ByteArray × Bool) := do
  let pong := actions.contains .sendPong
  match event with
  | some (.p2p message) =>
    let data ← (Serialization.Rlp.encode message.toItem).mapError fun _ =>
      (0, "message does not encode")
    return (phaseName phase, "p2p", .empty, 0, message.id, data, pong)
  | some (.capability capability relativeId data) =>
    return (phaseName phase, "capability", capability.name, capability.version, relativeId,
      data, pong)
  | none => return (phaseName phase, "none", .empty, 0, 0, .empty, pong)

/-- The outcomes of the frames a session receives in turn, from before the peer's Hello. -/
def sessionOf (args : ByteArray × List ByteArray) :
    Result (List (String × String × ByteArray × Nat × Nat × ByteArray × Bool)) := do
  let (helloData, frames) := args
  let .hello ours ← (decodeMessage false helloData).mapError fun e =>
      (0, s!"our Hello: {Networking.Devp2p.Exports.message e}")
    | throw (0, "our Hello is another message")
  let mut phase := Phase.awaitHello
  let mut outcomes := #[]
  for (frame, index) in frames.zipIdx do
    match receive capabilityLength ours phase frame with
    | .error e => throw (e.code, s!"frame {index}: {sessionMessage e}")
    | .ok (next, event, actions) =>
      phase := next
      outcomes := outcomes.push (← outcomeOf next event actions)
  return outcomes.toList

/-- The outcomes of the frames a session receives in turn, from before the peer's Hello.

Our Hello is given as its uncompressed frame data, and each frame as the data of a frame.

Each outcome first gives the phase after the frame, then `p2p` or `capability`.

Then come the capability's name and version, the message ID and the RLP data of the message.

For a capability message, the ID is relative to the capability's first ID.

Last comes whether to send a Pong.

A rejected frame raises the error of the session, and names the index of the frame. -/
@[export eth_devp2p_session]
def sessionExport (args : PyValue) : Result PyValue := pyExport sessionOf args

/-- A message for a rejected eth message, phrased for someone reading a Python traceback. -/
def ethSessionMessage : EthSessionError → String
  | .beforeStatus => "message came before the peer's Status"
  | .badStatus e => statusMessage e
  | .secondStatus => "a second Status came in an active session"
  | .unsolicited i => s!"response with request ID {i} answers no pending request"
  | .badRange e l => s!"block range starts at {e}, after its end {l}"
  | .transaction _ => "a received transaction has no RLP encoding"

/-- The outcomes of the eth messages that a session sends and receives in turn.

Each event says whether this node sends it, then gives its message ID and its RLP data.

Each outcome is the verdict on the message and the number of pending requests after it. -/
def ethSessionOf (args : Nat × ByteArray × Nat × Nat × List (Bool × Nat × ByteArray)) :
    Result (List (String × Nat)) := do
  let (version, schedule, number, timestamp, events) := args
  let some v := EthVersion.ofNumber? version
    | throw (0, s!"eth/{version} is not a version that EthLib specifies")
  let s ← Networking.Devp2p.Exports.readSchedule schedule
  let mut session := EthSession.init v
  let mut outcomes := #[]
  for ((sent, id, data), index) in events.zipIdx do
    let m ← (Message.decode v id data).mapError fun e =>
      (e.code, s!"event {index}: {ethMessage e}")
    if sent then
      match sendEth session m with
      | some next =>
        session := next
        outcomes := outcomes.push ("sent", session.pending.length)
      | none => outcomes := outcomes.push ("refused", session.pending.length)
    else
      match receiveEth s number timestamp session m with
      | .error e => throw (e.code, s!"event {index}: {ethSessionMessage e}")
      | .ok (next, verdict) =>
        session := next
        let name := match verdict with
          | .accept => "accept"
          | .discard => "discard"
        outcomes := outcomes.push (name, session.pending.length)
  return outcomes.toList

/-- The outcomes of the eth messages that a session sends and receives in turn.

The session runs on an eth version, for a node with a schedule and a head block.

Each event says whether this node sends it, then gives its message ID and its RLP data.

Each outcome gives the verdict and the number of requests still pending after the event.

A received message is accepted or discarded, and a sent one is sent or refused.

A message that does not decode, or that the session rejects, raises its error.

The error names the index of the event. -/
@[export eth_session]
def ethSessionExport (args : PyValue) : Result PyValue := pyExport ethSessionOf args

end EthLib.Execution.Network.Exports
