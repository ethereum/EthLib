module

public import EthLib.Base.Exports
public import EthLib.Execution.Network.Message
public import EthLib.Networking.Exports.ForkId

/-!
# `Exports.Network`

C-ABI exports for the messages of the eth capability, callable from the Python C extension.

A version crosses the boundary as its number, such as 69.

A message crosses it as its ID within the capability, and the RLP encoding of its data.

A schedule crosses it as the fork identifier exports read it.

Message errors have codes from 1, Status errors codes from 101, and a bad argument code 0.
-/

public section

namespace EthLib.Execution.Network.Exports

open EthLib.Exports (Result)

/-- A message for a rejected message, phrased for someone reading a Python traceback. -/
def ethMessage : EthError → String
  | .unknownId id => s!"message ID {id} is not used by this eth version, or not read by EthLib yet"
  | .rlp _ => "message data is not RLP of the expected shape"

/-- A message for a refused Status, phrased for someone reading a Python traceback. -/
def statusMessage : StatusError → String
  | .version v => s!"Status announces version {v}, not the negotiated one"
  | .forkId e => s!"fork identifier refused: {Networking.Devp2p.Exports.forkIdMessage e}"
  | .range e l => s!"block range starts at {e}, after its end {l}"

/-- The version with a number, or code 0 when EthLib does not specify it. -/
def readVersion (number : UInt64) : Result EthVersion :=
  match EthVersion.ofNumber? number.toNat with
  | some v => pure v
  | none => throw (0, s!"eth/{number} is not a version that EthLib specifies")

/-- The canonical data of the message with the ID `id` and the data `data`, on a version.

It reads the message, then writes it back. -/
@[export eth_message_decode]
def decodeExport (version id : UInt64) (data : ByteArray) : Result ByteArray := do
  let v ← readVersion version
  let run {α : Type} (act : Except EthError α) : Result α :=
    act.mapError fun e => (e.code, ethMessage e)
  run (← run (Message.decode v id.toNat data)).encode

/-- Whether a node accepts the Status `data` of a peer, on a version, at a head.

It returns true on acceptance, and raises the code of the refusal otherwise. -/
@[export eth_check_status]
def checkStatusExport (version : UInt64) (schedule : ByteArray) (number timestamp : UInt64)
    (data : ByteArray) : Result Bool := do
  let v ← readVersion version
  let s ← Networking.Devp2p.Exports.readSchedule schedule
  match Message.decode v STATUS_ID data with
  | .error e => throw (e.code, ethMessage e)
  | .ok (.status status) =>
    (checkStatus v s number.toNat timestamp.toNat status).map (fun _ => true)
      |>.mapError fun e => (e.code, statusMessage e)
  | .ok _ => throw (0, "message is not Status")

end EthLib.Execution.Network.Exports
