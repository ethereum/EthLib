module

public import EthLib.Base.Exports
public import EthLib.Execution.Network.Snap

/-!
# `Exports.Snap`

C-ABI exports for the messages of the snap capability, callable from the Python C extension.

A version crosses the boundary as its number, 1 or 2.

A message crosses it as its ID and the RLP encoding of its data.

A refused answer returns false, and a malformed input has code 0.
-/

public section

namespace EthLib.Execution.Network.Snap.Exports

open EthLib.Exports (Result)
open EthLib.Execution.Network

/-- A message for a rejected message, phrased for someone reading a Python traceback. -/
def snapMessage : SnapError → String
  | .unknownId id => s!"message ID {id} is not used by this snap version"
  | .rlp _ => "message data is not RLP of the expected shape"

/-- The version with a number, or code 0 when EthLib does not specify it. -/
def readVersion (number : UInt64) : Result SnapVersion :=
  match SnapVersion.ofNumber? number.toNat with
  | some v => pure v
  | none => throw (0, s!"snap/{number} is not a version that EthLib specifies")

/-- Run a fallible computation of a message, with its error as a code and a message. -/
def run {α : Type} (act : Except SnapError α) : Result α :=
  act.mapError fun e => (e.code, snapMessage e)

/-- The canonical data of the message with the ID `id` and the data `data`, on a version.

It reads the message, then writes it back. -/
@[export eth_snap_message_decode]
def decodeExport (version id : UInt64) (data : ByteArray) : Result ByteArray := do
  let v ← readVersion version
  run (← run (SnapMessage.decode v id.toNat data)).encode

/-- Whether the ByteCodes data `response` answers the GetByteCodes data `request`.

It must repeat the request ID, and the codes must hash to requested hashes, in order. -/
@[export eth_snap_codes_answer]
def codesAnswerExport (version : UInt64) (request response : ByteArray) : Result Bool := do
  let v ← readVersion version
  let req ← run (SnapMessage.decode v 0x04 request)
  let resp ← run (SnapMessage.decode v 0x05 response)
  match req, resp with
  | .getByteCodes _ hashes _, .byteCodes _ codes =>
    return SnapMessage.answers req resp && codesAnswer hashes codes
  | _, _ => return false

/-- Whether `response` answers a GetBlockAccessLists `request`, given each block's access list hash.

The request is GetBlockAccessLists data, and the response BlockAccessLists data. -/
@[export eth_snap_access_lists_answer]
def accessListsAnswerExport (request response : ByteArray) (expected : Array ByteArray) :
    Result Bool := do
  let req ← run (SnapMessage.decode .snap2 0x08 request)
  let resp ← run (SnapMessage.decode .snap2 0x09 response)
  let hashes ← expected.toList.mapM fun b =>
    if h : b.size = 32 then pure (⟨b.data, h⟩ : Base.Hash32)
    else throw (0, "an access list hash is not 32 bytes")
  match resp with
  | .blockAccessLists _ lists =>
    return SnapMessage.answers req resp && accessListsAnswer hashes lists
  | _ => return false

/-- The full RLP form of an account in slim form. -/
@[export eth_snap_full_account]
def fullAccountExport (slim : ByteArray) : Result ByteArray := do
  let .ok item := Serialization.Rlp.decode slim | throw (0, "account is not one RLP item")
  let .ok (account, root) := ofSlimAccount item | throw (0, "account is not in slim form")
  let .ok bytes := State.encodeAccount account root | throw (0, "account does not encode")
  return bytes

end EthLib.Execution.Network.Snap.Exports
