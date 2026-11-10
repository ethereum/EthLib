module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Execution.Network.SnapRange

/-!
# `Exports.Snap`

C-ABI exports for the messages of the snap capability, callable from the Python C extension.

A version crosses the boundary as its number, 1 or 2.

A message crosses it as its ID and the RLP encoding of its data.

A refused answer returns false, and a malformed input has code 0.
-/

public section

namespace EthLib.Execution.Network.Snap.Exports

open EthLib.Exports (Result PyValue pyExport)
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
  let some bytes := fullAccount slim | throw (0, "account is not in slim form")
  return bytes

/-- An answer as a Python value: `None` for the empty reply, else whether keys remain. -/
def answerToOption : RangeAnswer → Option Bool
  | .noState => none
  | .toEnd => some false
  | .more => some true

/-- Run a check of a range answer, with its error as a code and a message. -/
def runRange (act : Except SnapRangeError RangeAnswer) : Result (Option Bool) :=
  answerToOption <$> act.mapError fun e => (e.code, s!"range answer does not verify: {repr e}")

/-- An entry of a range from a pair of a key hash and its data. -/
def toRangeEntry (pair : Base.Hash32 × ByteArray) : RangeEntry := ⟨pair.1, pair.2⟩

/-- Check the accounts of an AccountRange answer, from a root and a start of 32 bytes each.

`None` means the empty reply of a peer without the state.

Otherwise it says whether the state trie holds an account after the last one. -/
def verifyAccountRangeOf
    (args : Base.Hash32 × Base.Hash32 × List (Base.Hash32 × ByteArray) × List ByteArray) :
    Result (Option Bool) := do
  let (root, start, accounts, proof) := args
  runRange (verifyAccountRange root start (accounts.map toRangeEntry) proof)

/-- Check the accounts of an AccountRange answer, from a root and a start of 32 bytes each.

The arguments are the state root, the start, the accounts and the encodings of the proof nodes.

Each account is a pair of the hash of its address and its body in slim form.

`None` means the empty reply of a peer without the state.

Otherwise it says whether the state trie holds an account after the last one.

An argument of the wrong shape has code 0.

An answer that does not verify has the code of its fault. -/
@[export eth_snap_verify_account_range]
def verifyAccountRangeExport (args : PyValue) : Result PyValue :=
  pyExport verifyAccountRangeOf args

/-- Check the ranges of a StorageRanges answer, against the storage roots of the request.

An empty start is the zero hash.

`None` means the empty reply of a peer without the state.

Otherwise it says whether the last account holds a slot after its range. -/
def verifyStorageRangesOf
    (args : List Base.Hash32 × ByteArray × List (List (Base.Hash32 × ByteArray)) ×
      List ByteArray) : Result (Option Bool) := do
  let (roots, start, slots, proof) := args
  let start ← if start.size = 0 then pure (Vector.replicate 32 0)
    else if h : start.size = 32 then pure ⟨start.data, h⟩
    else throw (0, s!"bad start size: {start.size}, expected 0 or 32")
  runRange (verifyStorageRanges roots start (slots.map (·.map toRangeEntry)) proof)

/-- Check the ranges of a StorageRanges answer, against the storage roots of the request.

The arguments are the storage roots, the start, the ranges and the encodings of the proof nodes.

Each range lists pairs of the hash of a slot and its value in the storage trie.

An empty start is the zero hash, and any other start has 32 bytes.

`None` means the empty reply of a peer without the state.

Otherwise it says whether the last account holds a slot after its range.

An argument of the wrong shape has code 0.

An answer that does not verify has the code of its fault. -/
@[export eth_snap_verify_storage_ranges]
def verifyStorageRangesExport (args : PyValue) : Result PyValue :=
  pyExport verifyStorageRangesOf args

end EthLib.Execution.Network.Snap.Exports
