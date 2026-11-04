module

public import EthLib.Networking.Enr.Consensus
public import EthLib.Networking.Enr.V4
public import EthLib.Networking.Exports.Fork

/-!
# `Exports.Enr`

C-ABI exports for Ethereum Node Records, callable from the Python C extension.

A record crosses the boundary as its RLP bytes, and its text form as ASCII bytes.

Each operation decodes the record first, and a rejected record becomes an error.

Booleans come back as `UInt8`.
-/

public section

namespace EthLib.Networking.Enr.Exports

open EthLib.Networking.Exports (forkAt)
open EthLib.Serialization.Ssz (SszType)

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : EnrError → String
  | .tooLarge size => s!"record has {size} bytes, more than {MAX_RECORD_SIZE}"
  | .rlp _ => "record is not one RLP item"
  | .notAList => "record is not an RLP list"
  | .tooFewItems => "record has no signature or no sequence number"
  | .signatureNotBytes => "signature is not a byte string"
  | .invalidSeq _ => "sequence number is not an RLP scalar below 2^64"
  | .keyNotBytes => "a key is not a byte string"
  | .missingValue => "the last key has no value"
  | .repeatedKey _ => "a key is repeated"
  | .unsortedKeys _ _ => "the keys are not sorted"
  | .missingPrefix => "text does not start with enr:"
  | .base64 _ => "text is not unpadded URL-safe base64"
  | .missingId => "record has no id"
  | .unknownScheme => "identity scheme is not v4"
  | .invalidPublicKey => "secp256k1 value is not a valid compressed public key"

/-- Run a fallible computation down to `IO`.

The C extension turns the error into a Python exception. -/
def runEnr {α : Type} (act : Except EnrError α) : IO α :=
  match act with
  | .ok a => pure a
  | .error e => throw (IO.userError (message e))

/-! ## Sizes -/

@[export eth_enr_const_max_record_size]
def constMaxRecordSize (_ : Unit) : UInt64 := UInt64.ofNat MAX_RECORD_SIZE

/-! ## Operations -/

/-- The RLP bytes of a record in text form, after the decoder accepts the record. -/
@[export eth_enr_from_text]
def fromTextExport (text : ByteArray) : IO ByteArray := do
  let some s := String.fromUTF8? text | throw (IO.userError "text is not UTF-8")
  let r ← runEnr (fromText s)
  match r.encode with
  | .ok bytes => return bytes
  | .error _ => throw (IO.userError "record has no RLP encoding")

/-- The sequence number of a record. -/
@[export eth_enr_seq]
def seqExport (record : ByteArray) : IO UInt64 := do
  return (← runEnr (decode record)).seq

/-- Whether a record is a valid "v4" record. -/
@[export eth_enr_verify_v4]
def verifyV4Export (record : ByteArray) : IO UInt8 := do
  let r ← runEnr (decode record)
  return if verifyV4 r then 1 else 0

/-- The 32-byte node ID of a "v4" record. -/
@[export eth_enr_node_id]
def nodeIdExport (record : ByteArray) : IO ByteArray := do
  let r ← runEnr (decode record)
  let id ← runEnr (nodeId r)
  return ⟨id.toArray⟩

/-- A message for a refused consensus entry. -/
def entryMessage : EntryError → String
  | .missing key => s!"record has no {key.name} entry"
  | .notBytes key => s!"the {key.name} entry is not a byte string"
  | .ssz key _ => s!"the {key.name} entry is not valid SSZ"
  | .cgc _ => "the cgc entry is not a big-endian integer below 2^64 without leading zeros"

/-- The SSZ bytes of a value, or an error that names it. -/
def sszBytes {α : Type} [SszType α] (a : α) : IO ByteArray :=
  match SszType.serialize a with
  | .ok bytes => pure bytes
  | .error _ => throw (IO.userError "entry has no SSZ encoding")

/-- An optional entry: the byte 0 when absent, else the byte 1 and its SSZ bytes. -/
def optionBytes {α : Type} [SszType α] : Option α → IO ByteArray
  | none => pure ⟨#[0]⟩
  | some a => return ⟨#[1]⟩ ++ (← sszBytes a)

/-- The consensus entries of a record at the named fork.

They come back as the 16 SSZ bytes of `eth2`, then `attnets`, `syncnets`, `cgc` and `nfd`.

Each of the four is the byte 0 when absent, or the byte 1 and its SSZ bytes. -/
@[export eth_enr_consensus_entries]
def consensusEntriesExport (fork record : ByteArray) : IO ByteArray := do
  let fork ← forkAt fork
  let r ← runEnr (decode record)
  let e ← match readEntries fork r with
    | .ok e => pure e
    | .error err => throw (IO.userError (entryMessage err))
  return (← sszBytes e.eth2) ++ (← optionBytes e.attnets) ++ (← optionBytes e.syncnets) ++
    (← optionBytes e.cgc) ++ (← optionBytes e.nfd)

end EthLib.Networking.Enr.Exports
