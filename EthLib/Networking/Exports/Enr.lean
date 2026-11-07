module

public import EthLib.Base.Exports
public import EthLib.Networking.Enr.Consensus
public import EthLib.Networking.Enr.Eth
public import EthLib.Networking.Enr.V4

/-!
# `Exports.Enr`

C-ABI exports for Ethereum Node Records, callable from the Python C extension.

A record crosses the boundary as its RLP bytes, and its text form as a string.

Each operation decodes the record first.

A rejected record comes back as the code and the message of its error.

A private key crosses the boundary as 32 big-endian bytes, and a bad one comes back with code 0.

Booleans come back as `UInt8`.

The consensus entries hold up to BPO2.

BPO3 to BPO5 have no consensus configuration yet, and Gloas is not yet specified.

So the forks after BPO2 fail with code 0.
-/

public section

namespace EthLib.Networking.Enr.Exports

open EthLib.Exports (Result forkUpTo)

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
  | .signing => "the record could not be signed"

/-- Run a fallible computation, with its error as a code and a message. -/
def runEnr {α : Type} (act : Except EnrError α) : Result α :=
  act.mapError fun e => (e.code, message e)

/-! ## Sizes -/

@[export eth_enr_const_max_record_size]
def constMaxRecordSize (_ : Unit) : UInt64 := UInt64.ofNat MAX_RECORD_SIZE

/-! ## Operations -/

/-- The RLP bytes of a record in text form, after the decoder accepts the record. -/
@[export eth_enr_from_text]
def fromTextExport (text : String) : Result ByteArray := do
  let r ← runEnr (fromText text)
  -- An encoder failure keeps the code of an RLP error, with a message of its own.
  r.encode.mapError fun e => ((EnrError.rlp e).code, "record has no RLP encoding")

/-- The sequence number of a record. -/
@[export eth_enr_seq]
def seqExport (record : ByteArray) : Result UInt64 := do
  return (← runEnr (decode record)).seq

/-- Whether a record is a valid "v4" record. -/
@[export eth_enr_verify_v4]
def verifyV4Export (record : ByteArray) : Result UInt8 := do
  let r ← runEnr (decode record)
  return if verifyV4 r then 1 else 0

/-- The 32-byte node ID of a "v4" record. -/
@[export eth_enr_node_id]
def nodeIdExport (record : ByteArray) : Result ByteArray := do
  let r ← runEnr (decode record)
  let id ← runEnr (nodeId r)
  return ⟨id.toArray⟩

/-- A private key of 32 big-endian bytes, below the group order. -/
def privateKeyOf (bytes : ByteArray) : Result Cryptography.Secp256k1.Fn :=
  let k := Base.bytesToNat bytes.data.toList
  if bytes.size = 32 ∧ k < Cryptography.Secp256k1.Fn.modulus then pure (Fin.ofNat _ k)
  else throw (0, "private key is not 32 bytes below the group order")

/-- The bytes of a record, signed again with a private key by the "v4" scheme.

The decoder reads the record first, and its signature is replaced. -/
@[export eth_enr_sign_v4]
def signV4Export (secretKey record : ByteArray) : Result ByteArray := do
  let sk ← privateKeyOf secretKey
  let r ← runEnr (decode record)
  let signed ← runEnr (signV4 sk r)
  signed.encode.mapError fun e => ((EnrError.rlp e).code, "record has no RLP encoding")

/-- A message for a refused consensus entry. -/
def entryMessage : EntryError → String
  | .missing key => s!"record has no {key.name} entry"
  | .notBytes key => s!"the {key.name} entry is not a byte string"
  | .ssz key _ => s!"the {key.name} entry is not valid SSZ"
  | .cgc _ => "the cgc entry is not a big-endian integer below 2^64 without leading zeros"

/-- The SSZ bytes of a value, or an error that names it. -/
def sszBytes {α : Type} [SszType α] (a : α) : Result ByteArray :=
  match SszType.serialize a with
  | .ok bytes => pure bytes
  -- No error type of the specification covers this case, so its code is 0.
  | .error _ => throw (0, "entry has no SSZ encoding")

/-- An optional entry: the byte 0 when absent, else the byte 1 and its SSZ bytes. -/
def optionBytes {α : Type} [SszType α] : Option α → Result ByteArray
  | none => pure ⟨#[0]⟩
  | some a => return ⟨#[1]⟩ ++ (← sszBytes a)

/-- The consensus entries of a record at the named fork, with `count` attestation subnets.

They come back as the 16 SSZ bytes of `eth2`, then `attnets`, `syncnets`, `cgc` and `nfd`.

Each of the four is the byte 0 when absent, or the byte 1 and its SSZ bytes. -/
@[export eth_enr_consensus_entries]
def consensusEntriesExport (fork : ByteArray) (count : UInt64) (record : ByteArray) :
    Result ByteArray := do
  let fork ← forkUpTo .bpo2 fork
  let r ← runEnr (decode record)
  let e ← (readEntries count fork r).mapError fun err => (err.code, entryMessage err)
  return (← sszBytes e.eth2) ++ (← optionBytes e.attnets) ++ (← optionBytes e.syncnets) ++
    (← optionBytes e.cgc) ++ (← optionBytes e.nfd)

/-- The fork identifier of the "eth" entry of a record, as RLP, or no bytes without the entry.

An entry that is not a list starting with a fork identifier has code 0. -/
@[export eth_enr_eth_fork_id]
def ethForkIdExport (record : ByteArray) : Result ByteArray := do
  let r ← runEnr (decode record)
  match readEth r with
  | .error _ => throw (0, "eth entry is not a list that starts with [forkHash, forkNext]")
  | .ok none => pure .empty
  | .ok (some id) =>
    (Serialization.Rlp.Codec.encode id).mapError fun _ => (0, "too large")

end EthLib.Networking.Enr.Exports
