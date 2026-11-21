module

public import EthLib.Base.Exports.PyValue
public import EthLib.Base.Hex
public import EthLib.Cryptography.Exports.Secp256k1
public import EthLib.Networking.Enr.Address
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

open EthLib.Exports (ExportError Result PyValue UnreadArgument forkUpTo pyExport rejectArgument
  toResult)

open EthLib.Serialization.Ssz (SszType)

open EthLib.Base (hexString)

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : EnrError → String
  | .tooLarge size => s!"record has {size} bytes, more than {MAX_RECORD_SIZE}"
  | .rlp _ => "record is not one RLP item"
  | .notAList => "record is not an RLP list"
  | .tooFewItems count =>
    s!"record has {count} items, too few for a signature and a sequence number"
  | .signatureNotBytes => "signature is not a byte string"
  | .invalidSeq _ => "sequence number is not an RLP scalar below 2^64"
  | .keyNotBytes => "a key is not a byte string"
  | .missingValue => "the last key has no value"
  | .repeatedKey key => s!"the key {hexString key.data.toList} is repeated"
  | .unsortedKeys key next =>
    s!"the keys are not sorted: {hexString next.data.toList} follows {hexString key.data.toList}"
  | .missingPrefix => "text does not start with enr:"
  | .base64 _ => "text is not unpadded URL-safe base64"
  | .missingId => "record has no id"
  | .unknownScheme (.bytes scheme) => s!"identity scheme {hexString scheme.data.toList} is not v4"
  | .unknownScheme (.list _) => "identity scheme is a list, not v4"
  | .invalidPublicKey => "secp256k1 value is not a valid compressed public key"
  | .signing => "the record could not be signed"
  | .invalidAddress key _ => s!"the {hexString key.data.toList} entry is not an address of its size"
  | .invalidPort key _ =>
    s!"the {hexString key.data.toList} entry is not a big-endian integer below 2^16 " ++
      "without leading zeros"

/-- A rejected record reaches Python with its code, and its message names the fault. -/
instance : ExportError EnrError where
  code := EnrError.code
  message := message

/-! ## Sizes -/

@[export eth_enr_const_max_record_size]
def constMaxRecordSize (_ : Unit) : UInt64 := UInt64.ofNat MAX_RECORD_SIZE

/-! ## Operations -/

/-- The RLP bytes of a record in text form, after the decoder accepts the record. -/
@[export eth_enr_from_text]
def fromTextExport (text : String) : Result ByteArray := do
  let r ← toResult none (fromText text)
  -- An encoder failure keeps the code of an RLP error, with a message of its own.
  r.encode.mapError fun e => ((EnrError.rlp e).code, "record has no RLP encoding")

/-- The sequence number of a record. -/
@[export eth_enr_seq]
def seqExport (record : ByteArray) : Result UInt64 := do
  return (← toResult none (decode record)).seq

/-- Whether a record is a valid "v4" record. -/
@[export eth_enr_verify_v4]
def verifyV4Export (record : ByteArray) : Result UInt8 := do
  let r ← toResult none (decode record)
  return if verifyV4 r then 1 else 0

/-- The 32-byte node ID of a "v4" record. -/
@[export eth_enr_node_id]
def nodeIdExport (record : ByteArray) : Result ByteArray := do
  let r ← toResult none (decode record)
  let id ← toResult none (nodeId r)
  return ⟨id.toArray⟩

/-- A private key of 32 big-endian bytes, below the group order. -/
def privateKeyOf (bytes : ByteArray) : Result Cryptography.Secp256k1.Fn :=
  let bad := UnreadArgument.mk "private key is not 32 bytes below the group order"
  toResult none (Cryptography.Secp256k1.Exports.readPrivateKey bytes (fun _ => bad) bad)

/-- The bytes of a record, signed again with a private key by the "v4" scheme.

The decoder reads the record first, and its signature is replaced. -/
@[export eth_enr_sign_v4]
def signV4Export (secretKey record : ByteArray) : Result ByteArray := do
  let sk ← privateKeyOf secretKey
  let r ← toResult none (decode record)
  let signed ← toResult none (signV4 sk r)
  signed.encode.mapError fun e => ((EnrError.rlp e).code, "record has no RLP encoding")

/-- The bytes of a new "v4" record of a private key, a sequence number and other pairs.

The other pairs come as the RLP list `[k1, v1, k2, v2, ...]`, in key order. -/
@[export eth_enr_make_record_v4]
def makeRecordV4Export (secretKey : ByteArray) (seq : UInt64) (pairs : ByteArray) :
    Result ByteArray := do
  let sk ← privateKeyOf secretKey
  let items ← toResult none ((Serialization.Rlp.decode pairs).mapError EnrError.rlp)
  let .list items := items | toResult none (.error EnrError.notAList)
  let r ← toResult none (makeRecordV4 sk seq (← toResult none (readPairs items)))
  r.encode.mapError fun e => ((EnrError.rlp e).code, "record has no RLP encoding")

/-- A message for a refused consensus entry. -/
def entryMessage : EntryError → String
  | .missing key => s!"record has no {key.name} entry"
  | .notBytes key => s!"the {key.name} entry is not a byte string"
  | .ssz key _ => s!"the {key.name} entry is not valid SSZ"
  | .cgc _ => "the cgc entry is not a big-endian integer below 2^64 without leading zeros"

/-- A refused consensus entry reaches Python with its code, and its message names the entry. -/
instance : ExportError EntryError where
  code := EntryError.code
  message := entryMessage

/-- The SSZ bytes of a value, or an error that names it. -/
def sszBytes {α : Type} [SszType α] (a : α) : Result ByteArray :=
  match SszType.serialize a with
  | .ok bytes => pure bytes
  -- No error type of the specification covers this case, so its code is 0.
  | .error _ => rejectArgument none "entry has no SSZ encoding"

/-- The SSZ bytes of an optional entry, or `None` when it is absent. -/
def optionBytes {α : Type} [SszType α] : Option α → Result (Option ByteArray)
  | none => pure none
  | some a => some <$> sszBytes a

/-- The consensus entries of a record, as typed Python values.

They are `eth2` as its fork digest, next fork version and next fork epoch.

Then come `attnets`, `syncnets`, `cgc` and `nfd`, each `None` when absent.

The bitvectors are their SSZ bytes, and `cgc` is an integer. -/
abbrev EntriesValue := (Vector UInt8 4 × Vector UInt8 4 × UInt64) × Option ByteArray ×
  Option ByteArray × Option UInt64 × Option (Vector UInt8 4)

/-- The consensus entries of a record at the named fork, with `count` attestation subnets. -/
def consensusEntriesOf (args : String × UInt64 × ByteArray) : Result EntriesValue := do
  let (fork, count, record) := args
  let fork ← forkUpTo .bpo2 fork.toUTF8
  let r ← toResult none (decode record)
  let e ← toResult none (readEntries count fork r)
  return ((e.eth2.forkDigest, e.eth2.nextForkVersion, e.eth2.nextForkEpoch),
    ← optionBytes e.attnets, ← optionBytes e.syncnets, e.cgc, e.nfd)

/-- The consensus entries of a record at the named fork, with `count` attestation subnets.

The arguments are the name of the fork, the number of attestation subnets and the record.

They come back as `eth2`, as its three fields, then `attnets`, `syncnets`, `cgc` and `nfd`.

Each of the last four is `None` when absent, and the bitvectors are their SSZ bytes. -/
@[export eth_enr_consensus_entries]
def consensusEntriesExport (args : PyValue) : Result PyValue :=
  pyExport consensusEntriesOf args

/-- The fork identifier of the "eth" entry of a record, as its hash and its next fork.

It is `None` without the entry, and an entry that does not start with one has code 0. -/
def ethForkIdOf (record : ByteArray) : Result (Option (Vector UInt8 4 × UInt64)) := do
  let r ← toResult none (decode record)
  match readEth r with
  | .error _ => rejectArgument none "eth entry is not a list that starts with [forkHash, forkNext]"
  | .ok none => pure none
  | .ok (some id) => pure (some (id.hash, id.next))

/-- The fork identifier of the "eth" entry of a record, as its hash and its next fork.

It is `None` without the entry, and an entry that does not start with one has code 0. -/
@[export eth_enr_eth_fork_id]
def ethForkIdExport (args : PyValue) : Result PyValue :=
  pyExport ethForkIdOf args

/-- An endpoint as Python values: its address, then its TCP, UDP and QUIC ports.

Each port is `None` when absent. -/
abbrev EndpointValue (size : Nat) :=
  Vector UInt8 size × Option UInt16 × Option UInt16 × Option UInt16

/-- The Python value of an endpoint. -/
def endpointValue {size : Nat} (e : Endpoint size) : EndpointValue size :=
  (e.ip, e.tcp, e.udp, e.quic)

/-- The IPv4 and IPv6 endpoints of a record, each `None` when its address is absent. -/
def endpointsOf (record : ByteArray) :
    Result (Option (EndpointValue 4) × Option (EndpointValue 16)) := do
  let r ← toResult none (decode record)
  let (e4, e6) ← toResult none r.endpoints
  return (e4.map endpointValue, e6.map endpointValue)

/-- The IPv4 and IPv6 endpoints of a record, each `None` when its address is absent.

An endpoint is its address, then its TCP, UDP and QUIC ports, each `None` when absent.

The IPv6 endpoint takes the `tcp` and `udp` ports when `tcp6` and `udp6` are absent.

It does not check the signature. -/
@[export eth_enr_endpoints]
def endpointsExport (args : PyValue) : Result PyValue :=
  pyExport endpointsOf args

end EthLib.Networking.Enr.Exports
