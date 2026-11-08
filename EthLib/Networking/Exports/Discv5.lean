module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Exports.Enr
public import EthLib.Networking.Discv5.Identity
public import EthLib.Networking.Discv5.Message
public import EthLib.Networking.Discv5.Packet
public import EthLib.Networking.Discv5.Handshake
public import EthLib.Networking.Discv5.Session

/-!
# `Exports.Discv5`

C-ABI exports of the Node Discovery Protocol v5, for the Python bindings.

A private key crosses the boundary as 32 big-endian bytes, and a public key in a SEC 1 encoding.

A node ID is 32 bytes.

A packet error or a message error comes back with its code.

Any other rejected input comes back with code 0, including a failure of AES-GCM.

A failure of the handshake or of a session packet comes back with its own code.

When the failure is in the packet itself, the code is that of the packet error instead.

The exports that read a packet, a message or a handshake return typed Python values.

A byte string is `bytes` and a number is an `int`.

An argument that Lean cannot read fails with code 0.
-/

public section

namespace EthLib.Networking.Discv5.Exports

open EthLib.Exports (Result PyValue toPy pyExport)

open EthLib.Cryptography.Secp256k1
open EthLib.Networking.Enr.Exports (privateKeyOf)

/-- A node ID of 32 bytes. -/
def nodeIdOf (bytes : ByteArray) : Result NodeId :=
  if h : bytes.size = 32 then pure ⟨bytes.data, h⟩
  else throw (0, s!"node ID has {bytes.size} bytes, not 32")

/-- A public key in a SEC 1 encoding. -/
def publicKeyOf (bytes : ByteArray) : Result Point :=
  match Point.decode bytes with
  | .ok p => pure p
  | .error _ => throw (0, "public key is not a point of secp256k1")

/-- The logarithmic distance between two node IDs. -/
@[export eth_discv5_log_distance]
def logDistanceExport (a b : ByteArray) : Result UInt64 := do
  return (logDistance (← nodeIdOf a) (← nodeIdOf b)).toUInt64

/-- The 33-byte shared secret of a private key and a public key. -/
@[export eth_discv5_ecdh]
def ecdhExport (sk pk : ByteArray) : Result ByteArray := do
  match ecdh (← privateKeyOf sk) (← publicKeyOf pk) with
  | .ok secret => pure secret
  | .error _ => throw (0, "no shared secret")

/-- The session keys: the 16-byte initiator key and the 16-byte recipient key.

The secret is the ECDH of the ephemeral private key and the public key of node B. -/
def deriveKeysOf (args : ByteArray × ByteArray × ByteArray × ByteArray × ByteArray) :
    Result (ByteArray × ByteArray) := do
  let (ephemeralKey, destPubkey, nodeIdA, nodeIdB, challengeData) := args
  let some secret := (ecdh (← privateKeyOf ephemeralKey) (← publicKeyOf destPubkey)).toOption
    | throw (0, "no shared secret")
  match deriveKeys secret challengeData (← nodeIdOf nodeIdA) (← nodeIdOf nodeIdB) with
  | .ok keys => pure (keys.initiatorKey, keys.recipientKey)
  | .error _ => throw (0, "key derivation failed")

/-- The session keys: the 16-byte initiator key and the 16-byte recipient key.

The arguments are the ephemeral key of node A and the public key of node B.

Then come the two node IDs and the challenge data. -/
@[export eth_discv5_derive_keys]
def deriveKeysExport (args : PyValue) : Result PyValue :=
  pyExport deriveKeysOf args

/-- The 64-byte ID signature of node A. -/
@[export eth_discv5_id_sign]
def idSignExport (staticKey challengeData ephemeralPubkey nodeIdB : ByteArray) :
    Result ByteArray := do
  match idSign (← privateKeyOf staticKey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB) with
  | .ok signature => pure signature
  | .error _ => throw (0, "signing failed")

/-- Whether an ID signature verifies under the public key of node A. -/
@[export eth_discv5_id_verify]
def idVerifyExport (pubkey challengeData ephemeralPubkey nodeIdB signature : ByteArray) :
    Result UInt8 := do
  let ok := idVerify (← publicKeyOf pubkey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB)
    signature
  return if ok then 1 else 0

/-! ## Packets -/

/-- Run a packet operation, with its error as a code and a message. -/
def runPacket {α : Type} (act : Except PacketError α) : Result α :=
  act.mapError fun e => (e.code, s!"invalid packet: {repr e}")

/-- The fields of an authdata, as Python values. -/
def authdataFields : Authdata → List (String × PyValue)
  | .message srcId => [("src_id", toPy srcId)]
  | .whoareyou idNonce enrSeq => [("id_nonce", toPy idNonce), ("enr_seq", toPy enrSeq)]
  | .handshake srcId idSignature ephemeralPubkey record =>
    [("src_id", toPy srcId), ("id_signature", toPy idSignature),
      ("ephemeral_pubkey", toPy ephemeralPubkey), ("record", toPy record)]

/-- The packet that a destination node reads, as a `dict`.

It holds the flag, the masking IV, the nonce, the authdata fields and the message.

It also holds the additional data of the message. -/
def decodePacketOf (args : ByteArray × ByteArray) : Result PyValue := do
  let (destId, bytes) := args
  let p ← runPacket (Packet.decode (← nodeIdOf destId) bytes)
  let ad ← runPacket p.messageAd
  return .dict <| (#[
    ("flag", toPy p.header.authdata.flag),
    ("masking_iv", toPy p.maskingIv),
    ("nonce", toPy p.header.nonce),
    ("message", toPy p.message),
    ("message_ad", toPy ad)] ++ (authdataFields p.header.authdata).toArray)

/-- The packet that a destination node reads, as a `dict`.

The arguments are the node ID of the destination and the packet.

It holds the flag, the masking IV, the nonce, the authdata fields and the message.

It also holds the additional data of the message. -/
@[export eth_discv5_decode_packet]
def decodePacketExport (args : PyValue) : Result PyValue :=
  pyExport decodePacketOf args

/-- The bytes of the packet that the decoder reads, written again by the encoder. -/
@[export eth_discv5_reencode_packet]
def reencodePacketExport (destId bytes : ByteArray) : Result ByteArray := do
  let id ← nodeIdOf destId
  runPacket ((Packet.decode id bytes).bind (Packet.encode id))

/-- An AES-128 key of 16 bytes. -/
def aesKeyOf (bytes : ByteArray) : Result (Cryptography.Aes.Key .aes128) :=
  if h : bytes.size = 16 then pure ⟨bytes.data, h⟩
  else throw (0, "key is not 16 bytes")

/-- A nonce of 12 bytes. -/
def nonceOf (bytes : ByteArray) : Result (Vector UInt8 12) :=
  if h : bytes.size = 12 then pure ⟨bytes.data, h⟩
  else throw (0, "nonce is not 12 bytes")

/-- The encrypted message, the ciphertext then the 16-byte tag. -/
@[export eth_discv5_encrypt_message]
def encryptMessageExport (key nonce plaintext ad : ByteArray) : Result ByteArray := do
  match encryptMessage (← aesKeyOf key) (← nonceOf nonce) plaintext ad with
  | .ok message => pure message
  | .error _ => throw (0, "encryption failed")

/-- The plaintext of an encrypted message, or an error if it does not authenticate. -/
@[export eth_discv5_decrypt_message]
def decryptMessageExport (key nonce message ad : ByteArray) : Result ByteArray := do
  match decryptMessage (← aesKeyOf key) (← nonceOf nonce) message ad with
  | .ok plaintext => pure plaintext
  | .error _ => throw (0, "message does not authenticate")

/-! ## Messages -/

/-- A message error, with its code and a message for a Python traceback. -/
def runMessage {α : Type} (act : Except MessageError α) : Result α :=
  act.mapError fun e => (e.code, match e with
    | .empty => "invalid message: empty"
    | .unknownType t => s!"invalid message: unknown type {t}"
    | .rlp _ => "invalid message: not one RLP list, or a field of the wrong form"
    | .fields t => s!"invalid message: wrong field count for type {t}"
    | .invalid => "invalid message: a size or a distance is out of range")

/-- The RLP bytes of an item, for a record inside a message, or `None` when it has none. -/
def itemBytes (item : Serialization.Rlp.Item) : PyValue :=
  match Serialization.Rlp.encode item with
  | .ok bytes => .bytes bytes
  | .error _ => .none

/-- The fields of a message, as Python values: byte strings as `bytes`, integers as `int`. -/
def messageFields : Message → List (String × PyValue)
  | .ping id seq => [("request_id", toPy id), ("enr_seq", toPy seq)]
  | .pong id seq ip port =>
    [("request_id", toPy id), ("enr_seq", toPy seq),
      ("recipient_ip", toPy ip), ("recipient_port", toPy port)]
  | .findnode id ds => [("request_id", toPy id), ("distances", toPy ds)]
  | .nodes id total rs =>
    [("request_id", toPy id), ("total", toPy total),
      ("records", .list (rs.map itemBytes).toArray)]
  | .talkreq id p r =>
    [("request_id", toPy id), ("protocol", toPy p),
      ("request", toPy r)]
  | .talkresp id r => [("request_id", toPy id), ("response", toPy r)]
  | .regtopic id t rec ticket ds =>
    [("request_id", toPy id), ("topic", toPy t), ("record", itemBytes rec),
      ("ticket", toPy ticket), ("distances", toPy ds)]
  | .regconfirmation id total ticket wait =>
    [("request_id", toPy id), ("total", toPy total),
      ("ticket", toPy ticket), ("wait_time", toPy wait)]
  | .topicquery id t ds =>
    [("request_id", toPy id), ("topic", toPy t), ("distances", toPy ds)]
  | .topicnodes id total rs =>
    [("request_id", toPy id), ("total", toPy total),
      ("records", .list (rs.map itemBytes).toArray)]

/-- The message of a plaintext, as a `dict` of its type and its fields. -/
def decodeMessageOf (plaintext : ByteArray) : Result PyValue := do
  let m ← runMessage (Message.decode plaintext)
  return .dict (("type", toPy m.type) :: messageFields m).toArray

/-- The message of a plaintext, as a `dict` of its type and its fields. -/
@[export eth_discv5_decode_message]
def decodeMessageExport (args : PyValue) : Result PyValue :=
  pyExport decodeMessageOf args

/-- The plaintext of the decoded message, written again by the encoder. -/
@[export eth_discv5_reencode_message]
def reencodeMessageExport (plaintext : ByteArray) : Result ByteArray := do
  let m ← runMessage (Message.decode plaintext)
  match m.encode with
  | .ok bytes => pure bytes
  | .error _ => throw (0, "message has no RLP encoding")

/-! ## Session packets -/

/-- A vector of `n` bytes, or an error that names the field. -/
def vectorOf (n : Nat) (field : String) (bytes : ByteArray) : Result (Vector UInt8 n) :=
  if h : bytes.size = n then pure ⟨bytes.data, h⟩
  else throw (0, s!"{field} has {bytes.size} bytes, not {n}")

/-- A session error, with its code or that of its packet error, and the reason. -/
def runSession {α : Type} (act : Except SessionError α) : Result α :=
  act.mapError fun e => match e with
    | .packet p => (p.code, s!"invalid packet: {repr p}")
    | .encryption _ => (e.code, "encryption failed")
    | .decryption _ => (e.code, "message does not authenticate")
    | .wrongFlag flag expected => (e.code, s!"packet has flag {flag}, not {expected}")
    | .noSession _ => (e.code, "no session key for the source node ID")

/-- A handshake error, with its code or that of its packet error, and the reason. -/
def runHandshake {α : Type} (act : Except HandshakeError α) : Result α :=
  act.mapError fun e => match e with
    | .packet p => (p.code, s!"invalid packet: {repr p}")
    | .keyAgreement _ => (e.code, "no shared secret")
    | .keyDerivation _ => (e.code, "key derivation failed")
    | .signing _ => (e.code, "signing failed")
    | .ephemeralKeySize size => (e.code, s!"ephemeral key has {size} bytes, not 33")
    | .ephemeralKey _ => (e.code, "ephemeral key is not a point of secp256k1")
    | .idSignature => (e.code, "ID signature does not verify")
    | .encryption _ => (e.code, "encryption failed")
    | .decryption _ => (e.code, "message does not authenticate")
    | .notHandshake flag => (e.code, s!"packet has flag {flag}, not 2")

/-- Node B's WHOAREYOU packet for node A, and its challenge data. -/
def makeWhoareyouOf (args : ByteArray × ByteArray × ByteArray × ByteArray × UInt64) :
    Result (ByteArray × ByteArray) := do
  let (destId, maskingIv, nonce, idNonce, enrSeq) := args
  runSession (makeWhoareyou (← nodeIdOf destId) (← vectorOf 16 "masking IV" maskingIv)
    (← nonceOf nonce) (← vectorOf 16 "ID nonce" idNonce) enrSeq)

/-- Node B's WHOAREYOU packet for node A, and its challenge data.

The arguments are the node ID of node A, the masking IV, the nonce, the ID nonce and the seq. -/
@[export eth_discv5_make_whoareyou]
def makeWhoareyouExport (args : PyValue) : Result PyValue :=
  pyExport makeWhoareyouOf args

/-- Node A's reading of a WHOAREYOU packet, as a `dict`. -/
def readWhoareyouOf (args : ByteArray × ByteArray) : Result PyValue := do
  let (destId, packet) := args
  let c ← runSession (readWhoareyou (← nodeIdOf destId) packet)
  return .dict #[("nonce", toPy c.nonce), ("id_nonce", toPy c.idNonce),
    ("enr_seq", toPy c.enrSeq), ("challenge_data", toPy c.challengeData)]

/-- Node A's reading of a WHOAREYOU packet, as a `dict`.

The arguments are the node ID of node A and the packet. -/
@[export eth_discv5_read_whoareyou]
def readWhoareyouExport (args : PyValue) : Result PyValue :=
  pyExport readWhoareyouOf args

/-- An ordinary message packet from one node to another, under a session key. -/
@[export eth_discv5_seal_message]
def sealMessageExport (key srcId destId maskingIv nonce plaintext : ByteArray) :
    Result ByteArray := do
  runSession (sealMessage (← aesKeyOf key) (← nodeIdOf srcId) (← nodeIdOf destId)
    (← vectorOf 16 "masking IV" maskingIv) (← nonceOf nonce) plaintext)

/-- The plaintext of an ordinary message packet from a given node, under its session key.

It fails when the packet names another source node ID. -/
@[export eth_discv5_open_message]
def openMessageExport (key srcId destId packet : ByteArray) : Result ByteArray := do
  let k ← aesKeyOf key
  let src ← nodeIdOf srcId
  let (_, plaintext) ← runSession (openMessage (fun id => if id = src then some k else none)
    (← nodeIdOf destId) packet)
  return plaintext

/-- The arguments of a handshake that node A seals.

They are the ephemeral key and the static key of node A, the challenge data and the two node IDs.

Then come the public key of node B, the masking IV, the nonce, the record and the plaintext. -/
abbrev SealHandshakeArgs := ByteArray × ByteArray × ByteArray × ByteArray × ByteArray ×
  ByteArray × ByteArray × ByteArray × ByteArray × ByteArray

/-- Node A's handshake message packet for node B, and its two session keys. -/
def sealHandshakeOf (args : SealHandshakeArgs) : Result (ByteArray × ByteArray × ByteArray) := do
  let (ephemeralKey, staticKey, challengeData, srcId, destId, destPubkey, maskingIv, nonce, record,
    plaintext) := args
  let (packet, keys) ← runHandshake (sealHandshake (← privateKeyOf ephemeralKey)
    (← privateKeyOf staticKey) challengeData (← nodeIdOf srcId) (← nodeIdOf destId)
    (← publicKeyOf destPubkey) (← vectorOf 16 "masking IV" maskingIv) (← nonceOf nonce) record
    plaintext)
  return (packet, keys.initiatorKey, keys.recipientKey)

/-- Node A's handshake message packet for node B, and its two session keys.

The arguments are the ephemeral key and the static key of node A, the challenge data and the IDs.

Then come the public key of node B, the masking IV, the nonce, the record and the plaintext. -/
@[export eth_discv5_seal_handshake]
def sealHandshakeExport (args : PyValue) : Result PyValue :=
  pyExport sealHandshakeOf args

/-- Node B's reading of a handshake message packet, as a `dict`. -/
def openHandshakeOf (args : ByteArray × ByteArray × ByteArray × ByteArray × ByteArray) :
    Result PyValue := do
  let (staticKey, challengeData, destId, srcPubkey, packet) := args
  let r ← runHandshake (openHandshake (← privateKeyOf staticKey) challengeData
    (← nodeIdOf destId) (← publicKeyOf srcPubkey) packet)
  return .dict #[("src_id", toPy r.srcId), ("record", toPy r.record),
    ("plaintext", toPy r.message), ("initiator_key", toPy r.keys.initiatorKey),
    ("recipient_key", toPy r.keys.recipientKey)]

/-- Node B's reading of a handshake message packet, as a `dict`.

The arguments are the static key of node B, the challenge data and the node ID of node B.

Then come the public key of node A and the packet. -/
@[export eth_discv5_open_handshake]
def openHandshakeExport (args : PyValue) : Result PyValue :=
  pyExport openHandshakeOf args

end EthLib.Networking.Discv5.Exports
