module

public import EthLib.Base.Exports
public import Lean.Data.Json
public import EthLib.Base.Hex
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

A failure of the handshake or of a session packet comes back with the code of its packet error.

Any other such failure comes back with code 0, and its message names the reason.
-/

public section

namespace EthLib.Networking.Discv5.Exports

open EthLib.Exports (Result)

open EthLib.Cryptography.Secp256k1
open Lean (Json ToJson toJson)

/-- A node ID of 32 bytes. -/
def nodeIdOf (bytes : ByteArray) : Result NodeId :=
  if h : bytes.size = 32 then pure ⟨bytes.data, h⟩
  else throw (0, s!"node ID has {bytes.size} bytes, not 32")

/-- A private key of 32 big-endian bytes, below the group order. -/
def privateKeyOf (bytes : ByteArray) : Result Fn :=
  let k := Base.bytesToNat bytes.data.toList
  if bytes.size = 32 ∧ k < Fn.modulus then pure (Fin.ofNat _ k)
  else throw (0, "private key is not 32 bytes below the group order")

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

/-- The session keys, as the 16 bytes of the initiator key, then the 16 of the recipient key.

The secret is the ECDH of the ephemeral private key and the public key of node B. -/
@[export eth_discv5_derive_keys]
def deriveKeysExport (ephemeralKey destPubkey nodeIdA nodeIdB challengeData : ByteArray) :
    Result ByteArray := do
  let some secret := (ecdh (← privateKeyOf ephemeralKey) (← publicKeyOf destPubkey)).toOption
    | throw (0, "no shared secret")
  match deriveKeys secret challengeData (← nodeIdOf nodeIdA) (← nodeIdOf nodeIdB) with
  | .ok keys => pure (keys.initiatorKey ++ keys.recipientKey)
  | .error _ => throw (0, "key derivation failed")

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

/-- Bytes as a `0x`-prefixed lowercase hex string. -/
def hex (bytes : List UInt8) : Json :=
  Json.str (Base.hexString bytes)

/-- Run a packet operation, with its error as a code and a message. -/
def runPacket {α : Type} (act : Except PacketError α) : Result α :=
  act.mapError fun e => (e.code, s!"invalid packet: {repr e}")

/-- The fields of an authdata, as JSON. -/
def authdataJson : Authdata → List (String × Json)
  | .message srcId => [("src_id", hex srcId.toList)]
  | .whoareyou idNonce enrSeq =>
    [("id_nonce", hex idNonce.toList), ("enr_seq", toJson enrSeq.toNat)]
  | .handshake srcId idSignature ephemeralPubkey record =>
    [("src_id", hex srcId.toList), ("id_signature", hex idSignature.data.toList),
      ("ephemeral_pubkey", hex ephemeralPubkey.data.toList), ("record", hex record.data.toList)]

/-- The packet that a destination node reads, as a JSON object of hex strings.

It holds the flag, the masking IV, the nonce, the authdata fields and the message.

It also holds the additional data of the message. -/
@[export eth_discv5_decode_packet]
def decodePacketExport (destId bytes : ByteArray) : Result ByteArray := do
  let p ← runPacket (Packet.decode (← nodeIdOf destId) bytes)
  let ad ← runPacket p.messageAd
  let json := Json.mkObj <| [
    ("flag", toJson p.header.authdata.flag.toNat),
    ("masking_iv", hex p.maskingIv.toList),
    ("nonce", hex p.header.nonce.toList),
    ("message", hex p.message.data.toList),
    ("message_ad", hex ad.data.toList)] ++ authdataJson p.header.authdata
  return json.compress.toUTF8

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

/-- The RLP bytes of an item, for a record inside a message. -/
def itemHex (item : Serialization.Rlp.Item) : Json :=
  match Serialization.Rlp.encode item with
  | .ok bytes => hex bytes.data.toList
  | .error _ => Json.null

/-- The fields of a message, as JSON: byte strings in hex, integers as numbers. -/
def messageJson : Message → List (String × Json)
  | .ping id seq => [("request_id", hex id.data.toList), ("enr_seq", toJson seq.toNat)]
  | .pong id seq ip port =>
    [("request_id", hex id.data.toList), ("enr_seq", toJson seq.toNat),
      ("recipient_ip", hex ip.data.toList), ("recipient_port", toJson port.toNat)]
  | .findnode id ds => [("request_id", hex id.data.toList), ("distances", toJson ds)]
  | .nodes id total rs =>
    [("request_id", hex id.data.toList), ("total", toJson total.toNat),
      ("records", Json.arr (rs.map itemHex).toArray)]
  | .talkreq id p r =>
    [("request_id", hex id.data.toList), ("protocol", hex p.data.toList),
      ("request", hex r.data.toList)]
  | .talkresp id r => [("request_id", hex id.data.toList), ("response", hex r.data.toList)]
  | .regtopic id t rec ticket ds =>
    [("request_id", hex id.data.toList), ("topic", hex t.toList), ("record", itemHex rec),
      ("ticket", hex ticket.data.toList), ("distances", toJson ds)]
  | .regconfirmation id total ticket wait =>
    [("request_id", hex id.data.toList), ("total", toJson total.toNat),
      ("ticket", hex ticket.data.toList), ("wait_time", toJson wait.toNat)]
  | .topicquery id t ds =>
    [("request_id", hex id.data.toList), ("topic", hex t.toList), ("distances", toJson ds)]
  | .topicnodes id total rs =>
    [("request_id", hex id.data.toList), ("total", toJson total.toNat),
      ("records", Json.arr (rs.map itemHex).toArray)]

/-- The message of a plaintext, as a JSON object with its type and its fields. -/
@[export eth_discv5_decode_message]
def decodeMessageExport (plaintext : ByteArray) : Result ByteArray := do
  let m ← runMessage (Message.decode plaintext)
  let json := Json.mkObj (("type", toJson m.type.toNat) :: messageJson m)
  return json.compress.toUTF8

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

/-- A session error, with the code of its packet error or 0, and the reason. -/
def runSession {α : Type} (act : Except SessionError α) : Result α :=
  act.mapError fun
    | .packet e => (e.code, s!"invalid packet: {repr e}")
    | .encryption _ => (0, "encryption failed")
    | .decryption _ => (0, "message does not authenticate")
    | .wrongFlag flag expected => (0, s!"packet has flag {flag}, not {expected}")
    | .noSession _ => (0, "no session key for the source node ID")

/-- A handshake error, with the code of its packet error or 0, and the reason. -/
def runHandshake {α : Type} (act : Except HandshakeError α) : Result α :=
  act.mapError fun
    | .packet e => (e.code, s!"invalid packet: {repr e}")
    | .keyAgreement _ => (0, "no shared secret")
    | .keyDerivation _ => (0, "key derivation failed")
    | .signing _ => (0, "signing failed")
    | .ephemeralKeySize size => (0, s!"ephemeral key has {size} bytes, not 33")
    | .ephemeralKey _ => (0, "ephemeral key is not a point of secp256k1")
    | .idSignature => (0, "ID signature does not verify")
    | .encryption _ => (0, "encryption failed")
    | .decryption _ => (0, "message does not authenticate")
    | .notHandshake flag => (0, s!"packet has flag {flag}, not 2")

/-- Node B's WHOAREYOU packet for node A, and its challenge data, as a JSON object.

The `enr-seq` is 8 big-endian bytes. -/
@[export eth_discv5_make_whoareyou]
def makeWhoareyouExport (destId maskingIv nonce idNonce enrSeq : ByteArray) :
    Result ByteArray := do
  let seq ← vectorOf 8 "enr-seq" enrSeq
  let (packet, challengeData) ← runSession (makeWhoareyou (← nodeIdOf destId)
    (← vectorOf 16 "masking IV" maskingIv) (← nonceOf nonce) (← vectorOf 16 "ID nonce" idNonce)
    (Base.bytesToNat seq.toList).toUInt64)
  let json := Json.mkObj [("packet", hex packet.data.toList),
    ("challenge_data", hex challengeData.data.toList)]
  return json.compress.toUTF8

/-- Node A's reading of a WHOAREYOU packet, as a JSON object. -/
@[export eth_discv5_read_whoareyou]
def readWhoareyouExport (destId packet : ByteArray) : Result ByteArray := do
  let c ← runSession (readWhoareyou (← nodeIdOf destId) packet)
  let json := Json.mkObj [("nonce", hex c.nonce.toList), ("id_nonce", hex c.idNonce.toList),
    ("enr_seq", toJson c.enrSeq.toNat), ("challenge_data", hex c.challengeData.data.toList)]
  return json.compress.toUTF8

/-- An ordinary message packet from node `srcId` to node `destId`, under a session key. -/
@[export eth_discv5_seal_message]
def sealMessageExport (key srcId destId maskingIv nonce plaintext : ByteArray) :
    Result ByteArray := do
  runSession (sealMessage (← aesKeyOf key) (← nodeIdOf srcId) (← nodeIdOf destId)
    (← vectorOf 16 "masking IV" maskingIv) (← nonceOf nonce) plaintext)

/-- The plaintext of an ordinary message packet from the node `srcId`, under its session key.

It fails when the packet names another source node ID. -/
@[export eth_discv5_open_message]
def openMessageExport (key srcId destId packet : ByteArray) : Result ByteArray := do
  let k ← aesKeyOf key
  let src ← nodeIdOf srcId
  let (_, plaintext) ← runSession (openMessage (fun id => if id = src then some k else none)
    (← nodeIdOf destId) packet)
  return plaintext

/-- Node A's handshake message packet for node B, and its session keys, as a JSON object. -/
@[export eth_discv5_seal_handshake]
def sealHandshakeExport (ephemeralKey staticKey challengeData srcId destId destPubkey maskingIv
    nonce record plaintext : ByteArray) : Result ByteArray := do
  let (packet, keys) ← runHandshake (sealHandshake (← privateKeyOf ephemeralKey)
    (← privateKeyOf staticKey) challengeData (← nodeIdOf srcId) (← nodeIdOf destId)
    (← publicKeyOf destPubkey) (← vectorOf 16 "masking IV" maskingIv) (← nonceOf nonce) record
    plaintext)
  let json := Json.mkObj [("packet", hex packet.data.toList),
    ("initiator_key", hex keys.initiatorKey.data.toList),
    ("recipient_key", hex keys.recipientKey.data.toList)]
  return json.compress.toUTF8

/-- Node B's reading of a handshake message packet, as a JSON object. -/
@[export eth_discv5_open_handshake]
def openHandshakeExport (staticKey challengeData destId srcPubkey packet : ByteArray) :
    Result ByteArray := do
  let r ← runHandshake (openHandshake (← privateKeyOf staticKey) challengeData
    (← nodeIdOf destId) (← publicKeyOf srcPubkey) packet)
  let json := Json.mkObj [("src_id", hex r.srcId.toList), ("record", hex r.record.data.toList),
    ("plaintext", hex r.message.data.toList),
    ("initiator_key", hex r.keys.initiatorKey.data.toList),
    ("recipient_key", hex r.keys.recipientKey.data.toList)]
  return json.compress.toUTF8

end EthLib.Networking.Discv5.Exports
