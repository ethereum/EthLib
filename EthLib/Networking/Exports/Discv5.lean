module

public import Lean.Data.Json
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Networking.Discv5.Identity
public import EthLib.Networking.Discv5.Packet

/-!
# `Exports.Discv5`

C-ABI exports of the Node Discovery Protocol v5, for the Python bindings.

A private key crosses the boundary as 32 big-endian bytes, and a public key in a SEC 1 encoding.

A node ID is 32 bytes, and a rejected input becomes an error.
-/

public section

namespace EthLib.Networking.Discv5.Exports

open EthLib.Cryptography.Secp256k1
open Lean (Json ToJson toJson)

/-- A node ID of 32 bytes. -/
def nodeIdOf (bytes : ByteArray) : IO NodeId :=
  if h : bytes.size = 32 then pure ⟨bytes.data, h⟩
  else throw (IO.userError s!"node ID has {bytes.size} bytes, not 32")

/-- A private key of 32 big-endian bytes, below the group order. -/
def privateKeyOf (bytes : ByteArray) : IO Fn :=
  let k := ofBytesBE bytes.data.toList
  if bytes.size = 32 ∧ k < Fn.modulus then pure (Fin.ofNat _ k)
  else throw (IO.userError "private key is not 32 bytes below the group order")

/-- A public key in a SEC 1 encoding. -/
def publicKeyOf (bytes : ByteArray) : IO Point :=
  match Point.decode bytes with
  | .ok p => pure p
  | .error _ => throw (IO.userError "public key is not a point of secp256k1")

/-- The logarithmic distance between two node IDs. -/
@[export eth_discv5_log_distance]
def logDistanceExport (a b : ByteArray) : IO UInt64 := do
  return (logDistance (← nodeIdOf a) (← nodeIdOf b)).toUInt64

/-- The 33-byte shared secret of a private key and a public key. -/
@[export eth_discv5_ecdh]
def ecdhExport (sk pk : ByteArray) : IO ByteArray := do
  match ecdh (← privateKeyOf sk) (← publicKeyOf pk) with
  | .ok secret => pure secret
  | .error _ => throw (IO.userError "no shared secret")

/-- The session keys, as the 16 bytes of the initiator key, then the 16 of the recipient key.

The secret is the ECDH of the ephemeral private key and the public key of node B. -/
@[export eth_discv5_derive_keys]
def deriveKeysExport (ephemeralKey destPubkey nodeIdA nodeIdB challengeData : ByteArray) :
    IO ByteArray := do
  let some secret := (ecdh (← privateKeyOf ephemeralKey) (← publicKeyOf destPubkey)).toOption
    | throw (IO.userError "no shared secret")
  match deriveKeys secret challengeData (← nodeIdOf nodeIdA) (← nodeIdOf nodeIdB) with
  | .ok keys => pure (keys.initiatorKey ++ keys.recipientKey)
  | .error _ => throw (IO.userError "key derivation failed")

/-- The 64-byte ID signature of node A. -/
@[export eth_discv5_id_sign]
def idSignExport (staticKey challengeData ephemeralPubkey nodeIdB : ByteArray) :
    IO ByteArray := do
  match idSign (← privateKeyOf staticKey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB) with
  | .ok signature => pure signature
  | .error _ => throw (IO.userError "signing failed")

/-- Whether an ID signature verifies under the public key of node A. -/
@[export eth_discv5_id_verify]
def idVerifyExport (pubkey challengeData ephemeralPubkey nodeIdB signature : ByteArray) :
    IO UInt8 := do
  let ok := idVerify (← publicKeyOf pubkey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB)
    signature
  return if ok then 1 else 0

/-! ## Packets -/

/-- Bytes as a `0x`-prefixed lowercase hex string. -/
def hex (bytes : List UInt8) : Json :=
  Json.str (Serialization.Ssz.toHex bytes.toArray)

/-- Run a packet operation down to `IO`. -/
def runPacket {α : Type} (act : Except PacketError α) : IO α :=
  match act with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"invalid packet: {repr e}")

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
def decodePacketExport (destId bytes : ByteArray) : IO ByteArray := do
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
def reencodePacketExport (destId bytes : ByteArray) : IO ByteArray := do
  let id ← nodeIdOf destId
  runPacket ((Packet.decode id bytes).bind (Packet.encode id))

/-- An AES-128 key of 16 bytes. -/
def aesKeyOf (bytes : ByteArray) : IO (Cryptography.Aes.Key .aes128) :=
  if h : bytes.size = 16 then pure ⟨bytes.data, h⟩
  else throw (IO.userError "key is not 16 bytes")

/-- A nonce of 12 bytes. -/
def nonceOf (bytes : ByteArray) : IO (Vector UInt8 12) :=
  if h : bytes.size = 12 then pure ⟨bytes.data, h⟩
  else throw (IO.userError "nonce is not 12 bytes")

/-- The encrypted message, the ciphertext then the 16-byte tag. -/
@[export eth_discv5_encrypt_message]
def encryptMessageExport (key nonce plaintext ad : ByteArray) : IO ByteArray := do
  match encryptMessage (← aesKeyOf key) (← nonceOf nonce) plaintext ad with
  | .ok message => pure message
  | .error _ => throw (IO.userError "encryption failed")

/-- The plaintext of an encrypted message, or an error if it does not authenticate. -/
@[export eth_discv5_decrypt_message]
def decryptMessageExport (key nonce message ad : ByteArray) : IO ByteArray := do
  match decryptMessage (← aesKeyOf key) (← nonceOf nonce) message ad with
  | .ok plaintext => pure plaintext
  | .error _ => throw (IO.userError "message does not authenticate")

end EthLib.Networking.Discv5.Exports
