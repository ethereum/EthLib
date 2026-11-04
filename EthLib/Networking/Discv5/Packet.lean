module

public import EthLib.Cryptography.Aes.Ctr
public import EthLib.Cryptography.Aes.Gcm
public import EthLib.Networking.Discv5.Distance

/-!
# `Networking.Discv5.Packet`

The packets of discv5, from "Packet Encoding" of `discv5-wire.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-wire.md>

A packet is a masking IV of 16 bytes, the masked header, then the encrypted message.

The header is `"discv5" || 0x0001 || flag || nonce || authdata-size || authdata`.

The flag has 1 byte, the nonce 12 and the size 2, big-endian.

AES-128-CTR masks the header, with the first 16 bytes of the destination ID as the key.

The flag selects the authdata: an ordinary message, a WHOAREYOU challenge, or a handshake.

AES-128-GCM encrypts the message, with the masking IV and the header as additional data.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Cryptography

/-- The protocol ID at the start of every header, "discv5" in ASCII. -/
def PROTOCOL_ID : List UInt8 := [0x64, 0x69, 0x73, 0x63, 0x76, 0x35]

/-- The protocol version of the header, `0x0001`. -/
def VERSION : List UInt8 := [0x00, 0x01]

/-- The size of the header before the authdata: 6 + 2 + 1 + 12 + 2 bytes. -/
def STATIC_HEADER_SIZE : Nat := 23

/-- The smallest packet, in bytes. -/
def MIN_PACKET_SIZE : Nat := 63

/-- The largest packet, in bytes. -/
def MAX_PACKET_SIZE : Nat := 1280

/-- The authdata of a packet, one form for each flag. -/
inductive Authdata where
  /-- Flag 0, an ordinary message: the ID of the source node. -/
  | message (srcId : NodeId)
  /-- Flag 1, a WHOAREYOU challenge: the ID nonce and the sequence number of the known ENR. -/
  | whoareyou (idNonce : Vector UInt8 16) (enrSeq : UInt64)
  /-- Flag 2, a handshake: the source ID, the ID signature, the ephemeral key and an ENR. -/
  | handshake (srcId : NodeId) (idSignature ephemeralPubkey record : ByteArray)
  deriving DecidableEq

/-- The header of a packet, after unmasking: the nonce and the authdata. -/
structure Header where
  /-- The nonce of the message, 12 bytes. -/
  nonce : Vector UInt8 12
  /-- The authdata, whose form gives the flag. -/
  authdata : Authdata
  deriving DecidableEq

/-- A packet: the masking IV, the header and the encrypted message. -/
structure Packet where
  /-- The 16 random bytes that start the packet. -/
  maskingIv : Vector UInt8 16
  /-- The header, unmasked. -/
  header : Header
  /-- The encrypted message, empty in a WHOAREYOU packet. -/
  message : ByteArray
  deriving DecidableEq

/-- Every way a packet can be rejected. -/
inductive PacketError where
  /-- The packet has fewer than 63 or more than 1280 bytes. -/
  | size (size : Nat)
  /-- The header does not start with "discv5" and version `0x0001`. -/
  | protocolId
  /-- The packet ends inside its header. -/
  | headerTruncated
  /-- The flag is not 0, 1 or 2. -/
  | flag (flag : UInt8)
  /-- The authdata does not have the size or the layout of its flag. -/
  | authdata
  /-- A WHOAREYOU packet carries a message. -/
  | whoareyouMessage
  /-- A field is too long for its size field. -/
  | fieldTooLong
  deriving DecidableEq, Repr

namespace Authdata

/-- The flag of the authdata. -/
def flag : Authdata → UInt8
  | .message _ => 0
  | .whoareyou _ _ => 1
  | .handshake .. => 2

/-- The bytes of the authdata.

The handshake writes the sizes of the signature and of the key in one byte each. -/
def encode : Authdata → List UInt8
  | .message srcId => srcId.toList
  | .whoareyou idNonce enrSeq => idNonce.toList ++ Base.natToBytes 8 enrSeq.toNat
  | .handshake srcId idSignature ephemeralPubkey record =>
    srcId.toList ++ [UInt8.ofNat idSignature.size, UInt8.ofNat ephemeralPubkey.size] ++
      idSignature.data.toList ++ ephemeralPubkey.data.toList ++ record.data.toList

/-- Whether the sizes of the authdata fit their size fields. -/
def fits : Authdata → Bool
  | .handshake _ idSignature ephemeralPubkey _ =>
    idSignature.size < 256 && ephemeralPubkey.size < 256
  | _ => true

/-- A vector of the first `n` bytes of a list that has exactly `n` bytes. -/
def vectorOf (n : Nat) (bytes : List UInt8) : Option (Vector UInt8 n) :=
  if h : bytes.length = n then some ⟨bytes.toArray, by simpa using h⟩ else none

/-- The authdata of a flag, from its bytes. -/
def decode (flag : UInt8) (bytes : List UInt8) : Except PacketError Authdata :=
  if flag = 0 then
    match vectorOf 32 bytes with
    | some srcId => .ok (.message srcId)
    | none => .error .authdata
  else if flag = 1 then
    -- The ID nonce, then the ENR sequence number as 8 big-endian bytes.
    match vectorOf 16 (bytes.take 16) with
    | some idNonce =>
      if bytes.length = 24 then
        .ok (.whoareyou idNonce (UInt64.ofNat (Base.bytesToNat (bytes.drop 16))))
      else .error .authdata
    | none => .error .authdata
  else if flag = 2 then
    match vectorOf 32 (bytes.take 32), bytes.drop 32 with
    | some srcId, sigSize :: keySize :: rest =>
      if sigSize.toNat + keySize.toNat ≤ rest.length then
        let idSignature := rest.take sigSize.toNat
        let ephemeralPubkey := (rest.drop sigSize.toNat).take keySize.toNat
        let record := rest.drop (sigSize.toNat + keySize.toNat)
        .ok (.handshake srcId ⟨idSignature.toArray⟩ ⟨ephemeralPubkey.toArray⟩ ⟨record.toArray⟩)
      else .error .authdata
    | _, _ => .error .authdata
  else .error (.flag flag)

end Authdata

/-- The unmasked header bytes: the static header, then the authdata. -/
def Header.encode (h : Header) : Except PacketError (List UInt8) :=
  let authdata := h.authdata.encode
  if authdata.length < 2 ^ 16 && h.authdata.fits then
    .ok (PROTOCOL_ID ++ VERSION ++ [h.authdata.flag] ++ h.nonce.toList ++
      Base.natToBytes 2 authdata.length ++ authdata)
  else .error .fieldTooLong

/-- The masking key: the first 16 bytes of the destination node ID. -/
def maskingKey (destId : NodeId) : Aes.Key .aes128 :=
  Vector.ofFn fun i => destId[i.val]

/-- AES-128-CTR under the masking key, from the masking IV as the first counter block.

The counter is the whole 128-bit block. -/
def mask (destId : NodeId) (maskingIv : Vector UInt8 16) (data : List UInt8) : List UInt8 :=
  (Aes.ctr (Aes.ciph .aes128 (maskingKey destId)) 128 maskingIv ⟨data.toArray⟩).data.toList

/-- The bytes of a packet for a destination node.

It fails when a field is too long for its size field. -/
def Packet.encode (destId : NodeId) (p : Packet) : Except PacketError ByteArray := do
  let header ← p.header.encode
  return ⟨(p.maskingIv.toList ++ mask destId p.maskingIv header ++ p.message.data.toList).toArray⟩

/-- The packet that a destination node reads from bytes.

The decoder unmasks all bytes after the IV, byte by byte, so the header comes back in front.

The message stays as it is in the packet. -/
def Packet.decode (destId : NodeId) (bytes : ByteArray) : Except PacketError Packet := do
  if bytes.size < MIN_PACKET_SIZE ∨ MAX_PACKET_SIZE < bytes.size then
    throw (.size bytes.size)
  let all := bytes.data.toList
  let some maskingIv := Authdata.vectorOf 16 (all.take 16) | throw (.size bytes.size)
  let rest := all.drop 16
  let plain := mask destId maskingIv rest
  -- The static header: protocol ID, version, flag, nonce and authdata size.
  unless plain.take 8 = PROTOCOL_ID ++ VERSION do throw .protocolId
  let some flag := plain[8]? | throw .headerTruncated
  let some nonce := Authdata.vectorOf 12 ((plain.drop 9).take 12) | throw .headerTruncated
  let authdataSize := Base.bytesToNat ((plain.drop 21).take 2)
  if rest.length < STATIC_HEADER_SIZE + authdataSize then throw .headerTruncated
  let authdata ← Authdata.decode flag ((plain.drop STATIC_HEADER_SIZE).take authdataSize)
  let message := rest.drop (STATIC_HEADER_SIZE + authdataSize)
  if flag = 1 ∧ message ≠ [] then throw .whoareyouMessage
  return ⟨maskingIv, ⟨nonce, authdata⟩, ⟨message.toArray⟩⟩

/-- The additional data of the message: the masking IV, then the unmasked header. -/
def Packet.messageAd (p : Packet) : Except PacketError ByteArray := do
  return ⟨(p.maskingIv.toList ++ (← p.header.encode)).toArray⟩

/-- The size of the GCM tag that follows the ciphertext, in bytes. -/
def TAG_SIZE : Nat := 16

/-- The encrypted message: AES-128-GCM of the plaintext, then its 16-byte tag. -/
def encryptMessage (key : Aes.Key .aes128) (nonce : Vector UInt8 12) (plaintext ad : ByteArray) :
    Except Aes.Gcm.Error ByteArray := do
  let (c, tag) ← Aes.Gcm.encrypt (Aes.ciph .aes128 key) TAG_SIZE ⟨nonce.toArray⟩ plaintext ad
  return c ++ tag

/-- The plaintext of an encrypted message, or an error if it does not authenticate. -/
def decryptMessage (key : Aes.Key .aes128) (nonce : Vector UInt8 12) (message ad : ByteArray) :
    Except Aes.Gcm.Error ByteArray :=
  let n := message.size - TAG_SIZE
  Aes.Gcm.decrypt (Aes.ciph .aes128 key) TAG_SIZE ⟨nonce.toArray⟩ (message.extract 0 n) ad
    (message.extract n message.size)

end EthLib.Networking.Discv5
