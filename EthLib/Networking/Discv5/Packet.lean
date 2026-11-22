module

public import EthLib.Cryptography.Aes.Ctr
public import EthLib.Cryptography.Aes.Gcm
public import EthLib.Networking.Discv5.Distance

/-!
# `Networking.Discv5.Packet`

The packets of discv5, from the section Packet Encoding of `discv5-wire.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv5/discv5-wire.md>

A packet is a masking IV of 16 bytes, the masked header, then the encrypted message.

The flag selects the authdata: an ordinary message, a WHOAREYOU challenge, or a handshake.

AES-128-CTR masks the header, and AES-128-GCM encrypts the message.
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
  /-- The header does not start with "discv5" and version `0x0001`, but with `found`. -/
  | protocolId (found : List UInt8)
  /-- The packet ends inside its header: the header needs `needed` bytes after the masking IV.

  Only `available` bytes follow the IV. -/
  | headerTruncated (needed available : Nat)
  /-- The flag is not 0, 1 or 2. -/
  | flag (flag : UInt8)
  /-- The authdata of `size` bytes does not have the size or the layout of the flag `flag`. -/
  | authdata (flag : UInt8) (size : Nat)
  /-- A WHOAREYOU packet carries a message of `size` bytes. -/
  | whoareyouMessage (size : Nat)
  /-- A field is too long for its size field. -/
  | fieldTooLong
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PacketError.code : PacketError → UInt32
  | .size _ => 1
  | .protocolId _ => 2
  | .headerTruncated .. => 3
  | .flag _ => 4
  | .authdata .. => 5
  | .whoareyouMessage _ => 6
  | .fieldTooLong => 7

namespace Authdata

/-- The flag of the authdata. -/
def flag : Authdata → UInt8
  -- Ordinary Message Packet: `flag = 0`.
  | .message _ => 0
  -- WHOAREYOU Packet: `flag = 1`.
  | .whoareyou _ _ => 1
  -- Handshake Message Packet: `flag = 2`.
  | .handshake .. => 2

/-- The bytes of the authdata.

The handshake writes the sizes of the signature and of the key in one byte each. -/
def encode : Authdata → List UInt8
  -- Flag 0: `authdata = src-id`.
  | .message srcId => srcId.toList
  -- Flag 1: `authdata = id-nonce || enr-seq`, with `enr-seq` a `uint64` in 8 bytes.
  --
  -- The source gives no byte order for `enr-seq`; EthLib writes it big-endian.
  | .whoareyou idNonce enrSeq => idNonce.toList ++ Base.natToBytes 8 enrSeq.toNat
  -- Flag 2: `authdata = authdata-head || id-signature || eph-pubkey || record`.
  --
  -- And `authdata-head = src-id || sig-size || eph-key-size`, each size a `uint8`.
  | .handshake srcId idSignature ephemeralPubkey record =>
    srcId.toList ++ [UInt8.ofNat idSignature.size, UInt8.ofNat ephemeralPubkey.size] ++
      idSignature.data.toList ++ ephemeralPubkey.data.toList ++ record.data.toList

/-- Whether the sizes of the authdata fit their size fields. -/
def fits : Authdata → Bool
  -- `sig-size` and `eph-key-size` are each a `uint8`, so each size is below 2^8.
  | .handshake _ idSignature ephemeralPubkey _ =>
    idSignature.size < 256 && ephemeralPubkey.size < 256
  | _ => true

/-- A vector of the first `n` bytes of a list that has exactly `n` bytes. -/
def vectorOf (n : Nat) (bytes : List UInt8) : Option (Vector UInt8 n) :=
  Base.exactArray? n bytes.toArray

/-- The authdata of a flag, from its bytes. -/
def decode (flag : UInt8) (bytes : List UInt8) : Except PacketError Authdata :=
  -- Flag 0: `authdata = src-id`, with `authdata-size = 32`.
  if flag = 0 then
    match vectorOf 32 bytes with
    | some srcId => .ok (.message srcId)
    | none => .error (.authdata flag bytes.length)
  -- Flag 1: `authdata = id-nonce || enr-seq`, with `authdata-size = 24`.
  --
  -- `id-nonce` is a `uint128`, and `enr-seq` a `uint64`, which EthLib reads big-endian.
  else if flag = 1 then
    match vectorOf 16 (bytes.take 16) with
    | some idNonce =>
      if bytes.length = 24 then
        .ok (.whoareyou idNonce (UInt64.ofNat (Base.bytesToNat (bytes.drop 16))))
      else .error (.authdata flag bytes.length)
    | none => .error (.authdata flag bytes.length)
  -- Flag 2: `authdata-head = src-id || sig-size || eph-key-size`, 34 bytes.
  --
  -- The source gives the sizes 64 and 33 for the identity scheme v4; any sizes are read here.
  --
  -- The identity scheme checks them, so the packet layer stays the same for every scheme.
  else if flag = 2 then
    match vectorOf 32 (bytes.take 32), bytes.drop 32 with
    | some srcId, sigSize :: keySize :: rest =>
      -- `authdata-size` is 34, plus `sig-size` and `eph-key-size`, plus the length of `record`.
      if sigSize.toNat + keySize.toNat ≤ rest.length then
        let idSignature := rest.take sigSize.toNat
        let ephemeralPubkey := (rest.drop sigSize.toNat).take keySize.toNat
        -- The rest is `record`, empty when the node omits it.
        let record := rest.drop (sigSize.toNat + keySize.toNat)
        .ok (.handshake srcId ⟨idSignature.toArray⟩ ⟨ephemeralPubkey.toArray⟩ ⟨record.toArray⟩)
      else .error (.authdata flag bytes.length)
    | _, _ => .error (.authdata flag bytes.length)
  -- The source defines no other flag.
  else .error (.flag flag)

end Authdata

/-- The unmasked header bytes: the static header, then the authdata. -/
def Header.encode (h : Header) : Except PacketError (List UInt8) :=
  let authdata := h.authdata.encode
  -- `authdata-size` is a `uint16`, so the authdata has fewer than 2^16 bytes.
  if authdata.length < 2 ^ 16 && h.authdata.fits then
    -- `header = static-header || authdata`.
    --
    -- `static-header = protocol-id || version || flag || nonce || authdata-size`.
    .ok (PROTOCOL_ID ++ VERSION ++ [h.authdata.flag] ++ h.nonce.toList ++
      Base.natToBytes 2 authdata.length ++ authdata)
  else .error .fieldTooLong

/-- The masking key: the first 16 bytes of the destination node ID. -/
def maskingKey (destId : NodeId) : Aes.Key .aes128 :=
  -- `masking-key = dest-id[:16]`.
  Vector.ofFn fun i => destId[i.val]

/-- AES-128-CTR under the masking key, from the masking IV as the first counter block.

The counter is the whole 128-bit block. -/
def mask (destId : NodeId) (maskingIv : Vector UInt8 16) (data : List UInt8) : List UInt8 :=
  -- AES/CTR of the data under `masking-key`, from `masking-iv`; decryption is the same map.
  (Aes.ctr (Aes.ciph .aes128 (maskingKey destId)) 128 maskingIv ⟨data.toArray⟩).data.toList

/-- The bytes of a packet for a destination node.

It fails when a field is too long for its size field.

It fails with the size when the packet has more than 1280 bytes, which the decoder rejects. -/
def Packet.encode (destId : NodeId) (p : Packet) : Except PacketError ByteArray := do
  let header ← p.header.encode
  -- `packet = masking-iv || masked-header || message`.
  --
  -- And `masked-header` is `header` under AES/CTR, with `masking-key` and `masking-iv`.
  let bytes : ByteArray :=
    ⟨(p.maskingIv.toList ++ mask destId p.maskingIv header ++ p.message.data.toList).toArray⟩
  -- UDP Communication: implementations should not generate packets larger than 1280 bytes.
  if MAX_PACKET_SIZE < bytes.size then throw (.size bytes.size)
  return bytes

/-- The packet that a destination node reads from bytes.

The decoder unmasks all bytes after the IV, byte by byte, so the header comes back in front.

The message stays as it is in the packet. -/
def Packet.decode (destId : NodeId) (bytes : ByteArray) : Except PacketError Packet := do
  -- UDP Communication: reject packets below 63 bytes, and do not process packets over 1280.
  if bytes.size < MIN_PACKET_SIZE ∨ MAX_PACKET_SIZE < bytes.size then
    throw (.size bytes.size)
  let all := bytes.data.toList
  -- `packet = masking-iv || masked-header || message`, with a 16-byte `masking-iv`.
  let some maskingIv := Authdata.vectorOf 16 (all.take 16) | throw (.size bytes.size)
  let rest := all.drop 16
  -- The recipient unmasks with AES/CTR, under `dest-id[:16]` and the IV of the packet.
  --
  -- The source unmasks the static header, then the authdata; one pass gives the same bytes.
  let plain := mask destId maskingIv rest
  -- `protocol-id = "discv5"`; no response to a packet with another `protocol-id`.
  --
  -- Not in the source: a `version` other than `0x0001` is rejected too.
  unless plain.take 8 = PROTOCOL_ID ++ VERSION do throw (.protocolId (plain.take 8))
  -- `flag`, a `uint8`.
  let some flag := plain[8]? | throw (.headerTruncated STATIC_HEADER_SIZE rest.length)
  -- `nonce`, a `uint96`.
  let some nonce := Authdata.vectorOf 12 ((plain.drop 9).take 12)
    | throw (.headerTruncated STATIC_HEADER_SIZE rest.length)
  -- `authdata-size`, a `uint16`; the source gives no byte order, and EthLib reads it big-endian.
  let authdataSize := Base.bytesToNat ((plain.drop 21).take 2)
  -- `header = static-header || authdata`, so the header has `23 + authdata-size` bytes.
  if rest.length < STATIC_HEADER_SIZE + authdataSize then
    throw (.headerTruncated (STATIC_HEADER_SIZE + authdataSize) rest.length)
  -- The `flag` determines the encoding of `authdata`.
  let authdata ← Authdata.decode flag ((plain.drop STATIC_HEADER_SIZE).take authdataSize)
  -- The `message` follows the header, still encrypted.
  let message := rest.drop (STATIC_HEADER_SIZE + authdataSize)
  -- WHOAREYOU Packet: the `message` part is always empty.
  if flag = 1 ∧ message ≠ [] then throw (.whoareyouMessage message.length)
  return ⟨maskingIv, ⟨nonce, authdata⟩, ⟨message.toArray⟩⟩

/-- The additional data of the message: the masking IV, then the unmasked header. -/
def Packet.messageAd (p : Packet) : Except PacketError ByteArray := do
  -- `message-ad = masking-iv || header`.
  return ⟨(p.maskingIv.toList ++ (← p.header.encode)).toArray⟩

/-- The size of the GCM tag that follows the ciphertext, in bytes. -/
def TAG_SIZE : Nat := 16

/-- The encrypted message: AES-128-GCM of the plaintext, then its 16-byte tag. -/
def encryptMessage (key : Aes.Key .aes128) (nonce : Vector UInt8 12) (plaintext ad : ByteArray) :
    Except Aes.Gcm.Error ByteArray := do
  -- AES-GCM of the plaintext and the additional data, with a 16-byte key and a 12-byte nonce.
  --
  -- The source fixes no tag size; EthLib appends the full 16-byte tag of GCM.
  let (c, tag) ← Aes.Gcm.encrypt (Aes.ciph .aes128 key) TAG_SIZE ⟨nonce.toArray⟩ plaintext ad
  return c ++ tag

/-- The plaintext of an encrypted message, or an error if it does not authenticate. -/
def decryptMessage (key : Aes.Key .aes128) (nonce : Vector UInt8 12) (message ad : ByteArray) :
    Except Aes.Gcm.Error ByteArray :=
  -- The last 16 bytes are the tag; a shorter message gives a shorter tag, which GCM rejects.
  let n := message.size - TAG_SIZE
  Aes.Gcm.decrypt (Aes.ciph .aes128 key) TAG_SIZE ⟨nonce.toArray⟩ (message.extract 0 n) ad
    (message.extract n message.size)

/-! ## Sealing and opening a message packet -/

/-- A message packet to `destId`, with its message encrypted under `key`.

The two functions give the error of the caller, for the packet and for the encryption.

It fails when a field is too long for its size field, or the packet would exceed 1280 bytes.

It fails with the cipher error when the encryption rejects the plaintext. -/
def sealPacket {ε : Type} (packetError : PacketError → ε) (encryptionError : Aes.Gcm.Error → ε)
    (key : Aes.Key .aes128) (destId : NodeId) (maskingIv : Vector UInt8 16) (header : Header)
    (plaintext : ByteArray) : Except ε ByteArray := do
  -- `message-ad = masking-iv || header`.
  let ad ← (Packet.messageAd ⟨maskingIv, header, .empty⟩).mapError packetError
  -- `message` is AES-GCM of `message-pt` and `message-ad`, under `key` and the header's nonce.
  let message ← (encryptMessage key header.nonce plaintext ad).mapError encryptionError
  -- `packet = masking-iv || masked-header || message`.
  (Packet.encode destId ⟨maskingIv, header, message⟩).mapError packetError

/-- The plaintext of a decoded message packet, decrypted under `key`.

The two functions give the error of the caller, for the packet and for the decryption. -/
def openPacket {ε : Type} (packetError : PacketError → ε) (decryptionError : Aes.Gcm.Error → ε)
    (key : Aes.Key .aes128) (packet : Packet) : Except ε ByteArray := do
  -- `message-ad = masking-iv || header`, with the header encoded again from its fields.
  --
  -- A decoded header encodes back to the bytes it was read from, so the data is the same.
  let ad ← packet.messageAd.mapError packetError
  -- The message decrypts and authenticates under `key` and the nonce of the header.
  (decryptMessage key packet.header.nonce packet.message ad).mapError decryptionError

end EthLib.Networking.Discv5
