module

public import EthLib.Networking.Quic.Keys
public import EthLib.Networking.Quic.Packet
public import EthLib.Cryptography.Aes.Gcm
public import EthLib.Cryptography.ChaCha20Poly1305
public import EthLib.Base.Except
public import EthLib.Base.BigEndian

/-!
# QUIC v1 packet protection

Payload protection and header protection follow [RFC 9001 §§5.3 to 5.4][rfc].

The caller isolates one packet and supplies its packet-number offset from the clear header.

Retry integrity follows [RFC 9001 §5.8][retry].

Nothing here tracks nonce reuse, key updates or the usage limits of §6.6.

Nothing here claims constant-time execution.

[rfc]: https://www.rfc-editor.org/rfc/rfc9001#section-5.3
[retry]: https://www.rfc-editor.org/rfc/rfc9001#section-5.8
-/

@[expose] public section

namespace EthLib.Networking.Quic.Protection

open EthLib.Base EthLib.Cryptography

/-- A full packet number, a QUIC integer below `2^62` (RFC 9000 §12.3). -/
abbrev PacketNumber := Varint

/-- Failures of packet protection and Retry integrity, reserved bits after AEAD included. -/
inductive Error where
  | header
  | sample
  | packetNumber
  | tagLength
  | aes (reason : Aes.Gcm.Error)
  | chacha (reason : ChaCha20Poly1305.ChaCha20Poly1305Error)
  | connectionId
  /-- The payload authenticated, but a reserved bit is set, RFC 9000 §§17.2, 17.3.1. -/
  | reservedBits
  deriving DecidableEq, Repr

/-- Stable codes for packet-protection failures at the Python boundary. -/
def Error.code : Error → UInt32
  | .header => 1
  | .sample => 2
  | .packetNumber => 3
  | .tagLength => 4
  | .aes _ => 5
  | .chacha _ => 6
  | .connectionId => 7
  | .reservedBits => 8

/-- XOR the IV with the left-zero-padded, network-order packet number, RFC 9001 §5.3. -/
def nonce (iv : Vector UInt8 12) (number : PacketNumber) : Vector UInt8 12 :=
  Vector.ofFn fun i => iv[i] ^^^ UInt8.ofNat (number.val / 256 ^ (11 - i.val))

/-- The first five AES or ChaCha20 output bytes mask the header, RFC 9001 §§5.4.3 to 5.4.4. -/
def headerMask (suite : CipherSuite) (key : Vector UInt8 suite.keyLength)
    (sample : Vector UInt8 16) : Vector UInt8 5 :=
  match suite with
  | .aes128GcmSha256 =>
    let block := Aes.ciph .aes128 key sample
    Vector.ofFn fun i => block[i.val]'(by omega)
  | .chacha20Poly1305Sha256 =>
    let counter := uint32OfBytes sample[0] sample[1] sample[2] sample[3]
    let iv : Vector UInt8 12 := Vector.ofFn fun i => sample[4 + i.val]'(by omega)
    let block := ChaCha20Poly1305.block key counter iv
    Vector.ofFn fun i => block[i.val]'(by omega)

/-- Encrypt a payload and return its ciphertext and tag, RFC 9001 §5.3.

The additional data is the entire unprotected header, including its encoded packet number. -/
def encryptPayload (suite : CipherSuite) (keys : PacketKeys suite) (number : PacketNumber)
    (header plaintext : ByteArray) : Except Error (ByteArray × ByteArray) :=
  match suite with
  | .aes128GcmSha256 =>
    (Aes.Gcm.encrypt (Aes.ciph .aes128 keys.key) 16 (packBytes (nonce keys.iv number))
      plaintext header).mapError .aes
  | .chacha20Poly1305Sha256 =>
    ((ChaCha20Poly1305.encrypt keys.key (nonce keys.iv number) header plaintext).map
      fun (ciphertext, tag) => (ciphertext, packBytes tag)).mapError .chacha

/-- Authenticate the payload under the recovered header and packet number, RFC 9001 §5.3. -/
def decryptPayload (suite : CipherSuite) (keys : PacketKeys suite) (number : PacketNumber)
    (header ciphertext tag : ByteArray) : Except Error ByteArray :=
  match suite with
  | .aes128GcmSha256 =>
    (Aes.Gcm.decrypt (Aes.ciph .aes128 keys.key) 16 (packBytes (nonce keys.iv number))
      ciphertext header tag).mapError .aes
  | .chacha20Poly1305Sha256 =>
    if h : tag.size = 16 then
      (ChaCha20Poly1305.decrypt keys.key (nonce keys.iv number) header ciphertext
        (readBytes tag 0 16 (by omega))).mapError .chacha
    else .error .tagLength

/-- One byte's mask, with four low first-byte bits for long headers and five for short ones.

The offset and width select only the encoded packet number, RFC 9001 §5.4.1. -/
def maskByte (longHeader : Bool) (offset : Nat) (width : Packet.PacketNumberLength)
    (mask : Vector UInt8 5) (i : Nat) : UInt8 :=
  if i = 0 then mask[0] &&& (if longHeader then 0x0f else 0x1f)
  else if h : offset ≤ i ∧ i < offset + (width.val + 1) then
    mask[i - offset + 1]'(by omega)
  else 0

/-- Apply the header mask without changing the ciphertext, RFC 9001 §5.4.1. -/
def applyMask (longHeader : Bool) (offset : Nat) (width : Packet.PacketNumberLength)
    (mask : Vector UInt8 5) (bytes : ByteArray) : ByteArray :=
  ⟨(bytes.data.toList.mapIdx fun i b => b ^^^ maskByte longHeader offset width mask i).toArray⟩

/-- Read the full 16-byte ciphertext sample at `pn_offset + 4`, RFC 9001 §5.4.2. -/
def sample (bytes : ByteArray) (offset : Nat) : Except Error (Vector UInt8 16) :=
  if h : offset + 4 + 16 ≤ bytes.size then
    .ok (readBytes bytes (offset + 4) 16 h)
  else .error .sample

/-- The recovered header and ciphertext, before packet-number reconstruction and AEAD. -/
structure Unmasked where
  header : ByteArray
  ciphertext : ByteArray
  tag : ByteArray
  truncatedNumber : Nat
  width : Packet.PacketNumberLength
  deriving DecidableEq

/-- Remove header protection from one isolated packet, RFC 9001 §§5.4.1 to 5.4.2.

The caller obtains the offset from the unprotected portion of the header.

Reserved bits are checked only after the payload authenticates. -/
def removeHeaderProtection (suite : CipherSuite) (hp : Vector UInt8 suite.keyLength)
    (offset : Nat) (packet : ByteArray) : Except Error Unmasked := do
  ensure (0 < offset ∧ offset < packet.size) .header
  let sample ← sample packet offset
  let mask := headerMask suite hp sample
  if h : 0 < packet.size then
    let first := packet[0]
    let longHeader := first &&& 0x80 != 0
    let first := first ^^^ (mask[0] &&& (if longHeader then 0x0f else 0x1f))
    let width := Packet.widthOfFirst first
    ensure (offset + width.val + 1 + 16 ≤ packet.size) .header
    let bytes := applyMask longHeader offset width mask packet
    let endHeader := offset + width.val + 1
    return ⟨bytes.extract 0 endHeader, bytes.extract endHeader (bytes.size - 16),
      bytes.extract (bytes.size - 16) bytes.size,
      bytesToNat (bytes.extract offset endHeader).data.toList, width⟩
  else throw .header

/-- Check the fixed bit and the reserved bits after authentication, RFC 9000 §§17.2, 17.3.1. -/
def checkAuthenticatedHeader (header : ByteArray) : Except Error Unit :=
  if h : 0 < header.size then
    let first := header[0]
    let reserved := if first &&& 0x80 != 0 then 0x0c else 0x18
    ensure (first &&& 0x40 != 0 ∧ first &&& reserved = 0) .header
  else .error .header

/-- Reject reserved bits, mask 0x0c long or 0x18 short, in an authenticated header (§§17.2, 17.3.1).

The header checks then reject a header that is not a protected version 1 packet. -/
def checkReservedBits (header : ByteArray) : Except Error Unit :=
  if h : 0 < header.size then
    let first := header[0]
    let reserved := if first &&& 0x80 != 0 then 0x0c else 0x18
    ensure (first &&& 0x40 = 0 ∨ first &&& reserved = 0) .reservedBits
  else .ok ()

/-- Initial packets always use AES-128-GCM, independently of TLS negotiation, RFC 9001 §5. -/
def checkSuite (suite : CipherSuite) : Packet.Header → Except Error Unit
  | .initial .. => ensure (suite = .aes128GcmSha256) .header
  | _ => pure ()

/-- Check an authenticated header against the wire codec and isolated payload length.

A long header's Length counts the packet number and the protected payload, RFC 9000 §17.2.

Retry and Version Negotiation packets carry no protected payload and fail here. -/
def checkHeader (suite : CipherSuite) (header : ByteArray) (protectedLength : Nat) :
    Except Error Unit := do
  checkAuthenticatedHeader header
  if h : 0 < header.size then
    let width := Packet.widthOfFirst header[0]
    let (decoded, trailing) ← (Packet.decode (header.size - (width.val + 1) - 1)
      header.data.toList).mapError fun _ => .header
    ensure (trailing = []) .header
    checkSuite suite decoded
    match decoded with
    | .initial _ _ _ w length _ | .zeroRtt _ _ w length _ | .handshake _ _ w length _ =>
      ensure (length.val = w.val + 1 + protectedLength) .header
    | .oneRtt .. => pure ()
    | .retry .. | .versionNegotiation .. => throw .header
  else throw .header

/-- Protect a header and payload, RFC 9001 §§5.3 to 5.4.

The caller supplies `offset` and a header ending in the truncated packet number.

An insufficient ciphertext sample is an error, so callers add PADDING frames before sealing. -/
def protect (suite : CipherSuite) (keys : PacketKeys suite) (number : PacketNumber)
    (offset : Nat) (header plaintext : ByteArray) : Except Error ByteArray := do
  checkHeader suite header (plaintext.size + 16)
  if h : 0 < header.size then
    let first := header[0]
    let width := Packet.widthOfFirst first
    ensure (0 < offset ∧ header.size = offset + width.val + 1) .header
    ensure (bytesToNat (header.extract offset header.size).data.toList =
      number.val % 256 ^ (width.val + 1)) .packetNumber
    let (ciphertext, tag) ← encryptPayload suite keys number header plaintext
    let packet := header ++ ciphertext ++ tag
    let sample ← sample packet offset
    return applyMask (first &&& 0x80 != 0) offset width (headerMask suite keys.hp sample) packet
  else throw .header

/-- Reconstruct a full packet number for the receiver's packet-number space, RFC 9000 Appendix A.3.

`expected` is one greater than the largest authenticated packet number, or zero initially. -/
def reconstructNumber (width : Packet.PacketNumberLength) (truncated expected : Nat) :
    Except Error PacketNumber := do
  let number ← (Packet.decodePacketNumber width truncated expected).mapError fun _ => .packetNumber
  if h : number < 2 ^ 62 then return ⟨number, h⟩ else throw .packetNumber

/-- Authenticate one isolated packet, RFC 9001 §§5.3 to 5.4.

The caller supplies the packet-number offset from the clear header fields and connection context.

The expected number is one greater than the largest authenticated number, or zero initially.

Nonzero reserved bits in an authenticated header give their own error, before the other checks.

RFC 9000 §§17.2 and 17.3.1 make nonzero reserved bits a connection error.

The other failures reject only this packet. -/
def unprotect (suite : CipherSuite) (keys : PacketKeys suite) (expected : Nat)
    (offset : Nat) (packet : ByteArray) : Except Error (ByteArray × ByteArray) := do
  let recovered ← removeHeaderProtection suite keys.hp offset packet
  let number ← reconstructNumber recovered.width recovered.truncatedNumber expected
  let plaintext ← decryptPayload suite keys number recovered.header
    recovered.ciphertext recovered.tag
  checkReservedBits recovered.header
  -- Only the reserved-bit check may report its own error after authentication.
  (checkHeader suite recovered.header (recovered.ciphertext.size + recovered.tag.size)).mapError
    fun _ => .header
  return (recovered.header, plaintext)

/-- The fixed QUIC v1 Retry key, RFC 9001 §5.8. -/
def RETRY_KEY : Vector UInt8 16 :=
  #v[0xbe, 0x0c, 0x69, 0x0b, 0x9f, 0x66, 0x57, 0x5a,
    0x1d, 0x76, 0x6b, 0x54, 0xe3, 0x68, 0xc8, 0x4e]

/-- The fixed QUIC v1 Retry nonce, RFC 9001 §5.8. -/
def RETRY_NONCE : Vector UInt8 12 :=
  #v[0x46, 0x15, 0x99, 0xd3, 0x5d, 0x63, 0x2b, 0xf2, 0x23, 0x98, 0x25, 0xbb]

/-- Authenticate the Retry pseudo-packet with empty plaintext, RFC 9001 §5.8.

`retry` is the Retry packet without its integrity tag.

The caller checks its header format. -/
def retryTag (originalDcid retry : ByteArray) : Except Error ByteArray := do
  ensure (originalDcid.size ≤ 20) .connectionId
  let aad := ByteArray.mk #[UInt8.ofNat originalDcid.size] ++ originalDcid ++ retry
  let (_, tag) ← (Aes.Gcm.encrypt (Aes.ciph .aes128 RETRY_KEY) 16
    (packBytes RETRY_NONCE) .empty aad).mapError .aes
  return tag

end EthLib.Networking.Quic.Protection
