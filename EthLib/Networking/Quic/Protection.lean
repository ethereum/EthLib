module

public import EthLib.Networking.Quic.Keys
public import EthLib.Networking.Quic.Packet
public import EthLib.Cryptography.Aes.Gcm
public import EthLib.Cryptography.ChaCha20Poly1305
public import EthLib.Base.Except
public import EthLib.Base.BigEndian
public import EthLib.Base.Word32

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
  /-- A header does not fit the packet, or is not a protected version 1 header. -/
  | header
  /-- The 16-byte sample at `offset + 4` does not fit the packet of `size` bytes (RFC 9001 §5.4.2).

  The field `offset` is the packet number offset. -/
  | sample (offset size : Nat)
  /-- The packet number does not fit its encoded bytes, or cannot be reconstructed. -/
  | packetNumber
  /-- The authentication tag has `size` bytes, not 16. -/
  | tagLength (size : Nat)
  /-- AES-128-GCM failed. -/
  | aes (reason : Aes.Gcm.Error)
  /-- ChaCha20-Poly1305 failed. -/
  | chacha (reason : ChaCha20Poly1305.ChaCha20Poly1305Error)
  /-- The original destination connection ID has `length` bytes, more than 20. -/
  | connectionId (length : Nat)
  /-- The payload authenticated, but a reserved bit is set, RFC 9000 §§17.2, 17.3.1. -/
  | reservedBits
  deriving DecidableEq, Repr

/-- Stable codes for packet-protection failures at the Python boundary. -/
def Error.code : Error → UInt32
  | .header => 1
  | .sample .. => 2
  | .packetNumber => 3
  | .tagLength _ => 4
  | .aes _ => 5
  | .chacha _ => 6
  | .connectionId _ => 7
  | .reservedBits => 8

/-- The AEAD nonce of a packet, RFC 9001 §5.3. -/
def nonce (iv : Vector UInt8 12) (number : PacketNumber) : Vector UInt8 12 :=
  -- The 62 bits of the packet number in network byte order, left-padded with zeros to 12 bytes.
  --
  -- The exclusive OR of the padded packet number and the IV forms the nonce `N`.
  Vector.ofFn fun i => iv[i] ^^^ UInt8.ofNat (number.val / 256 ^ (11 - i.val))

/-- The 5-byte header-protection mask of a ciphertext sample, RFC 9001 §§5.4.3 to 5.4.4. -/
def headerMask (suite : CipherSuite) (key : Vector UInt8 suite.keyLength)
    (sample : Vector UInt8 16) : Vector UInt8 5 :=
  match suite with
  | .aes128GcmSha256 =>
    -- §5.4.3: `mask = AES-ECB(hp_key, sample)`, with 128-bit AES for AEAD_AES_128_GCM.
    let block := Aes.ciph .aes128 key sample
    -- The mask of §5.4.1 has 5 bytes: the first 5 of the block.
    Vector.ofFn fun i => block[i.val]'(by omega)
  | .chacha20Poly1305Sha256 =>
    -- §5.4.4: `counter = sample[0..3]`, read as a little-endian 32-bit integer.
    let counter := uint32OfBytes sample[0] sample[1] sample[2] sample[3]
    -- `nonce = sample[4..15]`.
    let iv : Vector UInt8 12 := Vector.ofFn fun i => sample[4 + i.val]'(by omega)
    -- `mask = ChaCha20(hp_key, counter, nonce, {0,0,0,0,0})`.
    --
    -- Five zero bytes XOR the key stream give its first 5 bytes, so EthLib reads them directly.
    let block := ChaCha20Poly1305.block key counter iv
    Vector.ofFn fun i => block[i.val]'(by omega)

/-- Encrypt a payload and return its ciphertext and tag, RFC 9001 §5.3.

The additional data is the entire unprotected header, including its encoded packet number. -/
def encryptPayload (suite : CipherSuite) (keys : PacketKeys suite) (number : PacketNumber)
    (header plaintext : ByteArray) : Except Error (ByteArray × ByteArray) :=
  -- The AEAD of the cipher suite, with the key `K`, the nonce `N`, the plaintext `P`.
  --
  -- The associated data `A` is the header, up to and including the unprotected packet number.
  match suite with
  -- AEAD_AES_128_GCM, with its 16-byte tag.
  | .aes128GcmSha256 =>
    (Aes.Gcm.encrypt (Aes.ciph .aes128 keys.key) 16 (packBytes (nonce keys.iv number))
      plaintext header).mapError .aes
  -- AEAD_CHACHA20_POLY1305, with its 16-byte tag.
  | .chacha20Poly1305Sha256 =>
    ((ChaCha20Poly1305.encrypt keys.key (nonce keys.iv number) header plaintext).map
      fun (ciphertext, tag) => (ciphertext, packBytes tag)).mapError .chacha

/-- Authenticate the payload under the recovered header and packet number, RFC 9001 §5.3. -/
def decryptPayload (suite : CipherSuite) (keys : PacketKeys suite) (number : PacketNumber)
    (header ciphertext tag : ByteArray) : Except Error ByteArray :=
  -- The AEAD opens `C` with the key `K`, the nonce `N` and the recovered header as `A`.
  match suite with
  -- AEAD_AES_128_GCM, with its 16-byte tag.
  | .aes128GcmSha256 =>
    (Aes.Gcm.decrypt (Aes.ciph .aes128 keys.key) 16 (packBytes (nonce keys.iv number))
      ciphertext header tag).mapError .aes
  -- AEAD_CHACHA20_POLY1305, whose tag has exactly 16 bytes; another size fails first.
  | .chacha20Poly1305Sha256 => do
    let tag ← exactBytes 16 tag .tagLength
    (ChaCha20Poly1305.decrypt keys.key (nonce keys.iv number) header ciphertext tag).mapError
      .chacha

/-- One byte's mask, with four low first-byte bits for long headers and five for short ones.

The offset and width select only the encoded packet number, RFC 9001 §5.4.1. -/
def maskByte (longHeader : Bool) (offset : Nat) (width : Packet.PacketNumberLength)
    (mask : Vector UInt8 5) (i : Nat) : UInt8 :=
  -- Figure 6: `packet[0] ^= mask[0] & 0x0f` for a long header, 4 bits masked.
  --
  -- For a short header, `packet[0] ^= mask[0] & 0x1f`, 5 bits masked.
  if i = 0 then mask[0] &&& (if longHeader then 0x0f else 0x1f)
  -- `packet[pn_offset:pn_offset+pn_length] ^= mask[1:1+pn_length]`.
  else if h : offset ≤ i ∧ i < offset + (width.val + 1) then
    mask[i - offset + 1]'(by omega)
  -- Every other byte is left as it is.
  else 0

/-- Apply the header mask without changing the ciphertext, RFC 9001 §5.4.1. -/
def applyMask (longHeader : Bool) (offset : Nat) (width : Packet.PacketNumberLength)
    (mask : Vector UInt8 5) (bytes : ByteArray) : ByteArray :=
  -- Each byte of the packet, XOR its byte of the mask.
  ⟨(bytes.data.toList.mapIdx fun i b => b ^^^ maskByte longHeader offset width mask i).toArray⟩

/-- Read the full 16-byte ciphertext sample at `pn_offset + 4`, RFC 9001 §5.4.2. -/
def sample (bytes : ByteArray) (offset : Nat) : Except Error (Vector UInt8 16) :=
  -- `sample_offset = pn_offset + 4`, and the sample has 16 bytes for these cipher suites.
  if h : offset + 4 + 16 ≤ bytes.size then
    -- `sample = packet[sample_offset..sample_offset+sample_length]`.
    .ok (readBytes bytes (offset + 4) 16 h)
  -- An endpoint MUST discard packets that are not long enough to contain a complete sample.
  else .error (.sample offset bytes.size)

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
  -- Not in §5.4: the Packet Number field starts inside the packet, after byte 0.
  ensure (0 < offset ∧ offset < packet.size) .header
  -- §5.4.2: the sample at `pn_offset + 4`, as if the Packet Number field had 4 bytes.
  let sample ← sample packet offset
  -- `mask = header_protection(hp_key, sample)`.
  let mask := headerMask suite hp sample
  if h : 0 < packet.size then
    let first := packet[0]
    -- `(packet[0] & 0x80) == 0x80` is a long header.
    let longHeader := first &&& 0x80 != 0
    -- `packet[0] ^= mask[0] & 0x0f` for a long header, or `& 0x1f` for a short one.
    let first := first ^^^ (mask[0] &&& (if longHeader then 0x0f else 0x1f))
    -- `pn_length = (packet[0] & 0x03) + 1`, read after byte 0 is unmasked.
    --
    -- The line reads the two-bit field, which is `pn_length - 1`.
    let width := Packet.widthOfFirst first
    -- Not in §5.4: the packet holds the Packet Number field and a 16-byte tag.
    ensure (offset + width.val + 1 + 16 ≤ packet.size) .header
    -- Figure 6 on the protected packet unmasks byte 0 and the Packet Number field.
    let bytes := applyMask longHeader offset width mask packet
    -- The header ends with the Packet Number field: it is the associated data `A` of §5.3.
    let endHeader := offset + width.val + 1
    -- The header, then the protected payload without its last 16 bytes, then the 16-byte tag.
    return ⟨bytes.extract 0 endHeader, bytes.extract endHeader (bytes.size - 16),
      bytes.extract (bytes.size - 16) bytes.size,
      -- The truncated packet number, in network byte order.
      bytesToNat (bytes.extract offset endHeader).data.toList, width⟩
  else throw .header

/-- Check the fixed bit and the reserved bits after authentication, RFC 9000 §§17.2, 17.3.1. -/
def checkAuthenticatedHeader (header : ByteArray) : Except Error Unit :=
  if h : 0 < header.size then
    let first := header[0]
    -- The Reserved Bits: mask 0x0c in a long header, 0x18 in a short one.
    let reserved := if first &&& 0x80 != 0 then 0x0c else 0x18
    -- Fixed Bit 0x40 is 1, and the Reserved Bits are 0.
    ensure (first &&& 0x40 != 0 ∧ first &&& reserved = 0) .header
  -- An empty header has no byte 0.
  else .error .header

/-- Reject reserved bits, mask 0x0c long or 0x18 short, in an authenticated header (§§17.2, 17.3.1).

The header checks then reject a header that is not a protected version 1 packet. -/
def checkReservedBits (header : ByteArray) : Except Error Unit :=
  if h : 0 < header.size then
    let first := header[0]
    -- The Reserved Bits: mask 0x0c in a long header, 0x18 in a short one.
    let reserved := if first &&& 0x80 != 0 then 0x0c else 0x18
    -- Nonzero Reserved Bits are a PROTOCOL_VIOLATION connection error.
    --
    -- A Fixed Bit of 0 is not a version 1 packet, so the header checks reject it instead.
    ensure (first &&& 0x40 = 0 ∨ first &&& reserved = 0) .reservedBits
  -- An empty header has no reserved bits, and the header checks reject it.
  else .ok ()

/-- Initial packets always use AES-128-GCM, independently of TLS negotiation, RFC 9001 §5. -/
def checkSuite (suite : CipherSuite) : Packet.Header → Except Error Unit
  -- Initial packets use AEAD_AES_128_GCM.
  | .initial .. => ensure (suite = .aes128GcmSha256) .header
  -- Other packets use the AEAD that TLS negotiated.
  | _ => pure ()

/-- Check an authenticated header against the wire codec and isolated payload length.

A long header's Length counts the packet number and the protected payload, RFC 9000 §17.2.

Retry and Version Negotiation packets carry no protected payload and fail here. -/
def checkHeader (suite : CipherSuite) (header : ByteArray) (protectedLength : Nat) :
    Except Error Unit := do
  -- Fixed Bit 1 and Reserved Bits 0, RFC 9000 §§17.2 and 17.3.1.
  checkAuthenticatedHeader header
  if h : 0 < header.size then
    let width := Packet.widthOfFirst header[0]
    -- §5.4.2: `pn_offset = 1 + len(connection_id)` in a short header.
    --
    -- The header ends with the Packet Number field, so its size gives the connection ID length.
    let (decoded, trailing) ← (Packet.decode (header.size - (width.val + 1) - 1)
      header).mapError fun _ => .header
    -- The header is exactly the bytes up to and including the packet number, `A` of §5.3.
    ensure (trailing = ByteArray.empty) .header
    checkSuite suite decoded
    match decoded with
    -- Length: the remainder of the packet, the Packet Number and Payload fields.
    | .initial _ _ _ w length _ | .zeroRtt _ _ w length _ | .handshake _ _ w length _ =>
      ensure (length.val = w.val + 1 + protectedLength) .header
    -- A short header has no Length field.
    | .oneRtt .. => pure ()
    -- §5.4: Retry and Version Negotiation packets have no protected payload.
    | .retry .. | .versionNegotiation .. => throw .header
  else throw .header

/-- Protect a header and payload, RFC 9001 §§5.3 to 5.4.

The caller supplies `offset` and a header ending in the truncated packet number.

An insufficient ciphertext sample is an error, so callers add PADDING frames before sealing. -/
def protect (suite : CipherSuite) (keys : PacketKeys suite) (number : PacketNumber)
    (offset : Nat) (header plaintext : ByteArray) : Except Error ByteArray := do
  -- §5.3: the protected payload is 16 bytes longer than the plaintext.
  checkHeader suite header (plaintext.size + 16)
  if h : 0 < header.size then
    let first := header[0]
    -- `pn_length = (packet[0] & 0x03) + 1`, before byte 0 is masked.
    --
    -- The line reads the two-bit field, which is `pn_length - 1`.
    let width := Packet.widthOfFirst first
    -- The Packet Number field starts at the given offset and ends the header.
    ensure (0 < offset ∧ header.size = offset + width.val + 1) .header
    -- RFC 9000 §17.1: it holds the least significant bytes of the full packet number.
    ensure (bytesToNat (header.extract offset header.size).data.toList =
      number.val % 256 ^ (width.val + 1)) .packetNumber
    -- §5.3: the AEAD is applied prior to applying header protection.
    let (ciphertext, tag) ← encryptPayload suite keys number header plaintext
    -- The AEAD output `C`, the ciphertext then its 16-byte tag, is transmitted in place of `P`.
    let packet := header ++ ciphertext ++ tag
    -- §5.4.2: the sample of the ciphertext at `pn_offset + 4`.
    let sample ← sample packet offset
    -- §5.4.1: `mask = header_protection(hp_key, sample)`, applied to byte 0 and the number.
    return applyMask (first &&& 0x80 != 0) offset width (headerMask suite keys.hp sample) packet
  else throw .header

/-- Reconstruct a full packet number for the receiver's packet-number space, RFC 9000 Appendix A.3.

`expected` is one greater than the largest authenticated packet number, or zero initially. -/
def reconstructNumber (width : Packet.PacketNumberLength) (truncated expected : Nat) :
    Except Error PacketNumber := do
  -- RFC 9000 Appendix A.3, with `expected_pn = largest_pn + 1` given by the caller.
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
  -- §5.3: when processing packets, an endpoint first removes the header protection.
  let recovered ← removeHeaderProtection suite keys.hp offset packet
  -- RFC 9000 §17.1: the full packet number, before the payload can be opened.
  let number ← reconstructNumber recovered.width recovered.truncatedNumber expected
  -- §5.3: the AEAD opens the payload, with the recovered header as `A`.
  let plaintext ← decryptPayload suite keys number recovered.header
    recovered.ciphertext recovered.tag
  -- RFC 9000 §§17.2 and 17.3.1: the Reserved Bits after removing both protections.
  checkReservedBits recovered.header
  -- Only the reserved-bit check may report its own error after authentication.
  (checkHeader suite recovered.header (recovered.ciphertext.size + recovered.tag.size)).mapError
    fun _ => .header
  return (recovered.header, plaintext)

/-- The fixed QUIC v1 Retry key, RFC 9001 §5.8. -/
def RETRY_KEY : Vector UInt8 16 :=
  -- `K = 0xbe0c690b9f66575a1d766b54e368c84e`.
  #v[0xbe, 0x0c, 0x69, 0x0b, 0x9f, 0x66, 0x57, 0x5a,
    0x1d, 0x76, 0x6b, 0x54, 0xe3, 0x68, 0xc8, 0x4e]

/-- The fixed QUIC v1 Retry nonce, RFC 9001 §5.8. -/
def RETRY_NONCE : Vector UInt8 12 :=
  -- `N = 0x461599d35d632bf2239825bb`.
  #v[0x46, 0x15, 0x99, 0xd3, 0x5d, 0x63, 0x2b, 0xf2, 0x23, 0x98, 0x25, 0xbb]

/-- Authenticate the Retry pseudo-packet with empty plaintext, RFC 9001 §5.8.

`retry` is the Retry packet without its integrity tag.

The caller checks its header format. -/
def retryTag (originalDcid retry : ByteArray) : Except Error ByteArray := do
  -- ODCID Length (8) holds up to 255, but a version 1 connection ID has at most 20 bytes.
  --
  -- EthLib rejects a longer Original Destination Connection ID, RFC 9000 §17.2.
  ensure (originalDcid.size ≤ 20) (.connectionId originalDcid.size)
  -- `A` is the Retry Pseudo-Packet of Figure 8.
  --
  -- That is ODCID Length (8), then the Original Destination Connection ID.
  --
  -- Then the Retry packet without its Retry Integrity Tag.
  let aad := ByteArray.mk #[UInt8.ofNat originalDcid.size] ++ originalDcid ++ retry
  -- AEAD_AES_128_GCM with the fixed `K` and `N`, and an empty plaintext `P`.
  let (_, tag) ← (Aes.Gcm.encrypt (Aes.ciph .aes128 RETRY_KEY) 16
    (packBytes RETRY_NONCE) .empty aad).mapError .aes
  -- The 128-bit output is the Retry Integrity Tag.
  return tag

end EthLib.Networking.Quic.Protection
