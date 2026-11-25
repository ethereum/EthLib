module

public import EthLib.Base.List
public import EthLib.Networking.Quic.Tls.Wire

/-!
# TLS 1.3 handshake message codecs

[RFC 9846 §4][handshake] frames each handshake message with a type and a three-byte body length.

The codecs cover the certificate-based handshake, including the ServerHello form of a retry.

They preserve extension order, opaque extension data and unrecognized algorithm identifiers.

They check field lengths, fixed legacy fields and duplicate extension types.

Extension placement and required extensions belong to the handshake steps.

So does agreement with earlier messages.

The codecs select no cipher suite, group, signature scheme or libp2p authentication policy.

QUIC carries these messages in CRYPTO data, without TLS record headers ([RFC 9001 §4][quic]).

CRYPTO reassembly and encryption-level checks belong to the transport.

[handshake]: https://www.rfc-editor.org/rfc/rfc9846#section-4
[quic]: https://www.rfc-editor.org/rfc/rfc9001#section-4
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire

/-- An extension's numeric type and exact data, RFC 9846 §4.3. -/
structure Extension where
  kind : CodePoint
  data : ByteArray
  deriving Repr, DecidableEq

/-- Read an extension without interpreting its payload (§4.3). -/
def readExtension : Reader Extension := do
  -- `ExtensionType extension_type;`, two bytes, kept even when unrecognized.
  let kind ← codePoint
  -- `opaque extension_data<0..2^16-1>;`, kept opaque.
  return ⟨kind, (← blob 2 0 65535).toByteArray⟩

/-- Encode an extension without selecting an algorithm (§4.3). -/
def encodeExtension (extension : Extension) : Except Error (List UInt8) := do
  -- `ExtensionType extension_type;` in two bytes, then `opaque extension_data<0..2^16-1>;`.
  return (Base.ByteOrder.toBE 2 extension.kind.val).toList
    ++ (← encodeBlob 2 0 65535 extension.data.data.toList)

/-- No extension type occurs twice in one block, RFC 9846 §4.3. -/
def uniqueExtensions (extensions : List Extension) : Bool :=
  -- There MUST NOT be more than one extension of the same type in a given extension block.
  --
  -- So no type of the block occurs again later in it.
  (Base.firstRepeated (extensions.map (·.kind))).isNone

/-- The first extension type that occurs again later in a block, or 0 when none does. -/
def repeatedKind (extensions : List Extension) : CodePoint :=
  (Base.firstRepeated (extensions.map (·.kind))).getD ⟨0, by decide⟩

/-- Read an extension block, preserving its order and rejecting duplicate types (§4.3). -/
def readExtensions (minimum : Nat) : Reader (List Extension) := do
  -- `Extension extensions<minimum..2^16-1>;`, with the floor of the enclosing message.
  let extensions ← items 2 minimum 65535 readExtension
  -- §4.3: no extension type twice in the block.
  --
  -- EthLib names the first repeated type in its own error, where §4.3 names no alert.
  require (uniqueExtensions extensions = true) (.duplicateExtension (repeatedKind extensions))
  return extensions

/-- Encode a block after checking its length and uniqueness (§4.3). -/
def encodeExtensions (minimum : Nat) (extensions : List Extension) :
    Except Error (List UInt8) := do
  -- §4.3: no extension type twice in the block, which a sender also meets.
  Base.ensure (uniqueExtensions extensions = true)
    (.duplicateExtension (repeatedKind extensions))
  -- `Extension extensions<minimum..2^16-1>;`, in the caller's order.
  encodeItems 2 minimum 65535 encodeExtension extensions

/-- The ClientHello fields whose values are not fixed by RFC 9846 §4.2.2.

The legacy version is `0x0303` and the compression vector is `[1, 0]`.

The codec retains the session ID; QUIC callers enforce [RFC 9001 §8.4][compat].

[compat]: https://www.rfc-editor.org/rfc/rfc9001#section-8.4
-/
structure ClientHello where
  random : Vector UInt8 32
  legacySessionId : ByteArray
  cipherSuites : List CodePoint
  extensions : List Extension
  deriving Repr, DecidableEq

/-- The variable ServerHello fields, also used by HelloRetryRequest (§§4.2.3 and 4.2.4). -/
structure ServerHello where
  random : Vector UInt8 32
  legacySessionIdEcho : ByteArray
  cipherSuite : CodePoint
  extensions : List Extension
  deriving Repr, DecidableEq

/-- One certificate's exact bytes and extensions, without certificate validation (§4.5.1). -/
structure CertificateEntry where
  data : ByteArray
  extensions : List Extension
  deriving Repr, DecidableEq

/-- The certificate request context and chain, including the empty client chain (§4.5.1). -/
structure CertificateMessage where
  context : ByteArray
  entries : List CertificateEntry
  deriving Repr, DecidableEq

/-- The certificate request context and extensions, RFC 9846 §4.4.2. -/
structure CertificateRequest where
  context : ByteArray
  extensions : List Extension
  deriving Repr, DecidableEq

/-- The seven messages of a certificate-based handshake, RFC 9846 §§4.2, 4.4 and 4.5.

Finished has the hash length that the caller supplies to the codec.

The synthetic `message_hash` is a transcript construction, never a received message (§4.1). -/
inductive Message where
  | clientHello (fields : ClientHello)
  | serverHello (fields : ServerHello)
  | encryptedExtensions (extensions : List Extension)
  | certificateRequest (fields : CertificateRequest)
  | certificate (fields : CertificateMessage)
  | certificateVerify (algorithm : CodePoint) (signature : ByteArray)
  | finished (verifyData : ByteArray)
  deriving Repr, DecidableEq

/-- The HandshakeType tag of RFC 9846 §4. -/
def Message.type : Message → UInt8
  | .clientHello _ => 1
  | .serverHello _ => 2
  | .encryptedExtensions _ => 8
  | .certificateRequest _ => 13
  | .certificate _ => 11
  | .certificateVerify .. => 15
  | .finished _ => 20

/-- Encode a list of two-byte identifiers without narrowing their values. -/
def encodeCodePoints (width minimum maximum : Nat) (values : List CodePoint) :
    Except Error (List UInt8) :=
  encodeItems width minimum maximum (fun n => .ok ((Base.ByteOrder.toBE 2 n.val).toList)) values

/-- Read a certificate entry, keeping its DER bytes opaque (§4.5.1). -/
def readCertificateEntry : Reader CertificateEntry := do
  -- The X509 case: `opaque cert_data<1..2^24-1>;`.
  let data ← blob 3 1 (2 ^ 24 - 1)
  -- `Extension extensions<0..2^16-1>;`.
  return ⟨data.toByteArray, ← readExtensions 0⟩

/-- Encode a certificate entry with a nonempty certificate (§4.5.1). -/
def encodeCertificateEntry (entry : CertificateEntry) : Except Error (List UInt8) := do
  -- The X509 case: `opaque cert_data<1..2^24-1>;`.
  let certificate ← encodeBlob 3 1 (2 ^ 24 - 1) entry.data.data.toList
  -- `Extension extensions<0..2^16-1>;`.
  return certificate ++ (← encodeExtensions 0 entry.extensions)

/-- Encode the body fields, checking each presentation-language bound. -/
def encodeBody (hashLength : Nat) : Message → Except Error (List UInt8)
  -- §4.2.2, ClientHello.
  | .clientHello h => do
    -- `opaque legacy_session_id<0..32>;`.
    let session ← encodeBlob 1 0 32 h.legacySessionId.data.toList
    -- `CipherSuite cipher_suites<2..2^16-2>;`.
    let suites ← encodeCodePoints 2 2 65534 h.cipherSuites
    -- RFC 9846 §4.2.2: `Extension extensions<7..2^16-1>;`.
    --
    -- RFC 8446 printed a floor of 8, which its verified erratum 8423 corrects to 7.
    let extensions ← encodeExtensions 7 h.extensions
    -- `ProtocolVersion legacy_version = 0x0303;`, `Random random;`, then the vectors above.
    --
    -- The compression methods are one byte, set to zero, after their one-byte length.
    return [3, 3] ++ h.random.toList ++ session ++ suites ++ [1, 0] ++ extensions
  -- §4.2.3, ServerHello, also the form of a HelloRetryRequest.
  | .serverHello h => do
    -- `opaque legacy_session_id_echo<0..32>;`.
    let session ← encodeBlob 1 0 32 h.legacySessionIdEcho.data.toList
    -- `Extension extensions<6..2^16-1>;`.
    let extensions ← encodeExtensions 6 h.extensions
    -- `ProtocolVersion legacy_version = 0x0303;`, `Random random;`, then the session ID echo.
    return [3, 3] ++ h.random.toList ++ session ++
      -- `CipherSuite cipher_suite;`, `uint8 legacy_compression_method = 0;`, the extensions.
      (Base.ByteOrder.toBE 2 h.cipherSuite.val).toList ++ [0] ++ extensions
  -- §4.4.1: `Extension extensions<0..2^16-1>;`.
  | .encryptedExtensions extensions => encodeExtensions 0 extensions
  -- §4.4.2, CertificateRequest.
  | .certificateRequest request => do
    -- `opaque certificate_request_context<0..2^8-1>;`.
    let context ← encodeBlob 1 0 255 request.context.data.toList
    -- RFC 9846 §4.4.2: `Extension extensions<0..2^16-1>;`.
    --
    -- RFC 8446 printed a floor of 2, which RFC 9846 §1.2 corrects to 0.
    return context ++ (← encodeExtensions 0 request.extensions)
  -- §4.5.1, Certificate.
  | .certificate certificate => do
    -- `opaque certificate_request_context<0..2^8-1>;`.
    let context ← encodeBlob 1 0 255 certificate.context.data.toList
    -- `CertificateEntry certificate_list<0..2^24-1>;`.
    return context ++ (← encodeItems 3 0 (2 ^ 24 - 1)
      encodeCertificateEntry certificate.entries)
  -- §4.5.2: `SignatureScheme algorithm;`, then `opaque signature<0..2^16-1>;`.
  | .certificateVerify algorithm signature => do
    return (Base.ByteOrder.toBE 2 algorithm.val).toList
      ++ (← encodeBlob 2 0 65535 signature.data.toList)
  -- §4.5.3: `opaque verify_data[Hash.length];`, with no length prefix.
  | .finished verifyData => do
    Base.ensure (verifyData.size = hashLength) .length
    return verifyData.data.toList

/-- Read a body by its HandshakeType, RFC 9846 §4.

Legacy constants are checked for TLS 1.3; the supported versions extension is left to the steps. -/
def readBody (hashLength : Nat) (kind : UInt8) : Reader Message := do
  match kind.toNat with
  -- The client hello, type 1, §4.2.2.
  | 1 =>
    -- `ProtocolVersion legacy_version = 0x0303;`.
    --
    -- RFC 9846 §4.2.2: a server that receives another value answers with protocol_version.
    require ((← uint 2) = 0x0303) .legacyVersion
    -- `Random random;`, 32 bytes.
    let random ← vector 32
    -- `opaque legacy_session_id<0..32>;`, kept for the check of RFC 9001 §8.4 by the caller.
    let session ← blob 1 0 32
    -- `CipherSuite cipher_suites<2..2^16-2>;`, unrecognized suites kept.
    let suites ← items 2 2 65534 codePoint
    -- `opaque legacy_compression_methods<1..2^8-1>;`.
    --
    -- §4.2.2: in TLS 1.3 this vector MUST contain exactly one byte, set to zero.
    require ((← bytes 2) = [1, 0]) .constant
    -- RFC 9846 §4.2.2: `Extension extensions<7..2^16-1>;`.
    --
    -- The smallest block is one supported versions extension that lists one version.
    --
    -- That is 4 header bytes, 1 length byte and 2 version bytes.
    return .clientHello ⟨random, session.toByteArray, suites, ← readExtensions 7⟩
  -- The server hello, type 2, §4.2.3, whose structure a HelloRetryRequest shares.
  | 2 =>
    -- `ProtocolVersion legacy_version = 0x0303;`.
    --
    -- RFC 9846 §§4.2.3 and 4.2.4: a client that receives another value sends protocol_version.
    require ((← uint 2) = 0x0303) .legacyVersion
    -- `Random random;`, 32 bytes.
    let random ← vector 32
    -- `opaque legacy_session_id_echo<0..32>;`.
    let session ← blob 1 0 32
    -- `CipherSuite cipher_suite;`.
    let suite ← codePoint
    -- `uint8 legacy_compression_method = 0;`.
    require ((← uint 1) = 0) .constant
    -- `Extension extensions<6..2^16-1>;`.
    return .serverHello ⟨random, session.toByteArray, suite, ← readExtensions 6⟩
  -- Encrypted extensions, type 8, §4.4.1: `Extension extensions<0..2^16-1>;`.
  | 8 => return .encryptedExtensions (← readExtensions 0)
  -- The certificate request, type 13, §4.4.2.
  | 13 =>
    -- `opaque certificate_request_context<0..2^8-1>;`.
    let context ← blob 1 0 255
    -- RFC 9846 §4.4.2: `Extension extensions<0..2^16-1>;`, so the block may be empty.
    --
    -- The handshake steps require the signature algorithms extension in it.
    return .certificateRequest ⟨context.toByteArray, ← readExtensions 0⟩
  -- The certificate, type 11, §4.5.1.
  | 11 =>
    -- `opaque certificate_request_context<0..2^8-1>;`.
    let context ← blob 1 0 255
    -- `CertificateEntry certificate_list<0..2^24-1>;`, each entry in the X509 form.
    return .certificate ⟨context.toByteArray, ← items 3 0 (2 ^ 24 - 1) readCertificateEntry⟩
  -- The certificate verify, type 15, §4.5.2.
  | 15 =>
    -- `SignatureScheme algorithm;`, unrecognized schemes kept.
    let algorithm ← codePoint
    -- `opaque signature<0..2^16-1>;`.
    return .certificateVerify algorithm (← blob 2 0 65535).toByteArray
  -- The finished message, type 20, §4.5.3: `opaque verify_data[Hash.length];`.
  | 20 => return .finished (← bytes hashLength).toByteArray
  -- Any other type is not one of the seven messages of the certificate handshake.
  --
  -- Among them are the new session ticket (4), end of early data (5) and key update (24).
  | _ => throw (.messageType kind)

/-- Add the type and uint24 body length, RFC 9846 §4. -/
def frameList (kind : UInt8) (body : List UInt8) : Except Error (List UInt8) := do
  -- `HandshakeType msg_type;`, then `uint24 length;`, the remaining bytes in the message.
  return kind :: (← encodeBlob 3 0 (2 ^ 24 - 1) body)

/-- Read a handshake envelope, preserving arbitrary bytes after that message (§4). -/
def readFrame : Reader (UInt8 × List UInt8) := do
  -- `HandshakeType msg_type;`, one byte.
  let kind ← uint 1
  -- `uint24 length;`, then that many bytes of the message.
  let body ← blob 3 0 (2 ^ 24 - 1)
  return (UInt8.ofNat kind, body)

/-- Encode one complete handshake message with the caller's negotiated hash length. -/
def encodeList (hashLength : Nat) (message : Message) : Except Error (List UInt8) := do
  -- §4: the type of the message, its length, then its body.
  frameList message.type (← encodeBody hashLength message)

/-- Read one complete message from input with no TLS record header, RFC 9001 §4.

A truncated message reports a truncation error.

A stream caller can then keep it until more data arrives.

Handshake types other than these seven are rejected.

Unknown extension types and algorithm identifiers survive. -/
def decodeList (hashLength : Nat) : Reader Message := do
  -- RFC 9001 §4: CRYPTO data carries the handshake messages, with no record layer.
  let (kind, body) ← readFrame
  -- RFC 9846 §4: the body is the structure that the type selects, and it fills the length exactly.
  --
  -- An incomplete field inside an already complete envelope cannot be repaired by more input.
  StateT.lift ((exact (readBody hashLength kind) body).mapError fun
    | .truncated .. => .length
    | error => error)

/-- The ServerHello random that identifies HelloRetryRequest, RFC 9846 §4.2.3. -/
def retryRandom : Vector UInt8 32 :=
  -- The special value of §4.2.3: the SHA-256 of the string HelloRetryRequest.
  #v[0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11,
    0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e,
    0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c]

/-- Distinguish HelloRetryRequest before processing ServerHello extensions (§4.2.3). -/
def Message.isRetry : Message → Bool
  -- §4.2.3: a server hello whose Random matches this value is processed as a HelloRetryRequest.
  | .serverHello h => h.random == retryRandom
  -- Only a server hello can be a HelloRetryRequest.
  | _ => false

/-- Encode one complete handshake message as packed bytes. -/
def encode (hashLength : Nat) (message : Message) : Except Error ByteArray :=
  (encodeList hashLength message).map List.toByteArray

/-- Decode one complete handshake message and return its packed trailing bytes. -/
def decode (hashLength : Nat) (input : ByteArray) : Except Error (Message × ByteArray) :=
  (decodeList hashLength input.data.toList).map fun (message, rest) => (message, rest.toByteArray)

/-- Add the handshake header to a packed body. -/
def frame (kind : UInt8) (body : ByteArray) : Except Error ByteArray :=
  (frameList kind body.data.toList).map List.toByteArray

end EthLib.Networking.Quic.Tls
