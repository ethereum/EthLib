module

public import EthLib.Networking.Quic.Tls.Wire

/-!
# TLS 1.3 handshake message codecs

[RFC 8446 §4][handshake] frames each handshake message with a type and a three-byte body length.

The codecs cover the certificate-based handshake, including the ServerHello form of a retry.

They preserve extension order, opaque extension data and unrecognized algorithm identifiers.

They check field lengths, fixed legacy fields and duplicate extension types.

Extension placement and required extensions belong to the handshake steps.

So does agreement with earlier messages.

The codecs select no cipher suite, group, signature scheme or libp2p authentication policy.

QUIC carries these messages in CRYPTO data, without TLS record headers ([RFC 9001 §4][quic]).

CRYPTO reassembly and encryption-level checks belong to the transport.

[handshake]: https://www.rfc-editor.org/rfc/rfc8446#section-4
[quic]: https://www.rfc-editor.org/rfc/rfc9001#section-4
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire

/-- An extension's numeric type and exact data, RFC 8446 §4.2. -/
structure Extension where
  kind : CodePoint
  data : List UInt8
  deriving Repr, DecidableEq

/-- Read an extension without interpreting its payload (§4.2). -/
def readExtension : Reader Extension := do
  let kind ← codePoint
  return ⟨kind, ← blob 2 0 65535⟩

/-- Encode an extension without selecting an algorithm (§4.2). -/
def encodeExtension (extension : Extension) : Except Error (List UInt8) := do
  return Base.natToBytes 2 extension.kind.val ++ (← encodeBlob 2 0 65535 extension.data)

/-- No extension type occurs twice in one block, RFC 8446 §4.2. -/
def uniqueExtensions (extensions : List Extension) : Bool :=
  (extensions.map (·.kind)).eraseDups.length == extensions.length

/-- Read an extension block, preserving its order and rejecting duplicate types (§4.2). -/
def readExtensions (minimum : Nat) : Reader (List Extension) := do
  let extensions ← items 2 minimum 65535 readExtension
  require (uniqueExtensions extensions = true) .duplicateExtension
  return extensions

/-- Encode a block after checking its length and uniqueness (§4.2). -/
def encodeExtensions (minimum : Nat) (extensions : List Extension) :
    Except Error (List UInt8) := do
  Base.ensure (uniqueExtensions extensions = true) .duplicateExtension
  encodeItems 2 minimum 65535 encodeExtension extensions

/-- The ClientHello fields whose values are not fixed by RFC 8446 §4.1.2.

The legacy version is `0x0303` and the compression vector is `[1, 0]`.

The codec retains the session ID; QUIC callers enforce [RFC 9001 §8.4][compat].

[compat]: https://www.rfc-editor.org/rfc/rfc9001#section-8.4
-/
structure ClientHello where
  random : Vector UInt8 32
  legacySessionId : List UInt8
  cipherSuites : List CodePoint
  extensions : List Extension
  deriving Repr, DecidableEq

/-- The variable ServerHello fields, also used by HelloRetryRequest (§§4.1.3 and 4.1.4). -/
structure ServerHello where
  random : Vector UInt8 32
  legacySessionIdEcho : List UInt8
  cipherSuite : CodePoint
  extensions : List Extension
  deriving Repr, DecidableEq

/-- One certificate's exact bytes and extensions, without certificate validation (§4.4.2). -/
structure CertificateEntry where
  data : List UInt8
  extensions : List Extension
  deriving Repr, DecidableEq

/-- The certificate request context and chain, including the empty client chain (§4.4.2). -/
structure CertificateMessage where
  context : List UInt8
  entries : List CertificateEntry
  deriving Repr, DecidableEq

/-- The certificate request context and extensions, RFC 8446 §4.3.2. -/
structure CertificateRequest where
  context : List UInt8
  extensions : List Extension
  deriving Repr, DecidableEq

/-- The seven messages of a certificate-based handshake, RFC 8446 §§4.1, 4.3 and 4.4.

Finished has the hash length that the caller supplies to the codec.

The synthetic `message_hash` is a transcript construction, never a received message (§4.4.1). -/
inductive Message where
  | clientHello (fields : ClientHello)
  | serverHello (fields : ServerHello)
  | encryptedExtensions (extensions : List Extension)
  | certificateRequest (fields : CertificateRequest)
  | certificate (fields : CertificateMessage)
  | certificateVerify (algorithm : CodePoint) (signature : List UInt8)
  | finished (verifyData : List UInt8)
  deriving Repr, DecidableEq

/-- The HandshakeType tag of RFC 8446 §4. -/
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
  encodeItems width minimum maximum (fun n => .ok (Base.natToBytes 2 n.val)) values

/-- Read a certificate entry, keeping its DER bytes opaque (§4.4.2). -/
def readCertificateEntry : Reader CertificateEntry := do
  let data ← blob 3 1 (2 ^ 24 - 1)
  return ⟨data, ← readExtensions 0⟩

/-- Encode a certificate entry with a nonempty certificate (§4.4.2). -/
def encodeCertificateEntry (entry : CertificateEntry) : Except Error (List UInt8) := do
  let certificate ← encodeBlob 3 1 (2 ^ 24 - 1) entry.data
  return certificate ++ (← encodeExtensions 0 entry.extensions)

/-- Encode the body fields, checking each presentation-language bound. -/
def encodeBody (hashLength : Nat) : Message → Except Error (List UInt8)
  | .clientHello h => do
    let session ← encodeBlob 1 0 32 h.legacySessionId
    let suites ← encodeCodePoints 2 2 65534 h.cipherSuites
    let extensions ← encodeExtensions 8 h.extensions
    return [3, 3] ++ h.random.toList ++ session ++ suites ++ [1, 0] ++ extensions
  | .serverHello h => do
    let session ← encodeBlob 1 0 32 h.legacySessionIdEcho
    let extensions ← encodeExtensions 6 h.extensions
    return [3, 3] ++ h.random.toList ++ session ++
      Base.natToBytes 2 h.cipherSuite.val ++ [0] ++ extensions
  | .encryptedExtensions extensions => encodeExtensions 0 extensions
  | .certificateRequest request => do
    let context ← encodeBlob 1 0 255 request.context
    return context ++ (← encodeExtensions 2 request.extensions)
  | .certificate certificate => do
    let context ← encodeBlob 1 0 255 certificate.context
    return context ++ (← encodeItems 3 0 (2 ^ 24 - 1)
      encodeCertificateEntry certificate.entries)
  | .certificateVerify algorithm signature => do
    return Base.natToBytes 2 algorithm.val ++ (← encodeBlob 2 0 65535 signature)
  | .finished verifyData => do
    Base.ensure (verifyData.length = hashLength) .length
    return verifyData

/-- Read a body by its HandshakeType, RFC 8446 §4.

Legacy constants are checked for TLS 1.3; version negotiation is left to the handshake steps. -/
def readBody (hashLength : Nat) (kind : UInt8) : Reader Message := do
  match kind.toNat with
  | 1 =>
    require ((← uint 2) = 0x0303) .constant
    let random ← vector 32
    let session ← blob 1 0 32
    let suites ← items 2 2 65534 codePoint
    require ((← bytes 2) = [1, 0]) .constant
    return .clientHello ⟨random, session, suites, ← readExtensions 8⟩
  | 2 =>
    require ((← uint 2) = 0x0303) .constant
    let random ← vector 32
    let session ← blob 1 0 32
    let suite ← codePoint
    require ((← uint 1) = 0) .constant
    return .serverHello ⟨random, session, suite, ← readExtensions 6⟩
  | 8 => return .encryptedExtensions (← readExtensions 0)
  | 13 =>
    let context ← blob 1 0 255
    return .certificateRequest ⟨context, ← readExtensions 2⟩
  | 11 =>
    let context ← blob 1 0 255
    return .certificate ⟨context, ← items 3 0 (2 ^ 24 - 1) readCertificateEntry⟩
  | 15 =>
    let algorithm ← codePoint
    return .certificateVerify algorithm (← blob 2 0 65535)
  | 20 => return .finished (← bytes hashLength)
  | _ => throw .messageType

/-- Add the type and uint24 body length, RFC 8446 §4. -/
def frame (kind : UInt8) (body : List UInt8) : Except Error (List UInt8) := do
  return kind :: (← encodeBlob 3 0 (2 ^ 24 - 1) body)

/-- Read a handshake envelope, preserving arbitrary bytes after that message (§4). -/
def readFrame : Reader (UInt8 × List UInt8) := do
  let kind ← uint 1
  let body ← blob 3 0 (2 ^ 24 - 1)
  return (UInt8.ofNat kind, body)

/-- Encode one complete handshake message with the caller's negotiated hash length. -/
def encode (hashLength : Nat) (message : Message) : Except Error (List UInt8) := do
  frame message.type (← encodeBody hashLength message)

/-- Read one complete message from input with no TLS record header, RFC 9001 §4.

A truncated message reports a truncation error.

A stream caller can then keep it until more data arrives.

Unknown handshake types are rejected; unknown extension types and algorithm identifiers survive. -/
def decode (hashLength : Nat) : Reader Message := do
  let (kind, body) ← readFrame
  -- An incomplete field inside an already complete envelope cannot be repaired by more input.
  StateT.lift ((exact (readBody hashLength kind) body).mapError fun
    | .truncated => .length
    | error => error)

/-- The ServerHello random that identifies HelloRetryRequest, RFC 8446 §4.1.3. -/
def retryRandom : Vector UInt8 32 :=
  #v[0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11,
    0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e,
    0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c]

/-- Distinguish HelloRetryRequest before processing ServerHello extensions (§4.1.3). -/
def Message.isRetry : Message → Bool
  | .serverHello h => h.random == retryRandom
  | _ => false

end EthLib.Networking.Quic.Tls
