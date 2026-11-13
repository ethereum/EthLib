module

public import EthLib.Base.Except
public import EthLib.Serialization.Der
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Cryptography.Secp256r1.Curve

/-!
# libp2p TLS certificates

The certificate fields follow [RFC 5280 §4.1][rfc5280].

Peer authentication follows libp2p TLS, [Peer Authentication][auth] and [Public Key Extension][ext].

Host keys may be secp256k1 or P-256; Ed25519 and RSA host keys are rejected as unsupported.

[rfc5280]: https://www.rfc-editor.org/rfc/rfc5280#section-4.1
[auth]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#peer-authentication
[ext]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#libp2p-public-key-extension
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Tls

/-- An object identifier in its DER content encoding. -/
abbrev Oid := ByteArray

/-- An X.509 extension: its object identifier, critical flag and octet-string content. -/
structure Extension where
  oid : Oid
  critical : Bool
  value : ByteArray

/-- Parsed certificate fields, preserving the signed bytes and the encoded public key. -/
structure Certificate where
  tbs : ByteArray
  spki : ByteArray
  issuer : ByteArray
  subject : ByteArray
  notBefore : Int
  notAfter : Int
  extensions : List Extension
  signatureAlgorithm : Oid
  signatureParameters : ByteArray
  signature : ByteArray
  issuerUniqueId : Bool
  subjectUniqueId : Bool

/-- The authenticated peer ID, with its certificate.

The certificate key later checks TLS CertificateVerify (RFC 8446 §4.4.3). -/
structure AuthenticatedPeer where
  peerId : ByteArray
  certificate : Certificate

open EthLib.Serialization
open EthLib.Base (ensure)

/-- Certificate parsing or a required libp2p authentication check failed. -/
inductive TlsCertError where
  | der (error : Der.Error)
  | certificate
  | validity
  | chain
  | missingExtension
  | duplicateExtension
  | criticalExtension
  | uniqueId
  | algorithm
  | publicKey
  | selfSignature
  | hostSignature
  | peerId
  deriving Repr, DecidableEq

/-- Stable error codes for the certificate boundary. -/
def TlsCertError.code : TlsCertError → UInt32
  | .der _ => 1
  | .certificate => 2
  | .validity => 3
  | .chain => 4
  | .missingExtension => 5
  | .duplicateExtension => 6
  | .criticalExtension => 7
  | .uniqueId => 8
  | .algorithm => 9
  | .publicKey => 10
  | .selfSignature => 11
  | .hostSignature => 12
  | .peerId => 13

/-- Lift a DER reader's error to the certificate boundary. -/
def der {α : Type} (value : Except Der.Error α) : Except TlsCertError α :=
  value.mapError .der

/-- Children of a value with the expected tag. -/
def fields (tag : UInt8) (value : Der.Value) : Except TlsCertError (List Der.Value) := do
  ensure (value.tag = tag) .certificate
  der (Der.children value.content)

/-- An AlgorithmIdentifier with at most one parameter (RFC 5280 §4.1.1.2). -/
def readAlgorithm (value : Der.Value) : Except TlsCertError (Oid × ByteArray) := do
  match ← fields 0x30 value with
  | [oid] => return (← der (Der.oid oid), .empty)
  | [oid, parameter] =>
    let _ ← der (Der.validate parameter)
    return (← der (Der.oid oid), parameter.encoded)
  | _ => throw .certificate

/-- Decimal ASCII digits, used by the certificate time formats. -/
def decimal (bytes : List UInt8) : Except TlsCertError Nat :=
  bytes.foldlM (fun n byte => do
    ensure (48 ≤ byte.toNat ∧ byte.toNat ≤ 57) .certificate
    return n * 10 + (byte.toNat - 48)) 0

/-- The Gregorian leap-year rule of certificate times (RFC 5280 §4.1.2.5). -/
def leapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- Gregorian month lengths, with February determined by the year. -/
def monthDays (year month : Nat) : Nat :=
  if month = 2 then if leapYear year then 29 else 28
  else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31

/-- Seconds from 1970-01-01T00:00:00Z, negative before it (RFC 5280 §§4.1.2.5.1, 4.1.2.5.2).

Issuers must write years before 2050 as UTCTime, but readers accept both forms. -/
def readTime (value : Der.Value) : Except TlsCertError Int := do
  let bytes := value.content.data.toList
  let yearLength ← if value.tag = 0x17 then pure 2
    else if value.tag = 0x18 then pure 4 else throw .certificate
  ensure (bytes.length = yearLength + 11 ∧ bytes.getLast? = some 90) .certificate
  let rawYear ← decimal (bytes.take yearLength)
  let year := if yearLength = 2 then
      if rawYear < 50 then 2000 + rawYear else 1900 + rawYear else rawYear
  ensure (0 < year) .certificate
  let rest := bytes.drop yearLength
  let month ← decimal (rest.take 2)
  let day ← decimal ((rest.drop 2).take 2)
  let hour ← decimal ((rest.drop 4).take 2)
  let minute ← decimal ((rest.drop 6).take 2)
  let second ← decimal ((rest.drop 8).take 2)
  ensure (1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ monthDays year month ∧
    hour < 24 ∧ minute < 60 ∧ second < 60) .certificate
  let y := year - 1
  let beforeYear := 365 * y + y / 4 - y / 100 + y / 400
  let beforeMonth := ((List.range (month - 1)).map (fun m => monthDays year (m + 1))).sum
  let days := (Int.ofNat (beforeYear + beforeMonth + day - 1)) - 719162
  return days * 86400 + Int.ofNat (hour * 3600 + minute * 60 + second)

/-- Read the two validity endpoints (RFC 5280 §4.1.2.5).

An inverted interval contains no time, so it is rejected as malformed. -/
def readValidity (value : Der.Value) : Except TlsCertError (Int × Int) := do
  match ← fields 0x30 value with
  | [first, last] =>
    let start ← readTime first
    let finish ← readTime last
    ensure (start ≤ finish) .certificate
    return (start, finish)
  | _ => throw .certificate

/-- Validate a Name: a sequence of nonempty attribute sets (RFC 5280 §4.1.2.4). -/
def readName (value : Der.Value) : Except TlsCertError Unit := do
  let rdns ← fields 0x30 value
  rdns.forM fun rdn => do
    let attributes ← fields 0x31 rdn
    ensure (attributes ≠ []) .certificate
    -- DER orders the encodings of a SET OF lexicographically (X.690 §11.6).
    ensure (attributes.map (·.encoded.data.toList) |>.Pairwise (· ≤ ·)) .certificate
    attributes.forM fun item => do
      match ← fields 0x30 item with
      | [oid, value] =>
        let _ ← der (Der.oid oid)
        let _ ← der (Der.validate value)
        pure ()
      | _ => throw .certificate

/-- Read an extension, rejecting an explicit default FALSE (RFC 5280 §4.1, X.690 §11.5). -/
def readExtension (value : Der.Value) : Except TlsCertError Extension := do
  match ← fields 0x30 value with
  | [oid, data] =>
    ensure (data.tag = 4) .certificate
    return ⟨← der (Der.oid oid), false, data.content⟩
  | [oid, critical, data] =>
    ensure (data.tag = 4) .certificate
    let flag ← der (Der.boolean critical)
    ensure (flag = true) .certificate
    return ⟨← der (Der.oid oid), flag, data.content⟩
  | _ => throw .certificate

/-- Read optional unique identifiers, then extensions, in their ASN.1 order. -/
def readTail (version : Nat) (tail : List Der.Value) :
    Except TlsCertError (Bool × Bool × List Extension) := do
  let (issuer, tail) ← match tail with
    | value :: rest =>
      if value.tag = 0x81 then
        ensure (1 ≤ version) .certificate
        let _ ← der (Der.validBits value.content)
        pure (true, rest)
      else pure (false, tail)
    | [] => pure (false, [])
  let (subject, tail) ← match tail with
    | value :: rest =>
      if value.tag = 0x82 then
        ensure (1 ≤ version) .certificate
        let _ ← der (Der.validBits value.content)
        pure (true, rest)
      else pure (false, tail)
    | [] => pure (false, [])
  let extensions ← match tail with
    | [] => pure []
    | [wrapper] =>
      ensure (version = 2 ∧ wrapper.tag = 0xa3) .certificate
      let sequence ← der (Der.exact 0x30 wrapper.content)
      let values ← fields 0x30 sequence
      ensure (values ≠ []) .certificate
      let extensions ← values.mapM readExtension
      ensure ((extensions.map (·.oid)).Nodup) .duplicateExtension
      pure extensions
    | _ => throw .certificate
  return (issuer, subject, extensions)

/-- Parse the exact signed and public-key encodings (RFC 5280 §4.1).

Only low-tag-number DER is read.

Any serial number is accepted, as RFC 5280 §4.1.2.2 asks of certificate users.

Certificate signature and key algorithms are checked separately by authentication. -/
def readCertificate (input : ByteArray) : Except TlsCertError Certificate := do
  let outer ← der (Der.exact 0x30 input)
  match ← fields 0x30 outer with
  | [tbs, algorithm, signature] =>
    let (signatureAlgorithm, signatureParameters) ← readAlgorithm algorithm
    let signature ← der (Der.bitString signature)
    let values ← fields 0x30 tbs
    let (version, values) ← match values with
      | first :: rest =>
        if first.tag = 0xa0 then
          let integer ← der (Der.exact 2 first.content)
          let version ← der (Der.natural integer)
          ensure (version = 1 ∨ version = 2) .certificate
          pure (version, rest)
        else pure (0, values)
      | [] => throw .certificate
    match values with
    | serial :: innerAlgorithm :: issuer :: validity :: subject :: spki :: tail =>
      let _ ← der (Der.integer serial)
      let _ ← readAlgorithm innerAlgorithm
      ensure (innerAlgorithm.encoded = algorithm.encoded) .algorithm
      readName issuer
      readName subject
      let (notBefore, notAfter) ← readValidity validity
      let spkiFields ← fields 0x30 spki
      match spkiFields with
      | [keyAlgorithm, key] =>
        let _ ← readAlgorithm keyAlgorithm
        let _ ← der (Der.bitString key)
      | _ => throw .certificate
      let (issuerUniqueId, subjectUniqueId, extensions) ← readTail version tail
      return {
        tbs := tbs.encoded, spki := spki.encoded,
        issuer := issuer.encoded, subject := subject.encoded,
        notBefore := notBefore, notAfter := notAfter,
        extensions := extensions, signatureAlgorithm := signatureAlgorithm,
        signatureParameters := signatureParameters, signature := signature,
        issuerUniqueId := issuerUniqueId, subjectUniqueId := subjectUniqueId }
    | _ => throw .certificate
  | _ => throw .certificate

/-- The libp2p public-key extension OID `1.3.6.1.4.1.53594.1.1`, as DER content. -/
def libp2pOid : Oid := ⟨#[0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xa2, 0x5a, 0x01, 0x01]⟩

/-- ecdsa-with-SHA256, `1.2.840.10045.4.3.2` (RFC 5758 §3.2). -/
def ecdsaSha256Oid : Oid := ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02]⟩

/-- id-ecPublicKey, `1.2.840.10045.2.1` (RFC 5480 §2.1.1). -/
def ecPublicKeyOid : Oid := ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]⟩

/-- prime256v1, the P-256 named curve `1.2.840.10045.3.1.7` (RFC 5480 §2.1.1.1). -/
def p256Oid : Oid := ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩

/-- Decode an uncompressed P-256 SubjectPublicKeyInfo (RFC 5480 §§2.1.1, 2.2). -/
def readP256 (spki : ByteArray) : Except TlsCertError EthLib.Cryptography.Secp256r1.Point := do
  let sequence ← der (Der.exact 0x30 spki)
  match ← fields 0x30 sequence with
  | [algorithm, key] =>
    let (oid, parameter) ← readAlgorithm algorithm
    let curve ← der (Der.exact 6 parameter)
    ensure (oid = ecPublicKeyOid ∧ (← der (Der.oid curve)) = p256Oid) .algorithm
    let bytes ← der (Der.bitString key)
    match bytes.data.toList with
    | 4 :: coords =>
      ensure (coords.length = 64) .publicKey
      let x := EthLib.Base.bytesToNat (coords.take 32)
      let y := EthLib.Base.bytesToNat (coords.drop 32)
      if hx : x < EthLib.Cryptography.Secp256r1.Fp.modulus then
        if hy : y < EthLib.Cryptography.Secp256r1.Fp.modulus then
          let point := EthLib.Cryptography.Secp256r1.Point.affine ⟨x, hx⟩ ⟨y, hy⟩
          ensure (point.isOnCurve = true) .publicKey
          return point
        else throw .publicKey
      else throw .publicKey
    | _ => throw .publicKey
  | _ => throw .publicKey

/-- Verify ECDSA/SHA-256 under an uncompressed P-256 SPKI, with strict DER scalars.

The signature is the DER sequence of RFC 3279 §2.2.3. -/
def verifyP256 (spki message signature : ByteArray) : Bool :=
  match readP256 spki, Libp2p.decodeScalars signature with
  | .ok point, some (r, s) =>
    EthLib.Cryptography.Secp256r1.verify point
      (EthLib.Base.bytesToNat (EthLib.Cryptography.Hash.Sha256.hash32 message).toList) r s
  | _, _ => false

/-- Concrete host-key backends, independently selected by the caller. -/
inductive HostAlgorithm where
  | secp256k1
  | p256
  deriving Repr, DecidableEq

/-- Concrete certificate-signature backends, independently selected by the caller. -/
inductive CertificateAlgorithm where
  | p256Sha256
  deriving Repr, DecidableEq

/-- The application chooses accepted algorithms and whether to reject deprecated unique IDs.

There is no default profile: libp2p TLS leaves these choices to the application. -/
structure Policy where
  hostAlgorithms : List HostAlgorithm
  certificateAlgorithms : List CertificateAlgorithm
  rejectUniqueIds : Bool

/-- Decode SignedKey's two octet strings, libp2p TLS "libp2p Public Key Extension". -/
def readSignedKey (bytes : ByteArray) : Except TlsCertError (ByteArray × ByteArray) := do
  let sequence ← der (Der.exact 0x30 bytes)
  match ← fields 0x30 sequence with
  | [key, signature] =>
    ensure (key.tag = 4 ∧ signature.tag = 4) .certificate
    return (key.content, signature.content)
  | _ => throw .certificate

/-- Find the libp2p extension after rejecting every other critical extension.

No other extension is understood here.

libp2p TLS "Peer Authentication" requires an abort on a critical extension not understood. -/
def signedKey (certificate : Certificate) : Except TlsCertError (ByteArray × ByteArray) := do
  ensure (certificate.extensions.all (fun ext => !ext.critical || ext.oid == libp2pOid))
    .criticalExtension
  match certificate.extensions.filter (fun ext => ext.oid == libp2pOid) with
  | [] => throw .missingExtension
  | [extension] => readSignedKey extension.value
  | _ => throw .duplicateExtension

/-- The message the host key signs: `libp2p-tls-handshake:`, then the certificate's SPKI. -/
def hostMessage (spki : ByteArray) : ByteArray := "libp2p-tls-handshake:".toUTF8 ++ spki

/-- Verify the host signature and derive the peer ID, libp2p peer IDs [Keys][keys].

The P-256 branch accepts a key of type 3 whose data is an uncompressed named-curve SPKI.

The key encoding must be canonical: minimal varints, fields in tag order, exactly two fields.

That key has 95 bytes, more than 42, so its peer ID is the SHA-256 multihash.

Ed25519, RSA and other ECDSA keys are rejected as unsupported algorithms.

[keys]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/peer-ids/peer-ids.md#keys
-/
def authenticateHost (policy : Policy) (spki key signature : ByteArray) :
    Except TlsCertError ByteArray := do
  match key.data.toList with
  | 8 :: 2 :: _ =>
    ensure (.secp256k1 ∈ policy.hostAlgorithms) .algorithm
    let point ← (Libp2p.decodePublicKey key).mapError (fun _ => .publicKey)
    ensure (Libp2p.verify key (hostMessage spki) signature = true) .hostSignature
    return Libp2p.peerId point
  | 8 :: 3 :: 18 :: 91 :: bytes =>
    ensure (.p256 ∈ policy.hostAlgorithms) .algorithm
    ensure (bytes.length = 91) .publicKey
    let hostSpki : ByteArray := ⟨bytes.toArray⟩
    let _ ← readP256 hostSpki
    ensure (verifyP256 hostSpki (hostMessage spki) signature = true) .hostSignature
    return ⟨#[0x12, 0x20]⟩ ++ EthLib.Cryptography.Hash.Sha256.hash key
  | 8 :: 0 :: _ | 8 :: 1 :: _ | 8 :: 3 :: _ => throw .algorithm
  | _ => throw .publicKey

/-- Check validity, unique identifiers, self-signature, extension and host signature.

The only implemented self-signature backend is P-256/SHA-256, with absent parameters.

The caller's policy must explicitly enable it. -/
def authenticateCertificate (policy : Policy) (now : Nat) (certificate : Certificate) :
    Except TlsCertError AuthenticatedPeer := do
  ensure (certificate.notBefore ≤ Int.ofNat now ∧ Int.ofNat now ≤ certificate.notAfter) .validity
  ensure (policy.rejectUniqueIds = false ∨
    (certificate.issuerUniqueId = false ∧ certificate.subjectUniqueId = false)) .uniqueId
  ensure (.p256Sha256 ∈ policy.certificateAlgorithms ∧
    certificate.signatureAlgorithm = ecdsaSha256Oid ∧
    certificate.signatureParameters.isEmpty = true)
    .algorithm
  ensure (verifyP256 certificate.spki certificate.tbs certificate.signature = true) .selfSignature
  let (key, signature) ← signedKey certificate
  let id ← authenticateHost policy certificate.spki key signature
  return ⟨id, certificate⟩

/-- Authenticate exactly one certificate, libp2p TLS "Peer Authentication". -/
def authenticate (policy : Policy) (now : Nat) (chain : List ByteArray) :
    Except TlsCertError AuthenticatedPeer := do
  match chain with
  | [bytes] => authenticateCertificate policy now (← readCertificate bytes)
  | _ => throw .chain

/-- A dialer also checks the intended peer ID, libp2p TLS "libp2p Public Key Extension". -/
def authenticatePeer (policy : Policy) (now : Nat) (expected : ByteArray)
    (chain : List ByteArray) : Except TlsCertError AuthenticatedPeer := do
  let peer ← authenticate policy now chain
  ensure (peer.peerId = expected) .peerId
  return peer

end EthLib.Networking.Libp2p.Tls
