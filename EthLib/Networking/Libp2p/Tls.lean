module

public import EthLib.Base.Except
public import EthLib.Serialization.Der
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Cryptography.Secp256r1.Encoding

/-!
# libp2p TLS certificates

The certificate fields follow [RFC 5280 §4.1][rfc5280].

Peer authentication follows libp2p TLS, [Peer Authentication][auth] and [Public Key Extension][ext].

Host keys may be secp256k1 or P-256; Ed25519 and RSA host keys are rejected as unsupported.

[rfc5280]: https://www.rfc-editor.org/rfc/rfc5280#section-4.1
[auth]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/tls/tls.md#peer-authentication
[ext]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/tls/tls.md#libp2p-public-key-extension
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

The certificate key later checks TLS CertificateVerify (RFC 9846 §4.5.2). -/
structure AuthenticatedPeer where
  peerId : ByteArray
  certificate : Certificate

open EthLib.Serialization
open EthLib.Base (ensure)

/-- Certificate parsing or a required libp2p authentication check failed. -/
inductive TlsCertError where
  /-- The DER reader rejected the bytes. -/
  | der (error : Der.Error)
  /-- A DER value does not have the shape that X.509 gives its place (RFC 5280 §4.1). -/
  | certificate
  /-- The time `now` is outside the validity period from `notBefore` to `notAfter`. -/
  | validity (now : Nat) (notBefore notAfter : Int)
  /-- The chain holds `count` certificates, not exactly one. -/
  | chain (count : Nat)
  /-- The certificate has no libp2p extension. -/
  | missingExtension
  /-- The extension with the OID bytes `oid` occurs more than once. -/
  | duplicateExtension (oid : List UInt8)
  /-- The extension with the OID bytes `oid` is critical, and only the libp2p one is understood. -/
  | criticalExtension (oid : List UInt8)
  /-- A unique identifier is present, and the policy rejects it. -/
  | uniqueId
  /-- An algorithm is unsupported, disabled by the policy, or inconsistent in the certificate. -/
  | algorithm
  /-- A public key is not a valid key of its type. -/
  | publicKey
  /-- The self-signature of the certificate does not verify. -/
  | selfSignature
  /-- The host signature of the libp2p extension does not verify. -/
  | hostSignature
  /-- The certificate authenticates another peer than the expected one. -/
  | peerId
  deriving Repr, DecidableEq

/-- Stable error codes for the certificate boundary. -/
def TlsCertError.code : TlsCertError → UInt32
  | .der _ => 1
  | .certificate => 2
  | .validity .. => 3
  | .chain _ => 4
  | .missingExtension => 5
  | .duplicateExtension _ => 6
  | .criticalExtension _ => 7
  | .uniqueId => 8
  | .algorithm => 9
  | .publicKey => 10
  | .selfSignature => 11
  | .hostSignature => 12
  | .peerId => 13

/-- The first value of a list that occurs again later in it, if any. -/
def firstRepeated : List (List UInt8) → Option (List UInt8)
  | [] => none
  | oid :: rest => if oid ∈ rest then some oid else firstRepeated rest

/-- Lift a DER reader's error to the certificate boundary. -/
def der {α : Type} (value : Except Der.Error α) : Except TlsCertError α :=
  value.mapError .der

/-- Children of a value with the expected tag. -/
def fields (tag : UInt8) (value : Der.Value) : Except TlsCertError (List Der.Value) := do
  -- X.690 §8.1.2: the identifier octet encodes the tag that the place in the structure gives.
  ensure (value.tag = tag) .certificate
  -- X.690 §§8.9.2, 8.10.2 and 8.12.2: the contents are complete encodings of the components.
  der (Der.children value.content)

/-- An AlgorithmIdentifier with at most one parameter (RFC 5280 §4.1.1.2). -/
def readAlgorithm (value : Der.Value) : Except TlsCertError (Oid × ByteArray) := do
  -- `AlgorithmIdentifier ::= SEQUENCE { algorithm OBJECT IDENTIFIER, parameters ANY ... }`.
  match ← fields 0x30 value with
  -- The parameters are OPTIONAL: absent, they are returned empty.
  | [oid] => return (← der (Der.oid oid), .empty)
  -- Present, they are one DER value, kept in its encoding for the algorithm to read.
  | [oid, parameter] =>
    let _ ← der (Der.validate parameter)
    return (← der (Der.oid oid), parameter.encoded)
  | _ => throw .certificate

/-- Decimal ASCII digits, used by the certificate time formats. -/
def decimal (bytes : List UInt8) : Except TlsCertError Nat :=
  bytes.foldlM (fun n byte => do
    -- X.680 §§46.3 and 47.3: each character is one of the digits 0 to 9, 0x30 to 0x39.
    ensure (48 ≤ byte.toNat ∧ byte.toNat ≤ 57) .certificate
    -- The digits read most significant first.
    return n * 10 + (byte.toNat - 48)) 0

/-- The Gregorian leap-year rule of certificate times (RFC 5280 §4.1.2.5). -/
def leapYear (year : Nat) : Bool :=
  -- A year divisible by 4 is a leap year, unless divisible by 100 and not by 400.
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- Gregorian month lengths, with February determined by the year. -/
def monthDays (year month : Nat) : Nat :=
  -- February has 29 days in a leap year and 28 otherwise.
  --
  -- April, June, September and November have 30 days, and the other months 31.
  if month = 2 then if leapYear year then 29 else 28
  else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31

/-- Seconds from 1970-01-01T00:00:00Z, negative before it (RFC 5280 §§4.1.2.5.1, 4.1.2.5.2). -/
def readTime (value : Der.Value) : Except TlsCertError Int := do
  let bytes := value.content.data.toList
  -- `Time ::= CHOICE { utcTime UTCTime, generalTime GeneralizedTime }`, tags 23 and 24.
  --
  -- §4.1.2.5: issuers write years through 2049 as UTCTime, but readers accept both forms.
  let yearLength ← if value.tag = 0x17 then pure 2
    else if value.tag = 0x18 then pure 4 else throw .certificate
  -- §4.1.2.5.1: YYMMDDHHMMSSZ, and §4.1.2.5.2: YYYYMMDDHHMMSSZ, with no fractional seconds.
  --
  -- So the seconds are present (X.690 §§11.7.2, 11.8.2) and the time ends with Z, 0x5A.
  ensure (bytes.length = yearLength + 11 ∧ bytes.getLast? = some 90) .certificate
  let rawYear ← decimal (bytes.take yearLength)
  -- §4.1.2.5.1: YY of 50 or more is 19YY, and YY below 50 is 20YY.
  let year := if yearLength = 2 then
      if rawYear < 50 then 2000 + rawYear else 1900 + rawYear else rawYear
  -- Not in RFC 5280: the year 0000 fails, since the day count below starts at year 1.
  ensure (0 < year) .certificate
  let rest := bytes.drop yearLength
  -- MM, DD, HH, MM and SS, two digits each.
  let month ← decimal (rest.take 2)
  let day ← decimal ((rest.drop 2).take 2)
  let hour ← decimal ((rest.drop 4).take 2)
  let minute ← decimal ((rest.drop 6).take 2)
  let second ← decimal ((rest.drop 8).take 2)
  -- X.680 §47.3, for UTCTime: months 01 to 12, a day of that month, hours 00 to 23.
  --
  -- Minutes and seconds 00 to 59: EthLib applies these UTCTime ranges to GeneralizedTime too.
  ensure (1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ monthDays year month ∧
    hour < 24 ∧ minute < 60 ∧ second < 60) .certificate
  -- The days of the Gregorian years 1 to `year - 1`.
  let y := year - 1
  let beforeYear := 365 * y + y / 4 - y / 100 + y / 400
  -- The days of the months before `month` in `year`.
  let beforeMonth := ((List.range (month - 1)).map (fun m => monthDays year (m + 1))).sum
  -- 719162 days separate 0001-01-01 from 1970-01-01.
  let days := (Int.ofNat (beforeYear + beforeMonth + day - 1)) - 719162
  -- 86400 seconds a day, with no leap seconds.
  return days * 86400 + Int.ofNat (hour * 3600 + minute * 60 + second)

/-- Read the two validity endpoints (RFC 5280 §4.1.2.5). -/
def readValidity (value : Der.Value) : Except TlsCertError (Int × Int) := do
  -- `Validity ::= SEQUENCE { notBefore Time, notAfter Time }`.
  match ← fields 0x30 value with
  | [first, last] =>
    let start ← readTime first
    let finish ← readTime last
    -- Not in RFC 5280: an inverted interval contains no time, so it fails as malformed.
    ensure (start ≤ finish) .certificate
    return (start, finish)
  | _ => throw .certificate

/-- Validate a Name: a sequence of nonempty attribute sets (RFC 5280 §4.1.2.4). -/
def readName (value : Der.Value) : Except TlsCertError Unit := do
  -- `RDNSequence ::= SEQUENCE OF RelativeDistinguishedName`.
  --
  -- Not checked: the non-empty issuer name that §4.1.2.4 requires, since this reads subjects too.
  let rdns ← fields 0x30 value
  rdns.forM fun rdn => do
    -- `RelativeDistinguishedName ::= SET SIZE (1..MAX) OF AttributeTypeAndValue`.
    let attributes ← fields 0x31 rdn
    ensure (attributes ≠ []) .certificate
    -- X.690 §11.6: the encodings of a set-of value appear in ascending order.
    --
    -- §11.6 pads the shorter encoding with zeros to compare.
    --
    -- A DER encoding is never a proper prefix of another, so the order is lexicographic.
    ensure (attributes.map (·.encoded.data.toList) |>.Pairwise (· ≤ ·)) .certificate
    attributes.forM fun item => do
      -- `AttributeTypeAndValue ::= SEQUENCE { type AttributeType, value AttributeValue }`.
      --
      -- The type is an OBJECT IDENTIFIER, and the value any valid DER value.
      match ← fields 0x30 item with
      | [oid, value] =>
        let _ ← der (Der.oid oid)
        let _ ← der (Der.validate value)
        pure ()
      | _ => throw .certificate

/-- Read an extension, rejecting an explicit default FALSE (RFC 5280 §4.1, X.690 §11.5). -/
def readExtension (value : Der.Value) : Except TlsCertError Extension := do
  -- `Extension ::= SEQUENCE { extnID OBJECT IDENTIFIER, critical BOOLEAN DEFAULT FALSE, ... }`.
  match ← fields 0x30 value with
  -- The critical flag is absent, so it takes its default FALSE.
  | [oid, data] =>
    -- `extnValue OCTET STRING`, tag 4.
    ensure (data.tag = 4) .certificate
    return ⟨← der (Der.oid oid), false, data.content⟩
  | [oid, critical, data] =>
    ensure (data.tag = 4) .certificate
    let flag ← der (Der.boolean critical)
    -- X.690 §11.5: DER never encodes a component equal to its default, so it is TRUE.
    ensure (flag = true) .certificate
    return ⟨← der (Der.oid oid), flag, data.content⟩
  | _ => throw .certificate

/-- Read optional unique identifiers, then extensions, in their ASN.1 order. -/
def readTail (version : Nat) (tail : List Der.Value) :
    Except TlsCertError (Bool × Bool × List Extension) := do
  -- `issuerUniqueID [1] IMPLICIT UniqueIdentifier OPTIONAL`, a BIT STRING with tag 0x81.
  let (issuer, tail) ← match tail with
    | value :: rest =>
      if value.tag = 0x81 then
        -- §4.1.2.8: if present, the version MUST be v2 or v3.
        ensure (1 ≤ version) .certificate
        let _ ← der (Der.validBits value.content)
        pure (true, rest)
      else pure (false, tail)
    | [] => pure (false, [])
  -- `subjectUniqueID [2] IMPLICIT UniqueIdentifier OPTIONAL`, a BIT STRING with tag 0x82.
  let (subject, tail) ← match tail with
    | value :: rest =>
      if value.tag = 0x82 then
        -- §4.1.2.8: if present, the version MUST be v2 or v3.
        ensure (1 ≤ version) .certificate
        let _ ← der (Der.validBits value.content)
        pure (true, rest)
      else pure (false, tail)
    | [] => pure (false, [])
  -- `extensions [3] EXPLICIT Extensions OPTIONAL`, the last field.
  let extensions ← match tail with
    | [] => pure []
    | [wrapper] =>
      -- §4.1.2.9: if present, the version MUST be v3, whose value is 2.
      ensure (version = 2 ∧ wrapper.tag = 0xa3) .certificate
      -- X.690 §8.14.3: the explicit tag holds the complete encoding of one SEQUENCE.
      let sequence ← der (Der.exact 0x30 wrapper.content)
      -- `Extensions ::= SEQUENCE SIZE (1..MAX) OF Extension`.
      let values ← fields 0x30 sequence
      ensure (values ≠ []) .certificate
      let extensions ← values.mapM readExtension
      -- §4.2: a certificate MUST NOT include more than one instance of a particular extension.
      --
      -- When the check fails, some OID repeats, so the error names a real OID.
      ensure ((extensions.map (·.oid)).Nodup)
        (.duplicateExtension ((firstRepeated (extensions.map (·.oid.data.toList))).getD []))
      pure extensions
    -- Any other value after the public key does not belong to a TBSCertificate.
    | _ => throw .certificate
  return (issuer, subject, extensions)

/-- Parse the exact signed and public-key encodings (RFC 5280 §4.1).

Only low-tag-number DER is read.

Certificate signature and key algorithms are checked separately by authentication. -/
def readCertificate (input : ByteArray) : Except TlsCertError Certificate := do
  -- One DER value, with no byte after it.
  let outer ← der (Der.exact 0x30 input)
  -- `Certificate ::= SEQUENCE { tbsCertificate, signatureAlgorithm, signatureValue }`.
  match ← fields 0x30 outer with
  | [tbs, algorithm, signature] =>
    -- §4.1.1.2: `signatureAlgorithm AlgorithmIdentifier`.
    let (signatureAlgorithm, signatureParameters) ← readAlgorithm algorithm
    -- §4.1.1.3: `signatureValue BIT STRING`.
    let signature ← der (Der.bitString signature)
    -- `TBSCertificate ::= SEQUENCE { ... }`, its fields in order.
    let values ← fields 0x30 tbs
    -- `version [0] EXPLICIT Version DEFAULT v1`.
    --
    -- `Version ::= INTEGER { v1(0), v2(1), v3(2) }`.
    let (version, values) ← match values with
      | first :: rest =>
        if first.tag = 0xa0 then
          let integer ← der (Der.exact 2 first.content)
          let version ← der (Der.natural integer)
          -- X.690 §11.5: DER omits the default v1, so a present version is v2 or v3.
          ensure (version = 1 ∨ version = 2) .certificate
          pure (version, rest)
        -- Absent, the version is its default v1, whose value is 0.
        else pure (0, values)
      | [] => throw .certificate
    -- `serialNumber`, `signature`, `issuer`, `validity`, `subject`, `subjectPublicKeyInfo`.
    match values with
    | serial :: innerAlgorithm :: issuer :: validity :: subject :: spki :: tail =>
      -- §4.1.2.2: users SHOULD handle negative or zero serial numbers, so any INTEGER is read.
      let _ ← der (Der.integer serial)
      let _ ← readAlgorithm innerAlgorithm
      -- §4.1.2.3: the same algorithm identifier as the signatureAlgorithm field.
      --
      -- EthLib compares their DER encodings, parameters included.
      ensure (innerAlgorithm.encoded = algorithm.encoded) .algorithm
      -- §4.1.2.4 and §4.1.2.6: the issuer and the subject are each a Name.
      readName issuer
      readName subject
      -- §4.1.2.5: the validity.
      let (notBefore, notAfter) ← readValidity validity
      -- §4.1: `SubjectPublicKeyInfo ::= SEQUENCE { algorithm AlgorithmIdentifier, ... }`.
      let spkiFields ← fields 0x30 spki
      match spkiFields with
      | [keyAlgorithm, key] =>
        let _ ← readAlgorithm keyAlgorithm
        let _ ← der (Der.bitString key)
      | _ => throw .certificate
      -- Then the optional unique identifiers and extensions.
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
def libp2pOid : Oid :=
  -- X.690 §8.19: 40 * 1 + 3 = 0x2b, then 6, 1, 4, 1, 53594 in base 128 as 83 a2 5a, 1 and 1.
  ⟨#[0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xa2, 0x5a, 0x01, 0x01]⟩

/-- ecdsa-with-SHA256, `1.2.840.10045.4.3.2` (RFC 5758 §3.2). -/
def ecdsaSha256Oid : Oid :=
  -- X.690 §8.19: 0x2a for 1.2, 840 as 86 48, 10045 as ce 3d, then 4, 3 and 2.
  ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02]⟩

/-- id-ecPublicKey, `1.2.840.10045.2.1` (RFC 5480 §2.1.1). -/
def ecPublicKeyOid : Oid :=
  -- X.690 §8.19: 0x2a for 1.2, 840 as 86 48, 10045 as ce 3d, then 2 and 1.
  ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]⟩

/-- prime256v1, the P-256 named curve `1.2.840.10045.3.1.7` (RFC 5480 §2.1.1.1). -/
def p256Oid : Oid :=
  -- X.690 §8.19: 0x2a for 1.2, 840 as 86 48, 10045 as ce 3d, then 3, 1 and 7.
  ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩

/-- Decode an uncompressed P-256 SubjectPublicKeyInfo (RFC 5480 §§2.1.1, 2.1.1.1, 2.2). -/
def readP256 (spki : ByteArray) : Except TlsCertError EthLib.Cryptography.Secp256r1.Point := do
  -- One SubjectPublicKeyInfo, with no byte after it.
  let sequence ← der (Der.exact 0x30 spki)
  -- §4.1: `SubjectPublicKeyInfo ::= SEQUENCE { algorithm AlgorithmIdentifier, ... }`.
  match ← fields 0x30 sequence with
  | [algorithm, key] =>
    let (oid, parameter) ← readAlgorithm algorithm
    -- §2.1.1: the parameters are ECParameters, which MUST be present.
    --
    -- Only namedCurve, an OBJECT IDENTIFIER, is read: §2.1.1 forbids the other two in PKIX.
    let curve ← der (Der.exact 6 parameter)
    -- §2.1.1: the algorithm is id-ecPublicKey, and §2.1.1.1: the curve is secp256r1.
    ensure (oid = ecPublicKeyOid ∧ (← der (Der.oid curve)) = p256Oid) .algorithm
    -- §2.2: the ECPoint, an OCTET STRING, is the bits of subjectPublicKey.
    let bytes ← der (Der.bitString key)
    -- §2.2: the uncompressed form, 0x04, then the point on the curve, by SEC 1 v2 §2.3.4.
    --
    -- §2.2 lets an implementation support the compressed form; EthLib rejects it.
    match EthLib.Cryptography.Secp256r1.decodeUncompressed bytes.data.toList with
    | some point => return point
    | none => throw .publicKey
  | _ => throw .publicKey

/-- Verify ECDSA/SHA-256 under an uncompressed P-256 SPKI, with strict DER scalars. -/
def verifyP256 (spki message signature : ByteArray) : Bool :=
  -- The key, and `Ecdsa-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }` of RFC 3279 §2.2.3.
  match readP256 spki, Der.decodeEcdsaScalars signature with
  -- ECDSA verification of `(r, s)` over the SHA-256 hash of the message, read big-endian.
  | .ok point, some (r, s) =>
    EthLib.Cryptography.Secp256r1.verify point
      (EthLib.Base.bytesToNat (EthLib.Cryptography.Hash.Sha256.hash32 message).toList) r s
  -- A malformed key or signature verifies nothing.
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
  -- The extension value is one DER value, with no byte after it.
  let sequence ← der (Der.exact 0x30 bytes)
  -- `SignedKey ::= SEQUENCE { publicKey OCTET STRING, signature OCTET STRING }`.
  match ← fields 0x30 sequence with
  | [key, signature] =>
    ensure (key.tag = 4 ∧ signature.tag = 4) .certificate
    return (key.content, signature.content)
  | _ => throw .certificate

/-- The OID bytes of the first critical extension other than the libp2p one, or else `[]`. -/
def criticalOid (extensions : List Extension) : List UInt8 :=
  ((extensions.find? fun ext => ext.critical && !(ext.oid == libp2pOid)).map
    (·.oid.data.toList)).getD []

/-- Find the libp2p extension after rejecting every other critical extension, libp2p TLS. -/
def signedKey (certificate : Certificate) : Except TlsCertError (ByteArray × ByteArray) := do
  -- Peer Authentication: abort if the certificate contains critical extensions not understood.
  --
  -- Only the libp2p extension is understood here, and it MAY be marked critical.
  --
  -- Non-critical extensions with unknown OIDs are ignored.
  --
  -- When the check fails, some extension is critical, so the error names its real OID.
  ensure (certificate.extensions.all (fun ext => !ext.critical || ext.oid == libp2pOid))
    (.criticalExtension (criticalOid certificate.extensions))
  -- The extension with the OID `1.3.6.1.4.1.53594.1.1`.
  match certificate.extensions.filter (fun ext => ext.oid == libp2pOid) with
  -- If this extension is missing, endpoints MUST abort the connection attempt.
  | [] => throw .missingExtension
  -- Its value is the DER encoding of a SignedKey.
  | [extension] => readSignedKey extension.value
  -- Two instances: RFC 5280 §4.2 forbids them, and the certificate reader rejects them already.
  | _ => throw (.duplicateExtension libp2pOid.data.toList)

/-- The message the host key signs: `libp2p-tls-handshake:`, then the certificate's SPKI. -/
def hostMessage (spki : ByteArray) : ByteArray :=
  -- The concatenation of the string and the encoded SubjectPublicKeyInfo of the certificate.
  "libp2p-tls-handshake:".toUTF8 ++ spki

/-- Verify the host signature and derive the peer ID, libp2p peer IDs [Keys][keys].

[keys]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/peer-ids/peer-ids.md#keys
-/
def authenticateHost (policy : Policy) (spki key signature : ByteArray) :
    Except TlsCertError ByteArray := do
  -- The publicKey of SignedKey is a PublicKey protobuf: field 1, Type, then field 2, Data.
  --
  -- The encoding is deterministic: minimal varints, fields in tag order, exactly two fields.
  match key.data.toList with
  -- Type Secp256k1, 2.
  | 8 :: 2 :: _ =>
    -- The application enables or disables each key type.
    ensure (.secp256k1 ∈ policy.hostAlgorithms) .algorithm
    -- Data is a Bitcoin-encoded key; EthLib accepts only the compressed 33-byte form.
    let point ← (Libp2p.decodePublicKey key).mapError (fun _ => .publicKey)
    -- Peers MUST verify the signature, ECDSA over SHA-256 for this key type.
    ensure (Libp2p.verify key (hostMessage spki) signature = true) .hostSignature
    -- The peer ID of the key: its encoding has 37 bytes, at most 42, so the identity multihash.
    return Libp2p.peerId point
  -- Type ECDSA, 3, then field 2 with a length of 91 bytes: a P-256 SubjectPublicKeyInfo.
  | 8 :: 3 :: 18 :: 91 :: bytes =>
    ensure (.p256 ∈ policy.hostAlgorithms) .algorithm
    -- Exactly the 91 bytes that the length announces, with no further field.
    ensure (bytes.length = 91) .publicKey
    -- Data is a SubjectPublicKeyInfo in DER: id-ecPublicKey, secp256r1, uncompressed point.
    let hostSpki : ByteArray := ⟨bytes.toArray⟩
    let _ ← readP256 hostSpki
    -- Peers MUST verify the signature, ECDSA over SHA-256 for this key type.
    ensure (verifyP256 hostSpki (hostMessage spki) signature = true) .hostSignature
    -- The key encodes to 95 bytes, more than 42, so the SHA-256 multihash: 0x12, 0x20, digest.
    return ⟨#[0x12, 0x20]⟩ ++ EthLib.Cryptography.Hash.Sha256.hash key
  -- RSA (0), Ed25519 (1), and ECDSA keys whose Data is not a 91-byte SPKI: unsupported.
  | 8 :: 0 :: _ | 8 :: 1 :: _ | 8 :: 3 :: _ => throw .algorithm
  -- Any other first bytes do not encode a PublicKey of a known type.
  | _ => throw .publicKey

/-- Check validity, unique identifiers, self-signature, extension and host signature.

The only implemented self-signature backend is P-256/SHA-256, with absent parameters.

The caller's policy must explicitly enable it. -/
def authenticateCertificate (policy : Policy) (now : Nat) (certificate : Certificate) :
    Except TlsCertError AuthenticatedPeer := do
  -- Abort if the certificate is not yet valid, or if it is expired.
  --
  -- RFC 5280 §4.1.2.5: the period runs from notBefore through notAfter, inclusive.
  ensure (certificate.notBefore ≤ Int.ofNat now ∧ Int.ofNat now ≤ certificate.notAfter)
    (.validity now certificate.notBefore certificate.notAfter)
  -- Endpoints MAY abort if either unique identifier is present: the policy decides.
  ensure (policy.rejectUniqueIds = false ∨
    (certificate.issuerUniqueId = false ∧ certificate.subjectUniqueId = false)) .uniqueId
  -- The self-signature: ecdsa-with-SHA256, if the policy enables it.
  --
  -- RFC 5758 §3.2: the encoding of this algorithm identifier MUST omit the parameters field.
  ensure (.p256Sha256 ∈ policy.certificateAlgorithms ∧
    certificate.signatureAlgorithm = ecdsaSha256Oid ∧
    certificate.signatureParameters.isEmpty = true)
    .algorithm
  -- Abort if the self-signature of the certificate, over the TBSCertificate, is not valid.
  --
  -- It verifies under the key of the certificate itself, which must be a P-256 key.
  ensure (verifyP256 certificate.spki certificate.tbs certificate.signature = true) .selfSignature
  -- The libp2p Public Key Extension, after the check of critical extensions.
  let (key, signature) ← signedKey certificate
  -- The host key signs the SubjectPublicKeyInfo of the certificate, and gives the peer ID.
  let id ← authenticateHost policy certificate.spki key signature
  return ⟨id, certificate⟩

/-- Authenticate exactly one certificate, libp2p TLS "Peer Authentication". -/
def authenticate (policy : Policy) (now : Nat) (chain : List ByteArray) :
    Except TlsCertError AuthenticatedPeer := do
  match chain with
  -- Exactly one certificate, parsed, then authenticated.
  | [bytes] => authenticateCertificate policy now (← readCertificate bytes)
  -- Abort if more than one certificate is received.
  --
  -- An empty chain fails too, since endpoints MUST verify the identity of the peer.
  | _ => throw (.chain chain.length)

/-- A dialer also checks the intended peer ID, libp2p TLS "libp2p Public Key Extension". -/
def authenticatePeer (policy : Policy) (now : Nat) (expected : ByteArray)
    (chain : List ByteArray) : Except TlsCertError AuthenticatedPeer := do
  let peer ← authenticate policy now chain
  -- Clients MUST verify that the peer ID derived from the certificate is the intended one.
  ensure (peer.peerId = expected) .peerId
  return peer

end EthLib.Networking.Libp2p.Tls
