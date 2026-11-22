module

public import EthLib.Networking.Quic.Tls
public import EthLib.Networking.Quic.Tls.Crypto
public import EthLib.Networking.Quic.Tls.Extensions
public import EthLib.Networking.Quic.Tls.Transcript
public import EthLib.Networking.Quic.Keys

/-!
# The certificate handshake of libp2p QUIC

The pure steps follow [RFC 8446 §4][tls] and [RFC 9001 §4][quic].

Peer authentication and ALPN follow [libp2p TLS at 4facaf9][libp2p].

Every caller supplies its algorithm policy, credentials and ephemeral keys.

There is no default profile, pre-shared-key handshake, resumption or 0-RTT.

One input is one complete handshake message after CRYPTO reassembly.

Its encryption level is checked here; packet protection and reassembly belong to QUIC.

The caller keeps the same configuration throughout one handshake and discards state after an error.

Ephemeral keys must be fresh and secret, and no function claims constant-time execution.

CertificateVerify signatures use the deterministic nonce of RFC 6979, so no caller supplies one.

[tls]: https://www.rfc-editor.org/rfc/rfc8446#section-4
[quic]: https://www.rfc-editor.org/rfc/rfc9001#section-4
[libp2p]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/tls/tls.md
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Handshake

open EthLib.Base
open Wire

/-- A TLS alert, QUIC protocol violation, invalid local configuration or primitive failure. -/
inductive Error where
  | unexpectedMessage
  | illegalParameter
  /-- The extension `type`, which the message needs, is absent (RFC 8446 §6.2). -/
  | missingExtension (type : CodePoint)
  /-- The extension `type` was not offered, or is not allowed here (RFC 8446 §6.2). -/
  | unsupportedExtension (type : CodePoint)
  | handshakeFailure
  | protocolVersion
  | noApplicationProtocol
  | certificateRequired
  | decodeError
  | decryptError
  | protocolViolation
  | configuration
  | certificate (error : Libp2p.Tls.TlsCertError)
  | crypto (error : Crypto.Error)
  deriving Repr, DecidableEq

/-- The QUIC connection error, RFC 9000 §20.1; a TLS alert maps to 0x100 + alert, RFC 9001 §4.8. -/
def Error.code : Error → UInt32
  -- RFC 8446 §6: unexpected_message is alert 10, so the code is 0x0100 + 10.
  | .unexpectedMessage => 0x10a
  -- illegal_parameter is alert 47.
  | .illegalParameter => 0x12f
  -- missing_extension is alert 109.
  | .missingExtension _ => 0x16d
  -- unsupported_extension is alert 110.
  | .unsupportedExtension _ => 0x16e
  -- handshake_failure is alert 40.
  | .handshakeFailure => 0x128
  -- protocol_version is alert 70.
  | .protocolVersion => 0x146
  -- no_application_protocol is alert 120, the code 0x0178 of RFC 9001 §8.1.
  | .noApplicationProtocol => 0x178
  -- certificate_required is alert 116.
  | .certificateRequired => 0x174
  -- decode_error is alert 50.
  | .decodeError => 0x132
  -- decrypt_error is alert 51.
  | .decryptError => 0x133
  -- RFC 9000 §20.1: PROTOCOL_VIOLATION is the transport error 0x0a, not a TLS alert.
  | .protocolViolation => 0x0a
  -- EthLib's choice: a fault of the local configuration is internal_error, alert 80.
  | .configuration => 0x150
  -- EthLib's choice: a rejected certificate is bad_certificate, alert 42.
  | .certificate _ => 0x12a
  -- §§4.2.8.2 and 7.4.2 name no alert for a bad peer share or a degenerate secret.
  --
  -- EthLib takes illegal_parameter, a field the peer got wrong (§6.2).
  | .crypto .keyShare | .crypto .sharedSecret => 0x12f
  -- Every other failure of a primitive is local, so it is internal_error.
  | .crypto _ => 0x150

/-- The CRYPTO encryption level of a handshake message, RFC 9001 §4. -/
inductive Level where
  | initial
  | handshake
  | application
  deriving Repr, DecidableEq

/-- The order of the encryption levels, from Initial to 1-RTT, RFC 9001 §4.1.3. -/
def Level.rank : Level → Nat
  -- §4.1.3: CRYPTO frames use three of the four levels, without 0-RTT, in this order.
  | .initial => 0
  | .handshake => 1
  | .application => 2

/-- Complete handshake bytes and the encryption level at which QUIC carries them. -/
structure FlightMessage where
  level : Level
  data : ByteArray

/-- An explicit application policy; every listed algorithm must have a backend here.

The session-ID choice implements the server SHOULD of RFC 9001 §8.4.

The policy has no default, since RFC 8446 §9.1 leaves that choice to an application profile. -/
structure Policy where
  cipherSuites : List CodePoint
  groups : List CodePoint
  signatureSchemes : List CodePoint
  certificates : Libp2p.Tls.Policy
  rejectLegacySessionId : Bool

/-- One local ephemeral secret, with the group whose encoding interprets it. -/
structure EphemeralKey where
  group : CodePoint
  secret : Vector UInt8 32

/-- Explicit inputs for one endpoint and one handshake.

The initial client shares are a subset of the policy's groups, in its order.

Other ephemeral keys allow a client to answer HelloRetryRequest.

The ephemeral keys belong to this handshake alone. -/
structure Config where
  policy : Policy
  now : Nat
  certificates : List ByteArray
  signingKey : Vector UInt8 32
  random : Vector UInt8 32
  ephemeralKeys : List EphemeralKey
  initialShares : List CodePoint
  transportParameters : ByteArray

/-- The receive phase of a certificate handshake, RFC 8446 Appendix A. -/
inductive Phase where
  | serverHello
  | encryptedExtensions
  | certificateRequest
  | serverCertificate
  | serverCertificateVerify
  | serverFinished
  | clientHello
  | clientCertificate
  | clientCertificateVerify
  | clientFinished
  | complete
  deriving Repr, DecidableEq

/-- The parameters which a HelloRetryRequest fixes for the second ClientHello. -/
structure Retry where
  suite : CodePoint
  group : Option CodePoint
  cookie : Option Extension

/-- The negotiated parameters and their transcript boundaries, RFC 8446 §7.1. -/
structure Negotiated where
  suite : CodePoint
  group : CodePoint
  sharedSecret : Vector UInt8 32
  helloTranscript : ByteArray
  serverTranscript : ByteArray
  secrets : KeySchedule

/-- Saved inputs of the pure steps; completion authenticates the saved certificate again.

Callers obtain this state from initialization and successful steps. -/
structure State where
  phase : Phase
  transcript : Transcript
  hello : Option ClientHello
  retry : Option Retry
  negotiated : Option Negotiated
  peerChain : List ByteArray
  request : Option CertificateRequest

/-- The certificate-derived peer identity, its chain and the negotiated key schedule.

On a state reached from initialization, the peer's CertificateVerify and Finished were checked.

No theorem yet proves that for every reachable state. -/
structure Completion where
  peerId : ByteArray
  peerChain : List ByteArray
  negotiated : Negotiated

/-- The next state, its outgoing flight, and an authenticated result only at completion. -/
structure Step where
  state : State
  output : List FlightMessage
  completion : Option Completion

/-- The ALPN protocol name that the ALPN section of libp2p TLS fixes. -/
def libp2p : ByteArray := "libp2p".toUTF8

/-- The two implemented SHA-256 suites; other transcript hashes are unavailable. -/
def supportedSuite (suite : CodePoint) : Bool :=
  -- RFC 8446 Appendix B.4: TLS_AES_128_GCM_SHA256 is {0x13,0x01}.
  --
  -- TLS_CHACHA20_POLY1305_SHA256 is {0x13,0x03}.
  suite.val == 0x1301 || suite.val == 0x1303

/-- Separate an unexpected message type from malformed data, RFC 8446 §§4 and 6.2. -/
def wire {α : Type} (value : Except Wire.Error α) : Except Error α :=
  value.mapError fun
    -- §6.2: an inappropriate message, such as the wrong handshake message, is unexpected_message.
    | .messageType _ | .retry => .unexpectedMessage
    -- §6.2: a field that is incorrect, or inconsistent with other fields, is illegal_parameter.
    --
    -- §4.2 names no alert for a repeated extension type, so EthLib takes this one.
    | .constant | .duplicateExtension _ => .illegalParameter
    -- §6.2: a message that does not conform to the formal protocol syntax is decode_error.
    | _ => .decodeError

/-- A value whose absence means that a caller supplied an inconsistent state. -/
def saved {α : Type} : Option α → Except Error α
  | some value => .ok value
  | none => .error .configuration

/-- The first extension of a type; the message codec rejects duplicate types. -/
def extension (kind : CodePoint) (extensions : List Extension) : Option Extension :=
  -- §4.2: there MUST NOT be more than one extension of the same type in a block.
  extensions.find? (fun e => e.kind == kind)

/-- Require an optional field with the error appropriate to its protocol context. -/
def required {α : Type} (error : Error) : Option α → Except Error α
  | some value => .ok value
  | none => .error error

/-- Read a required extension in its message-specific form, RFC 8446 §4.2. -/
def payload (form : PayloadForm) (extensions : List Extension) : Except Error Payload := do
  -- §6.2: a message without an extension it must carry is missing_extension.
  let value ← required (.missingExtension form.type) (extension form.type extensions)
  -- The extension data holds the structure of the form, and nothing after it.
  wire (decodePayload form value)

/-- Read an ALPN list without selecting a protocol, RFC 7301 §3.1. -/
def alpn (extensions : List Extension) : Except Error (List ByteArray) := do
  -- RFC 9001 §8.1: without ALPN, no application protocol is negotiated.
  --
  -- So the endpoint closes the connection with no_application_protocol.
  let value ← required .noApplicationProtocol (extension PayloadForm.alpn.type extensions)
  -- RFC 7301 §3.1: `ProtocolName protocol_name_list<2..2^16-1>`.
  match ← wire (decodePayload .alpn value) with
  | .alpn protocols => return protocols
  | _ => throw .decodeError

/-- Read the offered groups, RFC 8446 §4.2.7. -/
def groups (extensions : List Extension) : Except Error (List CodePoint) := do
  -- §4.2.7: `NamedGroup named_group_list<2..2^16-1>;`, most preferred first.
  match ← payload .supportedGroups extensions with
  | .supportedGroups values => return values
  | _ => throw .decodeError

/-- Read offered signature schemes, RFC 8446 §4.2.3. -/
def signatures (extensions : List Extension) : Except Error (List CodePoint) := do
  -- §4.2.3: `SignatureScheme supported_signature_algorithms<2..2^16-2>;`.
  match ← payload .signatureAlgorithms extensions with
  | .signatureAlgorithms values => return values
  | _ => throw .decodeError

/-- Read ClientHello's shares, RFC 8446 §4.2.8. -/
def shares (extensions : List Extension) : Except Error (List KeyShareEntry) := do
  -- §4.2.8: `KeyShareEntry client_shares<0..2^16-1>;`, in descending order of preference.
  match ← payload .clientKeyShare extensions with
  | .clientKeyShare values => return values
  | _ => throw .decodeError

/-- Select the first local preference also offered by the peer, RFC 8446 §4.1.1. -/
def select (preferences offered : List CodePoint) : Except Error CodePoint :=
  -- §4.1.1: the selecting side picks from the overlap; EthLib takes its own first preference.
  --
  -- With no overlap, it MUST abort with handshake_failure or insufficient_security.
  --
  -- EthLib takes handshake_failure.
  required .handshakeFailure (preferences.find? (fun value => value ∈ offered))

/-- Find the local secret for a selected group without substituting another key. -/
def ephemeral (config : Config) (group : CodePoint) : Except Error (Vector UInt8 32) := do
  -- The secret configured for this group; none is a fault of the local configuration.
  let key ← required .configuration (config.ephemeralKeys.find? (fun key => key.group == group))
  return key.secret

/-- Enforce digitalSignature when KeyUsage is present, RFC 8446 §4.4.2.2 and RFC 5280 §4.2.1.3. -/
def checkSigningUsage (certificate : Libp2p.Tls.Certificate) : Except Error Unit :=
  certificate.extensions.forM fun value => do
    -- RFC 5280 §4.2.1.3: the key usage extension has the OID { id-ce 15 }, that is 2.5.29.15.
    if value.oid = (⟨#[0x55, 0x1d, 0x0f]⟩ : ByteArray) then
      -- RFC 5280 §4.2.1.3: its value is a BIT STRING, tag 3.
      let bits ← (EthLib.Serialization.Der.exact 3 value.value).mapError
        (fun error => Error.certificate (.der error))
      -- X.690 §§8.6.2 and 11.2.1: the initial octet and the unused bits are valid DER.
      let _ ← (EthLib.Serialization.Der.validBits bits.content).mapError
        (fun error => Error.certificate (.der error))
      match bits.content.toList with
      -- X.690 §8.6.2.1: bit 0, digitalSignature, is bit 8 of the first subsequent octet.
      --
      -- RFC 8446 §4.4.2.2: the digitalSignature bit MUST be set.
      | _ :: first :: _ => ensure (first.toNat / 128 = 1) (.certificate .publicKey)
      -- An empty bit string has no digitalSignature bit set.
      | _ => throw (.certificate .publicKey)
    -- Without the key usage extension, nothing restricts the key.
    else pure ()

/-- Validate the explicit implementation choices without providing a default profile. -/
def validateConfig (config : Config) : Except Error Unit := do
  -- EthLib's check: the policy names a cipher suite, a group and a signature scheme.
  ensure (config.policy.cipherSuites ≠ [] ∧ config.policy.groups ≠ [] ∧
    config.policy.signatureSchemes ≠ []) .configuration
  -- EthLib's check: every listed algorithm has a backend here.
  ensure (config.policy.cipherSuites.all supportedSuite ∧
    config.policy.groups.all Crypto.supportedGroup ∧
    config.policy.signatureSchemes.all Crypto.supportedSignatureScheme) .configuration
  -- RFC 8446 §4.2.8: the shares follow the order of the groups, with at most one per group.
  --
  -- EthLib's check: no group is listed twice, and no group has two ephemeral keys.
  ensure (config.initialShares.Sublist config.policy.groups ∧
    config.policy.groups.Nodup ∧ config.initialShares.Nodup ∧
    (config.ephemeralKeys.map (·.group)).Nodup) .configuration
  -- Each group of the policy has an ephemeral key, for a first share or after a retry.
  config.policy.groups.forM fun group => do
    let _ ← ephemeral config group
    pure ()
  -- libp2p tls.md, Peer Authentication: the own certificate passes the checks of the peer.
  let peer ← (Libp2p.Tls.authenticate config.policy.certificates config.now
    config.certificates).mapError Error.certificate
  -- libp2p permits a receiver to tolerate unique IDs, but a sender must omit them.
  ensure (peer.certificate.issuerUniqueId = false ∧ peer.certificate.subjectUniqueId = false)
    .configuration
  -- RFC 8446 §4.4.2.2: the certificate MUST allow its key to be used for signing.
  checkSigningUsage peer.certificate
  -- §4.4.3: the signing key is the private key of the certificate that is sent.
  ensure (Crypto.publicKeyMatches config.signingKey peer.certificate.spki = true) .configuration

/-- Build a typed payload's extension, checking its presentation bounds. -/
def encodedPayload (value : Payload) : Except Error Extension := wire (encodePayload value)

/-- Encode a complete outgoing handshake message, then retain those exact transcript bytes. -/
def emit (state : State) (level : Level) (message : Message) :
    Except Error (State × FlightMessage) := do
  -- RFC 8446 §4: the handshake type, the uint24 length, then the body.
  --
  -- With SHA-256, `Hash.length` is 32, the length of Finished.
  let data ← wire (encode 32 message)
  -- §4.4.1: the transcript takes the message exactly as sent, its header included.
  let transcript ← wire (state.transcript.append data)
  -- RFC 9001 §4.1.3: TLS hands the bytes to QUIC with their encryption level.
  return ({ state with transcript }, ⟨level, data⟩)

/-- Preserve an accepted incoming message byte for byte, RFC 8446 §4.4.1. -/
def receive (state : State) (input : FlightMessage) : Except Error State := do
  -- §4.4.1: the transcript takes the message exactly as received, its header included.
  return { state with transcript := ← wire (state.transcript.append input.data) }

/-- Check that a message arrived at its required QUIC encryption level, RFC 9001 §4. -/
def checkLevel (expected : Level) (input : FlightMessage) : Except Error Unit := do
  -- RFC 9001 §4.1.3: new data at an earlier level than expected is a PROTOCOL_VIOLATION.
  ensure (expected.rank ≤ input.level.rank) .protocolViolation
  -- §4.1.3: QUIC buffers data for a later level, so data that reaches TLS here is unexpected.
  --
  -- §4.1.3 names no error for this; EthLib takes unexpected_message.
  ensure (input.level = expected) .unexpectedMessage

/-- Decode one complete message at its required QUIC encryption level, RFC 9001 §4. -/
def readMessage (expected : Level) (input : FlightMessage) : Except Error Message := do
  checkLevel expected input
  -- RFC 8446 §4: exactly one handshake message, with the 32-byte Finished of SHA-256.
  wire (Wire.exact (decodeList 32) input.data.data.toList)

/-- Empty saved inputs before either endpoint receives a message. -/
def initialState (phase : Phase) : State := ⟨phase, {}, none, none, none, [], none⟩

/-- Build a key-share entry from the configured secret, RFC 8446 §4.2.8. -/
def localShare (config : Config) (group : CodePoint) : Except Error KeyShareEntry := do
  let secret ← ephemeral config group
  -- §§4.2.8.2 and 7.4.2: the key exchange bytes are the public value of the secret.
  let bytes ← (Crypto.keyShare group secret).mapError Error.crypto
  -- §4.2.8: the entry is the named group, then its key exchange bytes.
  return ⟨group, bytes⟩

/-- Generate a TLS 1.3-only ClientHello without SNI, libp2p TLS Future Extensibility. -/
def makeClientHello (config : Config) : Except Error ClientHello := do
  -- §4.2.8: one share for each initial group, in the order of the supported groups.
  let keyShares ← config.initialShares.mapM (localShare config)
  -- §4.2.1: the supported versions are 0x0304 alone, as RFC 9001 §4.2 forbids older versions.
  let extensions ← [Payload.supportedVersions [0x0304],
    -- §§4.2.7 and 4.2.3: the groups and signature schemes of the policy, in its order.
    .supportedGroups config.policy.groups, .signatureAlgorithms config.policy.signatureSchemes,
    -- §4.2.8: the key shares; libp2p tls.md, ALPN: the one protocol name libp2p.
    .clientKeyShare keyShares, .alpn [libp2p],
    -- RFC 9001 §8.2: endpoints MUST send the QUIC transport parameters extension.
    .quicTransportParameters config.transportParameters].mapM encodedPayload
  -- §4.1.2: the random, an empty legacy session ID, the cipher suites, then the extensions.
  --
  -- The session ID is empty, since RFC 9001 §8.4 forbids the middlebox compatibility mode.
  --
  -- libp2p tls.md, Future Extensibility: the client sends no server name.
  return ⟨config.random, .empty, config.policy.cipherSuites, extensions⟩

/-- Send ClientHello and wait for ServerHello or one retry, RFC 8446 §4.1.2. -/
def clientStart (config : Config) : Except Error Step := do
  -- EthLib's check: the configuration is complete and consistent before any message.
  validateConfig config
  -- §4.1.2: the client sends ClientHello as its first TLS message.
  let hello ← makeClientHello config
  -- Appendix A.1: Send ClientHello moves START to WAIT_SH.
  --
  -- RFC 9001 §4.1.5: ClientHello travels at the Initial level.
  let (state, message) ← emit { initialState .serverHello with hello := some hello }
    .initial (.clientHello hello)
  return ⟨state, [message], none⟩

/-- Wait for ClientHello with an explicit local policy and credentials. -/
def serverStart (config : Config) : Except Error State := do
  -- EthLib's check: the configuration is complete and consistent before any message.
  validateConfig config
  -- §4.1.3: a ServerHello random equal to that of HelloRetryRequest would read as a retry.
  ensure (config.random ≠ retryRandom) .configuration
  -- Appendix A.2: START, waiting for ClientHello.
  return initialState .clientHello

/-- The message contexts of RFC 8446 §4.2 and RFC 9001 §8.2. -/
inductive Context where
  | clientHello | serverHello | retry | encryptedExtensions | certificateRequest | certificate
  | newSessionTicket
  deriving DecidableEq

/-- Placement of every extension recognized here, with unknown types left uninterpreted. -/
def allowedExtension (context : Context) (kind : CodePoint) : Bool :=
  let contexts := match kind.val with
    -- §4.2, CH and EE: server name, max fragment length, supported groups and use SRTP.
    --
    -- CH and EE too: heartbeat, ALPN, and the client and server certificate types.
    --
    -- RFC 9001 §8.2: the QUIC transport parameters (57) are in CH and EE too.
    | 0 | 1 | 10 | 14 | 15 | 16 | 19 | 20 | 57 =>
      some [Context.clientHello, .encryptedExtensions]
    -- Status request and signed certificate timestamp: CH, CR and CT.
    | 5 | 18 => some [.clientHello, .certificateRequest, .certificate]
    -- Signature algorithms, certificate authorities and signature algorithms cert: CH and CR.
    | 13 | 47 | 50 => some [.clientHello, .certificateRequest]
    -- Padding, PSK key exchange modes and post-handshake auth: CH only.
    | 21 | 45 | 49 => some [.clientHello]
    -- Pre-shared key: CH and SH.
    | 41 => some [.clientHello, .serverHello]
    -- Early data: CH, EE and NST.
    | 42 => some [.clientHello, .encryptedExtensions, .newSessionTicket]
    -- Supported versions and key share: CH, SH and HRR.
    | 43 | 51 => some [.clientHello, .serverHello, .retry]
    -- Cookie: CH and HRR.
    | 44 => some [.clientHello, .retry]
    -- OID filters: CR only.
    | 48 => some [.certificateRequest]
    -- An extension this table does not list is not recognized here.
    | _ => none
  match contexts with
  -- §4.1.2: servers MUST ignore unrecognized extensions, and clients do too here.
  | none => true
  | some contexts => context ∈ contexts

/-- Validate placement and, for a response, the corresponding request, RFC 8446 §4.2. -/
def checkExtensions (context : Context) (offered : Option (List Extension))
    (extensions : List Extension) : Except Error Unit :=
  extensions.forM fun value => do
    -- §4.2: a recognized extension not specified for its message is illegal_parameter.
    --
    -- §6.2 also lists unsupported_extension for that case; erratum 6820 reports the clash.
    ensure (allowedExtension context value.kind = true) .illegalParameter
    match offered with
    -- A ClientHello, a CertificateRequest or a NewSessionTicket answers no request.
    | none => pure ()
    -- §4.2: a response holds only extensions that its request holds.
    --
    -- The exception is the cookie in HelloRetryRequest; any other is unsupported_extension.
    | some offered =>
      ensure ((context = .retry ∧ value.kind = 44) ∨
        (offered.any (fun request => request.kind == value.kind)) = true)
        (.unsupportedExtension value.kind)

/-- Read PSK identities while checking offer framing and binder count, RFC 8446 §4.2.11. -/
def pskIdentities (extensions : List Extension) : Except Error (List ByteArray) := do
  match extension 41 extensions with
  | none => return []
  | some psk =>
    -- §4.2.11, PskIdentity: `opaque identity<1..2^16-1>;`, then `uint32 obfuscated_ticket_age;`.
    let identity : Wire.Reader ByteArray := do
      let name ← blob 2 1 65535
      let _ ← uint 4
      return name.toByteArray
    let reader : Wire.Reader (List ByteArray) := do
      -- §4.2.11, OfferedPsks: `PskIdentity identities<7..2^16-1>;`.
      let identities ← items 2 7 65535 identity
      -- `PskBinderEntry binders<33..2^16-1>;`, each `opaque PskBinderEntry<32..255>;`.
      let binders ← items 2 33 65535 (blob 1 32 255)
      -- §4.2.11: one binder for each identity, in the same order.
      --
      -- §4.2.11 names no alert for a mismatch; EthLib takes illegal_parameter.
      require (identities.length = binders.length) .constant
      return identities
    -- The extension data is one OfferedPsks, and nothing after it.
    wire (Wire.exact reader psk.data.data.toList)

/-- Check the PSK offer's framing while declining to select it, RFC 8446 §§4.2.9 and 4.2.11. -/
def checkPskOffer (extensions : List Extension) : Except Error Unit := do
  match extension 45 extensions with
  | none => pure ()
  | some modes =>
    -- §4.2.9: `PskKeyExchangeMode ke_modes<1..255>;`, one byte per mode.
    let _ ← wire (Wire.exact (Wire.blob 1 1 255) modes.data.data.toList)
    pure ()
  match extension 41 extensions with
  -- §4.2.10: a client that sends early data MUST supply the pre-shared key extension too.
  --
  -- §4.2.10 names no alert; EthLib takes illegal_parameter.
  | none => ensure (extension 42 extensions = none) .illegalParameter
  | some psk =>
    -- §4.2.11: the pre-shared key extension MUST be the last one, else illegal_parameter.
    ensure (extensions.getLast? = some psk) .illegalParameter
    -- §4.2.9: a pre-shared key without PSK key exchange modes MUST abort the handshake.
    --
    -- §4.2.9 names no alert; EthLib takes missing_extension.
    let _ ← required (.missingExtension 45) (extension 45 extensions)
    -- §4.2.11: the offer is well formed, though the server never selects it.
    let _ ← pskIdentities extensions
    match extension 42 extensions with
    | none => pure ()
    -- §4.2.10: in a ClientHello, the early data indication is `Empty`.
    | some early => ensure (early.data = ByteArray.empty) .decodeError

/-- Validate the client offer; libp2p servers ignore SNI, including its opaque contents.

A PSK offer is never selected, and early data is never accepted. -/
def checkClientHello (config : Config) (hello : ClientHello) : Except Error Unit := do
  -- §4.2: each recognized extension is one that ClientHello may carry.
  checkExtensions .clientHello none hello.extensions
  -- RFC 9001 §8.4: a server SHOULD treat a nonempty legacy session ID as a PROTOCOL_VIOLATION.
  --
  -- The policy says whether this server follows that SHOULD.
  ensure (config.policy.rejectLegacySessionId = false ∨ hello.legacySessionId = ByteArray.empty)
    .protocolViolation
  -- Appendix D.2: a ClientHello without supported versions offers only TLS 1.2 or earlier.
  ensure (extension PayloadForm.supportedVersions.type hello.extensions).isSome .protocolVersion
  match ← payload .supportedVersions hello.extensions with
  -- §4.2.1: the server selects only a listed version, and RFC 9001 §4.2 requires TLS 1.3.
  --
  -- §6.2: a version recognized but not supported is protocol_version.
  | .supportedVersions versions => ensure ((0x0304 : CodePoint) ∈ versions) .protocolVersion
  | _ => throw .decodeError
  let offeredGroups ← groups hello.extensions
  let keyShares ← shares hello.extensions
  -- §4.2.8: each share is for a supported group, in the same order, and no group twice.
  --
  -- Servers MAY abort with illegal_parameter on a violation, and this server does.
  ensure ((keyShares.map (·.group)).Sublist offeredGroups ∧
    (keyShares.map (·.group)).Nodup) .illegalParameter
  -- §4.2.3: a server that authenticates with a certificate needs signature algorithms.
  --
  -- Without them it MUST abort with missing_extension.
  let _ ← signatures hello.extensions
  -- RFC 9001 §8.2: a ClientHello without QUIC transport parameters is missing_extension.
  let _ ← payload .quicTransportParameters hello.extensions
  -- §§4.2.9 to 4.2.11: a PSK offer is well formed, though never selected.
  checkPskOffer hello.extensions

/-- The parts of ClientHello which a non-PSK retry must preserve, RFC 8446 §4.1.2. -/
def stableHello (hello : ClientHello) : ClientHello :=
  { hello with extensions := hello.extensions.filter fun value =>
      -- §4.1.2: a retry may change the key share (51), cookie (44) and early data (42).
      --
      -- It may also change the padding (21) and pre-shared key (41); all else stays as sent.
      --
      -- EthLib allows no change for a future extension, since it recognizes none.
      value.kind != 51 && value.kind != 44 && value.kind != 42 && value.kind != 21 &&
      value.kind != 41 }

/-- Check the second ClientHello against the retry and first offer, RFC 8446 §§4.1.2 and 4.1.4. -/
def checkSecondHello (first second : ClientHello) (retry : Retry) : Except Error Unit := do
  -- §4.1.2: the client MUST send the same ClientHello, apart from the changes it lists.
  --
  -- §4.1.2 names no alert for the server; EthLib takes illegal_parameter for each change.
  ensure (stableHello first = stableHello second) .illegalParameter
  -- §4.1.2: early data is not permitted after a HelloRetryRequest.
  ensure (extension 42 second.extensions = none) .illegalParameter
  -- §4.2.2: the cookie of the retry, copied as received; without one, no cookie.
  ensure (extension 44 second.extensions = retry.cookie) .illegalParameter
  let originalIdentities ← pskIdentities first.extensions
  let updatedIdentities ← pskIdentities second.extensions
  -- §4.1.2: the client may only remove pre-shared keys, so the rest keep their order.
  ensure (updatedIdentities.Sublist originalIdentities) .illegalParameter
  match retry.group with
  -- §4.2.8: the new key share holds a single entry, for the group the retry selected.
  | some group =>
    let keyShares ← shares second.extensions
    ensure (keyShares.map (·.group) = [group]) .illegalParameter
  -- §4.1.2: without a group in the retry, the key share stays as sent.
  | none =>
    ensure (extension 51 first.extensions = extension 51 second.extensions) .illegalParameter

/-- Read and validate the selected TLS version before other ServerHello checks, RFC 8446 §4.2.1. -/
def selectedVersion (extensions : List Extension) : Except Error Unit := do
  -- §4.2.1: clients MUST check for this extension before the rest of ServerHello.
  --
  -- Appendix D.1: without it, the server chose TLS 1.2 or older, a protocol_version alert.
  ensure (extension PayloadForm.selectedVersion.type extensions).isSome .protocolVersion
  match ← payload .selectedVersion extensions with
  -- §4.2.1: a version not offered, or older than TLS 1.3, is illegal_parameter.
  --
  -- The client offers 0x0304 alone, so every other value is one of those.
  | .selectedVersion version => ensure (version = 0x0304) .illegalParameter
  | _ => throw .decodeError

/-- The peer's certificate, authenticated under the explicit libp2p policy.

For a dialer the expected peer ID is checked as well. -/
def authenticate (config : Config) (expected : Option ByteArray) (chain : List ByteArray) :
    Except Error Libp2p.Tls.AuthenticatedPeer := do
  -- libp2p tls.md, Peer Authentication: one valid self-signed certificate with the key extension.
  let peer ← (match expected with
    | none => Libp2p.Tls.authenticate config.policy.certificates config.now chain
    -- libp2p tls.md, Public Key Extension: a dialer checks that the peer ID is the one it expects.
    | some id => Libp2p.Tls.authenticatePeer config.policy.certificates config.now id chain)
      |>.mapError Error.certificate
  -- RFC 8446 §4.4.2.2: the key MUST be allowed to sign; EthLib asks it of a client too.
  checkSigningUsage peer.certificate
  return peer

/-- Recompute the schedule from the saved inputs and check the saved certificate chain again.

The peer's proof of key possession comes only from the CertificateVerify step. -/
def complete (config : Config) (expected : Option ByteArray) (state : State)
    (output : List FlightMessage) : Except Error Step := do
  let negotiated ← saved state.negotiated
  -- RFC 8446 §7.1: the key schedule, from the shared secret and the two saved transcripts.
  let secrets ← (keySchedule (packBytes negotiated.sharedSecret) negotiated.helloTranscript
    negotiated.serverTranscript).mapError fun _ => Error.configuration
  -- EthLib's check: the saved chain is authenticated again, so the result carries its identity.
  let peer ← authenticate config expected state.peerChain
  let negotiated := { negotiated with secrets }
  -- Appendix A: CONNECTED, with the peer ID that the certificate gives.
  return ⟨{ state with phase := .complete, negotiated := some negotiated }, output,
    some ⟨peer.peerId, state.peerChain, negotiated⟩⟩

/-- Start handshake traffic derivation at the exact ServerHello transcript boundary. -/
def negotiate (state : State) (suite group : CodePoint) (shared : Vector UInt8 32) :
    Except Error State := do
  -- RFC 8446 §7.1: the handshake traffic secrets take the transcript ClientHello...ServerHello.
  let hello := state.transcript.bytes
  -- The application secrets wait for server Finished, so their transcript is empty here.
  let secrets ← (keySchedule (packBytes shared) hello .empty).mapError fun _ => Error.configuration
  return { state with negotiated := some ⟨suite, group, shared, hello, .empty, secrets⟩ }

/-- Retain the transcript through server Finished before deriving application traffic secrets. -/
def serverBoundary (state : State) : Except Error State := do
  let negotiated ← saved state.negotiated
  -- RFC 8446 §7.1: the application traffic secrets take ClientHello...server Finished.
  let server := state.transcript.bytes
  let secrets ← (keySchedule (packBytes negotiated.sharedSecret)
    negotiated.helloTranscript server).mapError fun _ => Error.configuration
  return { state with negotiated := some { negotiated with serverTranscript := server, secrets } }

/-- Encode the configured chain with an empty request context, RFC 8446 §4.4.2. -/
def certificateMessage (config : Config) : Message :=
  -- §4.4.2: the request context is empty in the main handshake.
  --
  -- Each entry holds one certificate and no extensions.
  --
  -- libp2p tls.md, Peer Authentication: the chain is one certificate, as validation checks.
  .certificate ⟨.empty, config.certificates.map fun data => ⟨data, []⟩⟩

/-- Sign the transcript through Certificate, with the sender's role, RFC 8446 §4.4.3.

The signature is a function of the signing key and the signed content alone. -/
def sendCertificateVerify (config : Config) (server : Bool) (offered : List CodePoint)
    (state : State) : Except Error (State × FlightMessage) := do
  -- §4.4.3: the algorithm is one the peer offered in its signature algorithms extension.
  let algorithm ← select config.policy.signatureSchemes offered
  -- §4.4.3: octet 32 repeated 64 times, the context string of the role, a 0 byte, the content.
  --
  -- The content is `Transcript-Hash(Handshake Context, Certificate)`, the transcript so far.
  let content := certificateVerifyInput server state.transcript.hash
  -- §4.4.3: the signature with the private key of the certificate just sent.
  let signature ← (Crypto.signCertificateVerify algorithm config.signingKey content).mapError
    Error.crypto
  -- §4.4.3: CertificateVerify follows Certificate, at the Handshake level.
  emit state .handshake (.certificateVerify algorithm signature)

/-- Compute Finished before including its own encoding in the transcript, RFC 8446 §4.4.4. -/
def sendFinished (server : Bool) (state : State) : Except Error (State × FlightMessage) := do
  let negotiated ← saved state.negotiated
  -- §4.4: the Base Key is the handshake traffic secret of the sender.
  let secret := if server then negotiated.secrets.serverHandshake
    else negotiated.secrets.clientHandshake
  -- §4.4.4: the finished key is `HKDF-Expand-Label(BaseKey, "finished", "", Hash.length)`.
  --
  -- §4.4.4: the verify data is the HMAC, under that key, of the transcript hash so far.
  let value ← (finished secret state.transcript.bytes).mapError
    fun _ => Error.configuration
  emit state .handshake (.finished (packBytes value))

/-- Verify the peer's CertificateVerify before appending it to the transcript, RFC 8446 §4.4.3. -/
def checkCertificateVerify (config : Config) (expected : Option ByteArray) (server : Bool)
    (offered : List CodePoint) (state : State) (algorithm : CodePoint)
    (signature : ByteArray) : Except Error Unit := do
  -- §4.4.3: the algorithm is one that this side offered; EthLib also requires it in the policy.
  --
  -- §4.4.3 names no alert for this; EthLib takes illegal_parameter.
  ensure (algorithm ∈ offered ∧ algorithm ∈ config.policy.signatureSchemes) .illegalParameter
  -- §4.4.3: the public key of the end-entity certificate of the Certificate message.
  let peer ← authenticate config expected state.peerChain
  -- §4.4.3: the content covered, from the transcript through Certificate.
  let content := certificateVerifyInput server state.transcript.hash
  -- §4.4.3: if the verification fails, a decrypt_error alert.
  ensure (Crypto.verifyCertificateVerify algorithm peer.certificate.spki content
    signature = true) .decryptError

/-- Verify Finished against the saved transcript, RFC 8446 §4.4.4. -/
def checkFinished (server : Bool) (state : State) (value : ByteArray) : Except Error Unit := do
  let negotiated ← saved state.negotiated
  -- §4.4: the Base Key is the handshake traffic secret of the sender of Finished.
  let secret := if server then negotiated.secrets.serverHandshake
    else negotiated.secrets.clientHandshake
  -- §4.4.4: the expected verify data, over the transcript before this Finished.
  let expected ← (finished secret state.transcript.bytes).mapError
    fun _ => Error.configuration
  -- §4.4.4: incorrect contents MUST terminate the connection with decrypt_error.
  ensure (value = packBytes expected) .decryptError

/-- Validate a certificate message and save its exact chain for later signature checks. -/
def receiveCertificate (config : Config) (expected : Option ByteArray) (offered : List Extension)
    (state : State) (certificate : CertificateMessage) : Except Error State := do
  -- §4.4.2.4: an empty server Certificate is decode_error.
  --
  -- An empty client Certificate MAY be certificate_required, and libp2p tls.md makes it so.
  let emptyError := if expected.isSome then Error.decodeError else .certificateRequired
  ensure (certificate.entries ≠ []) emptyError
  -- §4.4.2: the context of a server Certificate SHALL be zero length.
  --
  -- A client Certificate echoes the request context, empty in the main handshake (§4.3.2).
  --
  -- Neither section names an alert; EthLib takes illegal_parameter.
  ensure (certificate.context = ByteArray.empty) .illegalParameter
  -- §4.4.2: entry extensions correspond to ones in ClientHello, or in CertificateRequest.
  certificate.entries.forM fun entry => checkExtensions .certificate (some offered) entry.extensions
  -- libp2p tls.md, Peer Authentication: the chain is checked before it is saved.
  let chain := certificate.entries.map (·.data)
  let _ ← authenticate config expected chain
  return { state with peerChain := chain }

/-- The server flight after a usable client share, RFC 8446 §2. -/
def serverFlight (config : Config) (state : State) (hello : ClientHello)
    (suite group : CodePoint) (share : KeyShareEntry) : Except Error Step := do
  -- RFC 8446 §7.4.2: the shared secret is ECDH of the own ephemeral key and the client share.
  let secret ← ephemeral config group
  let shared ← (Crypto.sharedSecret group secret share.keyExchange).mapError Error.crypto
  -- §4.2.8: the server share is in the group of the client share it selected.
  let ownShare ← localShare config group
  -- §4.1.3: ServerHello holds only supported versions, with 0x0304, and the key share.
  let extensions ← [Payload.selectedVersion 0x0304, .serverKeyShare ownShare].mapM encodedPayload
  -- §4.1.3: the random, the echo of the client session ID, the selected suite, the extensions.
  --
  -- Appendix A.2: Send ServerHello, at the Initial level of RFC 9001 §4.1.5.
  let (state, sh) ← emit state .initial
    (.serverHello ⟨config.random, hello.legacySessionId, suite, extensions⟩)
  -- Appendix A.2: K_send = handshake, from the transcript through ServerHello (§7.1).
  let state ← negotiate state suite group shared
  -- §4.3.1: EncryptedExtensions follows ServerHello immediately, at the Handshake level.
  --
  -- RFC 7301 §3.1: it names exactly one protocol, libp2p; RFC 9001 §8.2: the transport parameters.
  let extensions ← [Payload.alpn [libp2p],
    .quicTransportParameters config.transportParameters].mapM encodedPayload
  let (state, ee) ← emit state .handshake (.encryptedExtensions extensions)
  -- libp2p tls.md, Handshake Protocol: servers MUST require client authentication.
  --
  -- §4.3.2: so CertificateRequest, with an empty context and the signature algorithms extension.
  let requestExtensions ← [Payload.signatureAlgorithms config.policy.signatureSchemes].mapM
    encodedPayload
  let request : CertificateRequest := ⟨.empty, requestExtensions⟩
  let (state, cr) ← emit { state with request := some request } .handshake
    (.certificateRequest request)
  -- Appendix A.2: Send Certificate + CertificateVerify.
  let (state, certificate) ← emit state .handshake (certificateMessage config)
  -- §4.4.3: the server signs with an algorithm of the client's signature algorithms.
  let offered ← signatures hello.extensions
  let (state, cv) ← sendCertificateVerify config true offered state
  -- Appendix A.2: Send Finished, keyed by the server handshake traffic secret (§4.4).
  let (state, sf) ← sendFinished true state
  -- Appendix A.2: K_send = application, from the transcript through server Finished (§7.1).
  let state ← serverBoundary state
  -- Appendix A.2: WAIT_FLIGHT2 with client authentication, so the next message is Certificate.
  return ⟨{ state with phase := .clientCertificate }, [sh, ee, cr, certificate, cv, sf], none⟩

/-- Process a ClientHello, requiring ALPN before choosing the remaining parameters.

The server ignores SNI, as the Future Extensibility section of libp2p TLS requires. -/
def serverClientHello (config : Config) (state : State) (hello : ClientHello)
    (input : FlightMessage) : Except Error Step := do
  -- libp2p tls.md, ALPN: the server MUST abort if it supports none of the offered protocols.
  --
  -- RFC 7301 §3.2: it SHALL respond with no_application_protocol.
  let protocols ← alpn hello.extensions
  ensure (libp2p ∈ protocols) .noApplicationProtocol
  checkClientHello config hello
  let offeredGroups ← groups hello.extensions
  let keyShares ← shares hello.extensions
  -- §4.1.1: the server independently selects a cipher suite; no overlap is handshake_failure.
  let suite ← select config.policy.cipherSuites hello.cipherSuites
  -- §4.1.2: the server MUST ignore suites it does not support, so only a supported one is selected.
  ensure (supportedSuite suite = true) .handshakeFailure
  -- §4.1.1: it selects an (EC)DHE group; no overlap of supported groups is handshake_failure.
  let group ← select config.policy.groups offeredGroups
  ensure (Crypto.supportedGroup group = true) .handshakeFailure
  match state.retry with
  -- The first ClientHello of the connection.
  | none => pure ()
  -- The second ClientHello, which answers this server's HelloRetryRequest.
  | some retry =>
    checkSecondHello (← saved state.hello) hello retry
    -- §4.1.4: servers MUST negotiate the same cipher suite; EthLib asks the same group too.
    --
    -- §4.1.4 names no alert for the server; EthLib takes illegal_parameter.
    ensure (suite = retry.suite ∧ retry.group = some group) .illegalParameter
  -- Appendix A.2: Recv ClientHello, then RECVD_CH.
  let state ← receive state input
  match keyShares.find? (fun share => share.group == group) with
  -- A share of the selected group: Select parameters, then NEGOTIATED.
  | some share => serverFlight config { state with hello := some hello } hello suite group share
  -- §4.1.1: no share of the selected group, so the server MUST respond with HelloRetryRequest.
  | none =>
    -- §4.1.4: a second HelloRetryRequest MUST make the client abort, so none is sent.
    --
    -- A second ClientHello without that share already fails the check of §4.2.8 above.
    ensure (state.retry.isNone = true) .illegalParameter
    -- §4.1.4: supported versions, then the key share that names the selected group.
    let extensions ← [Payload.selectedVersion 0x0304, .retryKeyShare group].mapM encodedPayload
    let retry : Retry := ⟨suite, some group, none⟩
    -- §4.1.3: HelloRetryRequest is a ServerHello with the special random of a retry.
    --
    -- Appendix A.2: Send HelloRetryRequest, back to START.
    let (state, message) ← emit { state with hello := some hello, retry := some retry }
      .initial (.serverHello ⟨retryRandom, hello.legacySessionId, suite, extensions⟩)
    return ⟨state, [message], none⟩

/-- Read an optional retry group without confusing its payload with ServerHello's key share. -/
def retryGroup (extensions : List Extension) : Except Error (Option CodePoint) := do
  match extension 51 extensions with
  -- A retry without a key share asks for no new share.
  | none => return none
  | some value =>
    -- §4.2.8, KeyShareHelloRetryRequest: `NamedGroup selected_group;`.
    match ← wire (decodePayload .retryKeyShare value) with
    | .retryKeyShare group => return some group
    | _ => throw .decodeError

/-- Validate the cookie's opaque vector before echoing its exact bytes, RFC 8446 §4.2.2. -/
def retryCookie (extensions : List Extension) : Except Error (Option Extension) := do
  match extension 44 extensions with
  | none => return none
  | some value =>
    -- §4.2.2: `opaque cookie<1..2^16-1>;`, and nothing after it.
    let _ ← wire (Wire.exact (Wire.blob 2 1 65535) value.data.data.toList)
    return some value

/-- Respond to one effective retry while retaining the first ClientHello's other fields. -/
def clientRetry (config : Config) (state : State) (hello : ClientHello)
    (server : ServerHello) (input : FlightMessage) : Except Error Step := do
  -- §4.1.4: a second HelloRetryRequest MUST abort the handshake with unexpected_message.
  ensure (state.retry.isNone = true) .unexpectedMessage
  -- §4.1.4: only extensions the client offered, apart from the cookie.
  checkExtensions .retry (some hello.extensions) server.extensions
  let group ← retryGroup server.extensions
  let cookie ← retryCookie server.extensions
  -- §4.1.4: a retry that would not change the ClientHello is illegal_parameter.
  ensure (group.isSome = true ∨ cookie.isSome = true) .illegalParameter
  let extensions ← match group with
    -- §4.1.2: without a key share in the retry, the shares stay as sent.
    | none => pure hello.extensions
    | some group => do
      let offeredGroups ← groups hello.extensions
      let keyShares ← shares hello.extensions
      -- §4.2.8: the group was among the supported groups, and had no share, else illegal_parameter.
      ensure (group ∈ offeredGroups ∧ ¬ group ∈ keyShares.map (·.group)) .illegalParameter
      -- §4.2.8: the key share is replaced with one holding a single entry for that group.
      let share ← localShare config group
      let replacement ← encodedPayload (.clientKeyShare [share])
      pure (hello.extensions.map fun value => if value.kind = 51 then replacement else value)
  -- §4.1.2: early data is removed; a cookie of the first ClientHello goes too.
  let extensions := extensions.filter (fun value => value.kind != 42 && value.kind != 44)
  -- §4.2.2: the cookie of the retry, copied as received.
  --
  -- The client offers no pre-shared key, so no extension has to stay last.
  let extensions := extensions ++ cookie.toList
  let hello := { hello with extensions }
  -- §4.4.1: the transcript replaces ClientHello1 with its hash, then takes the retry.
  let state ← receive state input
  let retry : Retry := ⟨server.cipherSuite, group, cookie⟩
  -- Appendix A.1: Recv HelloRetryRequest, back to START, then Send ClientHello and WAIT_SH.
  let (state, message) ← emit { state with hello := some hello, retry := some retry }
    .initial (.clientHello hello)
  return ⟨state, [message], none⟩

/-- Check ServerHello or HelloRetryRequest against the client offer, RFC 8446 §§4.1.3 and 4.1.4. -/
def clientServerHello (config : Config) (state : State) (server : ServerHello)
    (input : FlightMessage) : Except Error Step := do
  -- §4.2.1: the client checks the selected version before the rest of either message.
  selectedVersion server.extensions
  let hello ← saved state.hello
  -- §4.1.3: an echo of another session ID, or a suite that was not offered, is illegal_parameter.
  ensure (server.legacySessionIdEcho = hello.legacySessionId ∧
    server.cipherSuite ∈ hello.cipherSuites) .illegalParameter
  -- EthLib's check: the suite is also in the policy, with a SHA-256 transcript here.
  ensure (server.cipherSuite ∈ config.policy.cipherSuites ∧
    supportedSuite server.cipherSuite = true) .illegalParameter
  -- §4.1.3 examines the random first; the checks common to both forms (§4.1.4) run before it.
  --
  -- A random equal to that of a retry makes this message a HelloRetryRequest.
  if server.random = retryRandom then
    clientRetry config state hello server input
  else
    -- §4.2: only extensions the client offered, and only those that ServerHello may carry.
    checkExtensions .serverHello (some hello.extensions) server.extensions
    -- The client never offers a PSK, so a selected PSK identity is unsupported.
    ensure (extension 41 server.extensions = none) (.unsupportedExtension 41)
    -- §4.2.8, KeyShareServerHello: `KeyShareEntry server_share;`.
    let share ← match ← payload .serverKeyShare server.extensions with
      | .serverKeyShare share => pure share
      | _ => throw .decodeError
    let offered ← shares hello.extensions
    -- §4.2.8: the server share is in the group of a client share, else illegal_parameter.
    --
    -- EthLib's check: that group is also in the policy.
    ensure (share.group ∈ offered.map (·.group) ∧ share.group ∈ config.policy.groups)
      .illegalParameter
    match state.retry with
    | none => pure ()
    -- §4.1.4: the suite of ServerHello is the one of the retry, else illegal_parameter.
    --
    -- §4.2.8: after a retry with a key share, the group is the one it selected.
    | some retry =>
      ensure (server.cipherSuite = retry.suite ∧
        (retry.group = none ∨ retry.group = some share.group)) .illegalParameter
    -- §7.4.2: the shared secret is ECDH of the own ephemeral key and the server share.
    let secret ← ephemeral config share.group
    let shared ← (Crypto.sharedSecret share.group secret share.keyExchange).mapError
      Error.crypto
    -- Appendix A.1: Recv ServerHello, then K_recv = handshake (§7.1).
    let state ← receive state input
    let state ← negotiate state server.cipherSuite share.group shared
    -- Appendix A.1: WAIT_EE.
    return ⟨{ state with phase := .encryptedExtensions }, [], none⟩

/-- Check EncryptedExtensions and the libp2p ALPN choice, RFC 8446 §4.3.1 and RFC 7301 §3.1. -/
def clientEncryptedExtensions (state : State) (extensions : List Extension)
    (input : FlightMessage) : Except Error Step := do
  let hello ← saved state.hello
  -- §4.3.1: a forbidden extension is illegal_parameter; §4.2: each answers one of ClientHello.
  checkExtensions .encryptedExtensions (some hello.extensions) extensions
  -- RFC 9001 §8.1: without ALPN, the client closes with no_application_protocol.
  let protocols ← alpn extensions
  -- RFC 7301 §3.1: the list holds exactly one name, and libp2p tls.md fixes it to libp2p.
  --
  -- RFC 9001 §8.1: any other selection is the error 0x0178.
  ensure (protocols = [libp2p]) .noApplicationProtocol
  -- RFC 9001 §8.2: EncryptedExtensions without QUIC transport parameters is missing_extension.
  let _ ← payload .quicTransportParameters extensions
  -- Appendix A.1: Recv EncryptedExtensions, then WAIT_CERT_CR.
  let state ← receive state input
  -- libp2p tls.md, Handshake Protocol: servers MUST require client authentication.
  --
  -- So only CertificateRequest may follow.
  --
  -- Appendix A.1 also lets WAIT_CERT_CR take Certificate; EthLib rejects it.
  return ⟨{ state with phase := .certificateRequest }, [], none⟩

/-- Require handshake client authentication with an empty request context, RFC 8446 §4.3.2. -/
def clientCertificateRequest (config : Config) (state : State) (request : CertificateRequest)
    (input : FlightMessage) : Except Error Step := do
  -- §4.2: each recognized extension is one that CertificateRequest may carry.
  checkExtensions .certificateRequest none request.extensions
  -- §4.3.2: the context SHALL be zero length outside post-handshake authentication.
  --
  -- §4.3.2 names no alert; EthLib takes illegal_parameter.
  ensure (request.context = ByteArray.empty) .illegalParameter
  -- §4.3.2: the signature algorithms extension MUST be specified.
  let offered ← signatures request.extensions
  -- §4.4.3: the client will sign with one of them.
  --
  -- EthLib checks the overlap here, before the server Certificate; none is handshake_failure.
  let _ ← select config.policy.signatureSchemes offered
  -- Appendix A.1: Recv CertificateRequest, then WAIT_CERT.
  let state ← receive state input
  return ⟨{ state with phase := .serverCertificate, request := some request }, [], none⟩

/-- Verify server Finished, then send the client's Certificate, CertificateVerify and Finished. -/
def clientFinished (config : Config) (expected : ByteArray) (state : State)
    (value : ByteArray) (input : FlightMessage) : Except Error Step := do
  -- §4.4.4: the server Finished, over the transcript through server CertificateVerify.
  checkFinished true state value
  -- Appendix A.1: Recv Finished at WAIT_FINISHED; RFC 9001 §8.3 drops EndOfEarlyData.
  let state ← receive state input
  -- §7.1: the application traffic secrets take ClientHello...server Finished.
  let state ← serverBoundary state
  -- §4.4.3: the client signs with an algorithm of CertificateRequest.
  let request ← saved state.request
  let offered ← signatures request.extensions
  -- Appendix A.1: Send Certificate + CertificateVerify, at K_send = handshake.
  let (state, certificate) ← emit state .handshake (certificateMessage config)
  let (state, cv) ← sendCertificateVerify config false offered state
  -- Appendix A.1: Send Finished, then CONNECTED.
  let (state, finished) ← sendFinished false state
  complete config (some expected) state [certificate, cv, finished]

/-- Accept a well-formed ticket without resuming or extending the main handshake transcript.

RFC 9001 §§4.5 and 4.6.1 allow tickets and constrain their early_data sentinel. -/
def receiveTicket (input : FlightMessage) : Except Error Unit := do
  -- RFC 9001 §4.5 and Figure 5: tickets travel after the handshake, so at the 1-RTT level.
  checkLevel .application input
  -- RFC 8446 §4: one handshake message, its type and its body.
  let (kind, body) ← wire (Wire.exact readFrame input.data.data.toList)
  -- RFC 9001 §4.4: a post-handshake CertificateRequest (13) is a PROTOCOL_VIOLATION.
  if kind = 13 then throw .protocolViolation
  -- Only NewSessionTicket (4) is accepted here.
  --
  -- RFC 9001 §6: a TLS KeyUpdate is the error 0x010a, unexpected_message.
  ensure (kind = 4) .unexpectedMessage
  let reader : Wire.Reader (List Extension) := do
    -- §4.6.1: `uint32 ticket_lifetime;` and `uint32 ticket_age_add;`.
    let _ ← uint 4
    let _ ← uint 4
    -- `opaque ticket_nonce<0..255>;` and `opaque ticket<1..2^16-1>;`.
    let _ ← blob 1 0 255
    let _ ← blob 2 1 65535
    -- RFC 9846 §4.7.1: `Extension extensions<0..2^16-1>;`.
    --
    -- RFC 8446 §4.6.1 printed 2^16-2, a calculation error that RFC 9846 §1.2 corrects.
    readExtensions 0
  let extensions ← wire (Wire.exact reader body)
  -- §4.2: each recognized extension is one that NewSessionTicket may carry.
  checkExtensions .newSessionTicket none extensions
  match extension 42 extensions with
  | none => pure ()
  -- RFC 9001 §4.6.1: an early data value other than 0xffffffff is a PROTOCOL_VIOLATION.
  | some value => ensure (value.data = [255, 255, 255, 255].toByteArray) .protocolViolation

/-- Advance the dialer's certificate handshake by one complete message.

An authenticated result follows verification of server Finished and transmission of client Finished.

Completed clients accept tickets, RFC 9001 §4.5.

They reject post-handshake authentication and TLS KeyUpdate, RFC 9001 §§4.4 and 6. -/
def clientStep (config : Config) (expected : ByteArray) (state : State)
    (input : FlightMessage) : Except Error Step := do
  match state.phase with
  -- Appendix A.1, WAIT_SH: ServerHello or HelloRetryRequest, at the Initial level.
  | .serverHello =>
    match ← readMessage .initial input with
    | .serverHello server => clientServerHello config state server input
    -- §6.2: in each state, any other message is unexpected_message.
    | _ => throw .unexpectedMessage
  -- WAIT_EE: EncryptedExtensions, at the Handshake level from here on.
  | .encryptedExtensions =>
    match ← readMessage .handshake input with
    | .encryptedExtensions extensions => clientEncryptedExtensions state extensions input
    | _ => throw .unexpectedMessage
  -- WAIT_CERT_CR, where this client takes only CertificateRequest.
  | .certificateRequest =>
    match ← readMessage .handshake input with
    | .certificateRequest request => clientCertificateRequest config state request input
    | _ => throw .unexpectedMessage
  -- WAIT_CERT: the server Certificate.
  | .serverCertificate =>
    match ← readMessage .handshake input with
    | .certificate certificate =>
      -- §4.4.2: its extensions correspond to ones from ClientHello.
      let hello ← saved state.hello
      let state ← receiveCertificate config (some expected) hello.extensions state certificate
      -- Recv Certificate, then WAIT_CV.
      let state ← receive state input
      return ⟨{ state with phase := .serverCertificateVerify }, [], none⟩
    | _ => throw .unexpectedMessage
  -- WAIT_CV: the server CertificateVerify.
  | .serverCertificateVerify =>
    match ← readMessage .handshake input with
    | .certificateVerify algorithm signature =>
      -- §4.4.3: the server signs with an algorithm of the client's signature algorithms.
      let hello ← saved state.hello
      let offered ← signatures hello.extensions
      -- §4.4.3: the signature covers the transcript through Certificate, so it is checked first.
      checkCertificateVerify config (some expected) true offered state algorithm signature
      -- Recv CertificateVerify, then WAIT_FINISHED.
      let state ← receive state input
      return ⟨{ state with phase := .serverFinished }, [], none⟩
    | _ => throw .unexpectedMessage
  -- WAIT_FINISHED: server Finished, then the second flight of the client.
  | .serverFinished =>
    match ← readMessage .handshake input with
    | .finished value => clientFinished config expected state value input
    | _ => throw .unexpectedMessage
  -- CONNECTED: RFC 9001 §4.5 carries NewSessionTicket after the handshake.
  | .complete =>
    receiveTicket input
    return ⟨state, [], none⟩
  -- A phase of the server is not a state of the client.
  | _ => throw .unexpectedMessage

/-- Advance the listener's certificate handshake by one complete message.

The listener requires the client's certificate and verifies its signature and Finished.

Its authenticated result follows both Finished messages, RFC 9001 §4.1.1. -/
def serverStep (config : Config) (state : State) (input : FlightMessage) : Except Error Step := do
  match state.phase with
  -- Appendix A.2, START: ClientHello, at the Initial level.
  | .clientHello =>
    match ← readMessage .initial input with
    | .clientHello hello => serverClientHello config state hello input
    -- §6.2: in each state, any other message is unexpected_message.
    | _ => throw .unexpectedMessage
  -- WAIT_FLIGHT2 with client authentication, then WAIT_CERT: the client Certificate.
  | .clientCertificate =>
    match ← readMessage .handshake input with
    | .certificate certificate =>
      -- Check the required client chain before reading any saved request state.
      --
      -- libp2p tls.md, Handshake Protocol: no client certificate fails, as §4.4.2.4 allows.
      ensure (certificate.entries ≠ []) .certificateRequired
      -- §4.4.2: its extensions correspond to ones in CertificateRequest.
      let request ← saved state.request
      let state ← receiveCertificate config none request.extensions state certificate
      -- Recv Certificate, then WAIT_CV.
      let state ← receive state input
      return ⟨{ state with phase := .clientCertificateVerify }, [], none⟩
    | _ => throw .unexpectedMessage
  -- WAIT_CV: the client CertificateVerify.
  | .clientCertificateVerify =>
    match ← readMessage .handshake input with
    | .certificateVerify algorithm signature =>
      -- §4.4.3: the client signs with an algorithm of CertificateRequest.
      let request ← saved state.request
      let offered ← signatures request.extensions
      checkCertificateVerify config none false offered state algorithm signature
      -- Recv CertificateVerify, then WAIT_FINISHED.
      let state ← receive state input
      return ⟨{ state with phase := .clientFinished }, [], none⟩
    | _ => throw .unexpectedMessage
  -- WAIT_FINISHED: client Finished.
  | .clientFinished =>
    match ← readMessage .handshake input with
    | .finished value =>
      -- §4.4.4: the client Finished, over the transcript through client CertificateVerify.
      checkFinished false state value
      -- Recv Finished, then K_recv = application and CONNECTED.
      let state ← receive state input
      complete config none state []
    | _ => throw .unexpectedMessage
  -- CONNECTED.
  | .complete =>
    -- Data at an earlier level is a protocol violation; nothing else follows completion here.
    checkLevel .application input
    throw .unexpectedMessage
  -- A phase of the client is not a state of the server.
  | _ => throw .unexpectedMessage

end EthLib.Networking.Quic.Tls.Handshake
