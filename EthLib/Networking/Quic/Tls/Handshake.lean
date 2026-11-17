module

public import EthLib.Networking.Quic.Tls
public import EthLib.Networking.Quic.Tls.Crypto
public import EthLib.Networking.Quic.Tls.Extensions
public import EthLib.Networking.Quic.Tls.Transcript
public import EthLib.Networking.Quic.Keys

/-!
# The certificate handshake of libp2p QUIC

The pure steps follow [RFC 8446 §4][tls] and [RFC 9001 §4][quic].

Peer authentication and ALPN follow [libp2p TLS at c750236][libp2p].

Every caller supplies its algorithm policy, credentials and ephemeral keys.

There is no default profile, pre-shared-key handshake, resumption or 0-RTT.

One input is one complete handshake message after CRYPTO reassembly.

Its encryption level is checked here; packet protection and reassembly belong to QUIC.

The caller keeps the same configuration throughout one handshake and discards state after an error.

Ephemeral keys must be fresh and secret, and no function claims constant-time execution.

CertificateVerify signatures use the deterministic nonce of RFC 6979, so no caller supplies one.

[tls]: https://www.rfc-editor.org/rfc/rfc8446#section-4
[quic]: https://www.rfc-editor.org/rfc/rfc9001#section-4
[libp2p]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md
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

/-- The QUIC connection error, RFC 9000 §20.1; a TLS alert maps to 0x100 + alert, RFC 9001 §4.8.

A bad peer key share or a degenerate shared secret is illegal_parameter, RFC 8446 §6.2.

Every other cryptographic failure is local, so it is internal_error. -/
def Error.code : Error → UInt32
  | .unexpectedMessage => 0x10a
  | .illegalParameter => 0x12f
  | .missingExtension _ => 0x16d
  | .unsupportedExtension _ => 0x16e
  | .handshakeFailure => 0x128
  | .protocolVersion => 0x146
  | .noApplicationProtocol => 0x178
  | .certificateRequired => 0x174
  | .decodeError => 0x132
  | .decryptError => 0x133
  | .protocolViolation => 0x0a
  | .configuration => 0x150
  | .certificate _ => 0x12a
  | .crypto .keyShare | .crypto .sharedSecret => 0x12f
  | .crypto _ => 0x150

/-- The CRYPTO encryption level of a handshake message, RFC 9001 §4. -/
inductive Level where
  | initial
  | handshake
  | application
  deriving Repr, DecidableEq

/-- The order of the encryption levels, from Initial to 1-RTT, RFC 9001 §4.1.3. -/
def Level.rank : Level → Nat
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
  suite.val == 0x1301 || suite.val == 0x1303

/-- Separate an unexpected message type from malformed data, RFC 8446 §§4 and 6.2. -/
def wire {α : Type} (value : Except Wire.Error α) : Except Error α :=
  value.mapError fun
    | .messageType _ | .retry => .unexpectedMessage
    | .constant | .duplicateExtension _ => .illegalParameter
    | _ => .decodeError

/-- A value whose absence means that a caller supplied an inconsistent state. -/
def saved {α : Type} : Option α → Except Error α
  | some value => .ok value
  | none => .error .configuration

/-- The first extension of a type; the message codec rejects duplicate types. -/
def extension (kind : CodePoint) (extensions : List Extension) : Option Extension :=
  extensions.find? (fun e => e.kind == kind)

/-- Require an optional field with the error appropriate to its protocol context. -/
def required {α : Type} (error : Error) : Option α → Except Error α
  | some value => .ok value
  | none => .error error

/-- Read a required extension in its message-specific form, RFC 8446 §4.2. -/
def payload (form : PayloadForm) (extensions : List Extension) : Except Error Payload := do
  let value ← required (.missingExtension form.type) (extension form.type extensions)
  wire (decodePayload form value)

/-- Read an ALPN list without selecting a protocol, RFC 7301 §3.1. -/
def alpn (extensions : List Extension) : Except Error (List ByteArray) := do
  let value ← required .noApplicationProtocol (extension PayloadForm.alpn.type extensions)
  match ← wire (decodePayload .alpn value) with
  | .alpn protocols => return protocols
  | _ => throw .decodeError

/-- Read the offered groups, RFC 8446 §4.2.7. -/
def groups (extensions : List Extension) : Except Error (List CodePoint) := do
  match ← payload .supportedGroups extensions with
  | .supportedGroups values => return values
  | _ => throw .decodeError

/-- Read offered signature schemes, RFC 8446 §4.2.3. -/
def signatures (extensions : List Extension) : Except Error (List CodePoint) := do
  match ← payload .signatureAlgorithms extensions with
  | .signatureAlgorithms values => return values
  | _ => throw .decodeError

/-- Read ClientHello's shares, RFC 8446 §4.2.8. -/
def shares (extensions : List Extension) : Except Error (List KeyShareEntry) := do
  match ← payload .clientKeyShare extensions with
  | .clientKeyShare values => return values
  | _ => throw .decodeError

/-- Select the first local preference also offered by the peer, RFC 8446 §4.1.1. -/
def select (preferences offered : List CodePoint) : Except Error CodePoint :=
  required .handshakeFailure (preferences.find? (fun value => value ∈ offered))

/-- Find the local secret for a selected group without substituting another key. -/
def ephemeral (config : Config) (group : CodePoint) : Except Error (Vector UInt8 32) := do
  let key ← required .configuration (config.ephemeralKeys.find? (fun key => key.group == group))
  return key.secret

/-- Enforce digitalSignature when KeyUsage is present, RFC 8446 §4.4.2.2 and RFC 5280 §4.2.1.3. -/
def checkSigningUsage (certificate : Libp2p.Tls.Certificate) : Except Error Unit :=
  certificate.extensions.forM fun value => do
    if value.oid = (⟨#[0x55, 0x1d, 0x0f]⟩ : ByteArray) then
      let bits ← (EthLib.Serialization.Der.exact 3 value.value).mapError
        (fun error => Error.certificate (.der error))
      let _ ← (EthLib.Serialization.Der.validBits bits.content).mapError
        (fun error => Error.certificate (.der error))
      match bits.content.toList with
      | _ :: first :: _ => ensure (first.toNat / 128 = 1) (.certificate .publicKey)
      | _ => throw (.certificate .publicKey)
    else pure ()

/-- Validate the explicit implementation choices without providing a default profile. -/
def validateConfig (config : Config) : Except Error Unit := do
  ensure (config.policy.cipherSuites ≠ [] ∧ config.policy.groups ≠ [] ∧
    config.policy.signatureSchemes ≠ []) .configuration
  ensure (config.policy.cipherSuites.all supportedSuite ∧
    config.policy.groups.all Crypto.supportedGroup ∧
    config.policy.signatureSchemes.all Crypto.supportedSignatureScheme) .configuration
  ensure (config.initialShares.Sublist config.policy.groups ∧
    config.policy.groups.Nodup ∧ config.initialShares.Nodup ∧
    (config.ephemeralKeys.map (·.group)).Nodup) .configuration
  config.policy.groups.forM fun group => do
    let _ ← ephemeral config group
    pure ()
  let peer ← (Libp2p.Tls.authenticate config.policy.certificates config.now
    config.certificates).mapError Error.certificate
  -- libp2p permits a receiver to tolerate unique IDs, but a sender must omit them.
  ensure (peer.certificate.issuerUniqueId = false ∧ peer.certificate.subjectUniqueId = false)
    .configuration
  checkSigningUsage peer.certificate
  ensure (Crypto.publicKeyMatches config.signingKey peer.certificate.spki = true) .configuration

/-- Build a typed payload's extension, checking its presentation bounds. -/
def encodedPayload (value : Payload) : Except Error Extension := wire (encodePayload value)

/-- Encode a complete outgoing handshake message, then retain those exact transcript bytes. -/
def emit (state : State) (level : Level) (message : Message) :
    Except Error (State × FlightMessage) := do
  let data ← wire (encode 32 message)
  let transcript ← wire (state.transcript.append data)
  return ({ state with transcript }, ⟨level, data⟩)

/-- Preserve an accepted incoming message byte for byte, RFC 8446 §4.4.1. -/
def receive (state : State) (input : FlightMessage) : Except Error State := do
  return { state with transcript := ← wire (state.transcript.append input.data) }

/-- Check that a message arrived at its required QUIC encryption level, RFC 9001 §4.

Data at an earlier level than expected is a PROTOCOL_VIOLATION, RFC 9001 §4.1.3.

The caller buffers data at a later level, so receiving it here is an unexpected message. -/
def checkLevel (expected : Level) (input : FlightMessage) : Except Error Unit := do
  ensure (expected.rank ≤ input.level.rank) .protocolViolation
  ensure (input.level = expected) .unexpectedMessage

/-- Decode one complete message at its required QUIC encryption level, RFC 9001 §4. -/
def readMessage (expected : Level) (input : FlightMessage) : Except Error Message := do
  checkLevel expected input
  wire (Wire.exact (decodeList 32) input.data.data.toList)

/-- Empty saved inputs before either endpoint receives a message. -/
def initialState (phase : Phase) : State := ⟨phase, {}, none, none, none, [], none⟩

/-- Build a key-share entry from the configured secret, RFC 8446 §4.2.8. -/
def localShare (config : Config) (group : CodePoint) : Except Error KeyShareEntry := do
  let secret ← ephemeral config group
  let bytes ← (Crypto.keyShare group secret).mapError Error.crypto
  return ⟨group, bytes⟩

/-- Generate a TLS 1.3-only ClientHello without SNI, libp2p TLS Future Extensibility. -/
def makeClientHello (config : Config) : Except Error ClientHello := do
  let keyShares ← config.initialShares.mapM (localShare config)
  let extensions ← [Payload.supportedVersions [0x0304],
    .supportedGroups config.policy.groups, .signatureAlgorithms config.policy.signatureSchemes,
    .clientKeyShare keyShares, .alpn [libp2p],
    .quicTransportParameters config.transportParameters].mapM encodedPayload
  return ⟨config.random, .empty, config.policy.cipherSuites, extensions⟩

/-- Send ClientHello and wait for ServerHello or one retry, RFC 8446 §4.1.2. -/
def clientStart (config : Config) : Except Error Step := do
  validateConfig config
  let hello ← makeClientHello config
  let (state, message) ← emit { initialState .serverHello with hello := some hello }
    .initial (.clientHello hello)
  return ⟨state, [message], none⟩

/-- Wait for ClientHello with an explicit local policy and credentials. -/
def serverStart (config : Config) : Except Error State := do
  validateConfig config
  ensure (config.random ≠ retryRandom) .configuration
  return initialState .clientHello

/-- The message contexts of RFC 8446 §4.2 and RFC 9001 §8.2. -/
inductive Context where
  | clientHello | serverHello | retry | encryptedExtensions | certificateRequest | certificate
  | newSessionTicket
  deriving DecidableEq

/-- Placement of every extension recognized here, with unknown types left uninterpreted. -/
def allowedExtension (context : Context) (kind : CodePoint) : Bool :=
  let contexts := match kind.val with
    | 0 | 1 | 10 | 14 | 15 | 16 | 19 | 20 | 57 =>
      some [Context.clientHello, .encryptedExtensions]
    | 5 | 18 => some [.clientHello, .certificateRequest, .certificate]
    | 13 | 47 | 50 => some [.clientHello, .certificateRequest]
    | 21 | 45 | 49 => some [.clientHello]
    | 41 => some [.clientHello, .serverHello]
    | 42 => some [.clientHello, .encryptedExtensions, .newSessionTicket]
    | 43 | 51 => some [.clientHello, .serverHello, .retry]
    | 44 => some [.clientHello, .retry]
    | 48 => some [.certificateRequest]
    | _ => none
  match contexts with
  | none => true
  | some contexts => context ∈ contexts

/-- Validate placement and, for a response, the corresponding request, RFC 8446 §4.2. -/
def checkExtensions (context : Context) (offered : Option (List Extension))
    (extensions : List Extension) : Except Error Unit :=
  extensions.forM fun value => do
    ensure (allowedExtension context value.kind = true) .illegalParameter
    match offered with
    | none => pure ()
    | some offered =>
      ensure ((context = .retry ∧ value.kind = 44) ∨
        (offered.any (fun request => request.kind == value.kind)) = true)
        (.unsupportedExtension value.kind)

/-- Read PSK identities while checking offer framing and binder count, RFC 8446 §4.2.11. -/
def pskIdentities (extensions : List Extension) : Except Error (List ByteArray) := do
  match extension 41 extensions with
  | none => return []
  | some psk =>
    let identity : Wire.Reader ByteArray := do
      let name ← blob 2 1 65535
      let _ ← uint 4
      return name.toByteArray
    let reader : Wire.Reader (List ByteArray) := do
      let identities ← items 2 7 65535 identity
      let binders ← items 2 33 65535 (blob 1 32 255)
      require (identities.length = binders.length) .constant
      return identities
    wire (Wire.exact reader psk.data.data.toList)

/-- Check the PSK offer's framing while declining to select it, RFC 8446 §§4.2.9 and 4.2.11. -/
def checkPskOffer (extensions : List Extension) : Except Error Unit := do
  match extension 45 extensions with
  | none => pure ()
  | some modes =>
    let _ ← wire (Wire.exact (Wire.blob 1 1 255) modes.data.data.toList)
    pure ()
  match extension 41 extensions with
  | none => ensure (extension 42 extensions = none) .illegalParameter
  | some psk =>
    ensure (extensions.getLast? = some psk) .illegalParameter
    let _ ← required (.missingExtension 45) (extension 45 extensions)
    let _ ← pskIdentities extensions
    match extension 42 extensions with
    | none => pure ()
    | some early => ensure (early.data = ByteArray.empty) .decodeError

/-- Validate the client offer; libp2p servers ignore SNI, including its opaque contents.

Duplicate or unordered key shares are rejected under RFC 8446 §4.2.8's server MAY.

A PSK offer is never selected, and early data is never accepted. -/
def checkClientHello (config : Config) (hello : ClientHello) : Except Error Unit := do
  checkExtensions .clientHello none hello.extensions
  ensure (config.policy.rejectLegacySessionId = false ∨ hello.legacySessionId = ByteArray.empty)
    .protocolViolation
  -- Appendix D.2: a ClientHello without supported_versions offers only TLS 1.2 or earlier.
  ensure (extension PayloadForm.supportedVersions.type hello.extensions).isSome .protocolVersion
  match ← payload .supportedVersions hello.extensions with
  | .supportedVersions versions => ensure ((0x0304 : CodePoint) ∈ versions) .protocolVersion
  | _ => throw .decodeError
  let offeredGroups ← groups hello.extensions
  let keyShares ← shares hello.extensions
  ensure ((keyShares.map (·.group)).Sublist offeredGroups ∧
    (keyShares.map (·.group)).Nodup) .illegalParameter
  let _ ← signatures hello.extensions
  let _ ← payload .quicTransportParameters hello.extensions
  checkPskOffer hello.extensions

/-- The parts of ClientHello which a non-PSK retry must preserve, RFC 8446 §4.1.2. -/
def stableHello (hello : ClientHello) : ClientHello :=
  { hello with extensions := hello.extensions.filter fun value =>
      value.kind != 51 && value.kind != 44 && value.kind != 42 && value.kind != 21 &&
      value.kind != 41 }

/-- Check the second ClientHello against the retry and first offer, RFC 8446 §§4.1.2 and 4.1.4. -/
def checkSecondHello (first second : ClientHello) (retry : Retry) : Except Error Unit := do
  ensure (stableHello first = stableHello second) .illegalParameter
  ensure (extension 42 second.extensions = none) .illegalParameter
  ensure (extension 44 second.extensions = retry.cookie) .illegalParameter
  let originalIdentities ← pskIdentities first.extensions
  let updatedIdentities ← pskIdentities second.extensions
  ensure (updatedIdentities.Sublist originalIdentities) .illegalParameter
  match retry.group with
  | some group =>
    let keyShares ← shares second.extensions
    ensure (keyShares.map (·.group) = [group]) .illegalParameter
  | none =>
    ensure (extension 51 first.extensions = extension 51 second.extensions) .illegalParameter

/-- Read and validate the selected TLS version before other ServerHello checks, RFC 8446 §4.2.1.

A ServerHello without the extension selects TLS 1.2, a protocol_version error by Appendix D.1. -/
def selectedVersion (extensions : List Extension) : Except Error Unit := do
  ensure (extension PayloadForm.selectedVersion.type extensions).isSome .protocolVersion
  match ← payload .selectedVersion extensions with
  | .selectedVersion version => ensure (version = 0x0304) .illegalParameter
  | _ => throw .decodeError

/-- The peer's certificate, authenticated under the explicit libp2p policy.

For a dialer the expected peer ID is checked as well. -/
def authenticate (config : Config) (expected : Option ByteArray) (chain : List ByteArray) :
    Except Error Libp2p.Tls.AuthenticatedPeer := do
  let peer ← (match expected with
    | none => Libp2p.Tls.authenticate config.policy.certificates config.now chain
    | some id => Libp2p.Tls.authenticatePeer config.policy.certificates config.now id chain)
      |>.mapError Error.certificate
  checkSigningUsage peer.certificate
  return peer

/-- Recompute the schedule from the saved inputs and check the saved certificate chain again.

The peer's proof of key possession comes only from the CertificateVerify step. -/
def complete (config : Config) (expected : Option ByteArray) (state : State)
    (output : List FlightMessage) : Except Error Step := do
  let negotiated ← saved state.negotiated
  let secrets ← (keySchedule (packBytes negotiated.sharedSecret) negotiated.helloTranscript
    negotiated.serverTranscript).mapError fun _ => Error.configuration
  let peer ← authenticate config expected state.peerChain
  let negotiated := { negotiated with secrets }
  return ⟨{ state with phase := .complete, negotiated := some negotiated }, output,
    some ⟨peer.peerId, state.peerChain, negotiated⟩⟩

/-- Start handshake traffic derivation at the exact ServerHello transcript boundary. -/
def negotiate (state : State) (suite group : CodePoint) (shared : Vector UInt8 32) :
    Except Error State := do
  let hello := state.transcript.bytes
  let secrets ← (keySchedule (packBytes shared) hello .empty).mapError fun _ => Error.configuration
  return { state with negotiated := some ⟨suite, group, shared, hello, .empty, secrets⟩ }

/-- Retain the transcript through server Finished before deriving application traffic secrets. -/
def serverBoundary (state : State) : Except Error State := do
  let negotiated ← saved state.negotiated
  let server := state.transcript.bytes
  let secrets ← (keySchedule (packBytes negotiated.sharedSecret)
    negotiated.helloTranscript server).mapError fun _ => Error.configuration
  return { state with negotiated := some { negotiated with serverTranscript := server, secrets } }

/-- Encode the configured chain with an empty request context, RFC 8446 §4.4.2. -/
def certificateMessage (config : Config) : Message :=
  .certificate ⟨.empty, config.certificates.map fun data => ⟨data, []⟩⟩

/-- Sign the transcript through Certificate, with the sender's role, RFC 8446 §4.4.3.

The signature is a function of the signing key and the signed content alone. -/
def sendCertificateVerify (config : Config) (server : Bool) (offered : List CodePoint)
    (state : State) : Except Error (State × FlightMessage) := do
  let algorithm ← select config.policy.signatureSchemes offered
  let content := certificateVerifyInput server state.transcript.hash
  let signature ← (Crypto.signCertificateVerify algorithm config.signingKey content).mapError
    Error.crypto
  emit state .handshake (.certificateVerify algorithm signature)

/-- Compute Finished before including its own encoding in the transcript, RFC 8446 §4.4.4. -/
def sendFinished (server : Bool) (state : State) : Except Error (State × FlightMessage) := do
  let negotiated ← saved state.negotiated
  let secret := if server then negotiated.secrets.serverHandshake
    else negotiated.secrets.clientHandshake
  let value ← (finished secret state.transcript.bytes).mapError
    fun _ => Error.configuration
  emit state .handshake (.finished (packBytes value))

/-- Verify the peer's CertificateVerify before appending it to the transcript, RFC 8446 §4.4.3. -/
def checkCertificateVerify (config : Config) (expected : Option ByteArray) (server : Bool)
    (offered : List CodePoint) (state : State) (algorithm : CodePoint)
    (signature : ByteArray) : Except Error Unit := do
  ensure (algorithm ∈ offered ∧ algorithm ∈ config.policy.signatureSchemes) .illegalParameter
  let peer ← authenticate config expected state.peerChain
  let content := certificateVerifyInput server state.transcript.hash
  ensure (Crypto.verifyCertificateVerify algorithm peer.certificate.spki content
    signature = true) .decryptError

/-- Verify Finished against the saved transcript, RFC 8446 §4.4.4. -/
def checkFinished (server : Bool) (state : State) (value : ByteArray) : Except Error Unit := do
  let negotiated ← saved state.negotiated
  let secret := if server then negotiated.secrets.serverHandshake
    else negotiated.secrets.clientHandshake
  let expected ← (finished secret state.transcript.bytes).mapError
    fun _ => Error.configuration
  ensure (value = packBytes expected) .decryptError

/-- Validate a certificate message and save its exact chain for later signature checks. -/
def receiveCertificate (config : Config) (expected : Option ByteArray) (offered : List Extension)
    (state : State) (certificate : CertificateMessage) : Except Error State := do
  let emptyError := if expected.isSome then Error.decodeError else .certificateRequired
  ensure (certificate.entries ≠ []) emptyError
  ensure (certificate.context = ByteArray.empty) .illegalParameter
  certificate.entries.forM fun entry => checkExtensions .certificate (some offered) entry.extensions
  let chain := certificate.entries.map (·.data)
  let _ ← authenticate config expected chain
  return { state with peerChain := chain }

/-- The server flight after a usable client share, RFC 8446 §2. -/
def serverFlight (config : Config) (state : State) (hello : ClientHello)
    (suite group : CodePoint) (share : KeyShareEntry) : Except Error Step := do
  let secret ← ephemeral config group
  let shared ← (Crypto.sharedSecret group secret share.keyExchange).mapError Error.crypto
  let ownShare ← localShare config group
  let extensions ← [Payload.selectedVersion 0x0304, .serverKeyShare ownShare].mapM encodedPayload
  let (state, sh) ← emit state .initial
    (.serverHello ⟨config.random, hello.legacySessionId, suite, extensions⟩)
  let state ← negotiate state suite group shared
  let extensions ← [Payload.alpn [libp2p],
    .quicTransportParameters config.transportParameters].mapM encodedPayload
  let (state, ee) ← emit state .handshake (.encryptedExtensions extensions)
  let requestExtensions ← [Payload.signatureAlgorithms config.policy.signatureSchemes].mapM
    encodedPayload
  let request : CertificateRequest := ⟨.empty, requestExtensions⟩
  let (state, cr) ← emit { state with request := some request } .handshake
    (.certificateRequest request)
  let (state, certificate) ← emit state .handshake (certificateMessage config)
  let offered ← signatures hello.extensions
  let (state, cv) ← sendCertificateVerify config true offered state
  let (state, sf) ← sendFinished true state
  let state ← serverBoundary state
  return ⟨{ state with phase := .clientCertificate }, [sh, ee, cr, certificate, cv, sf], none⟩

/-- Process a ClientHello, requiring ALPN before choosing the remaining parameters.

The server ignores SNI, as the Future Extensibility section of libp2p TLS requires. -/
def serverClientHello (config : Config) (state : State) (hello : ClientHello)
    (input : FlightMessage) : Except Error Step := do
  let protocols ← alpn hello.extensions
  ensure (libp2p ∈ protocols) .noApplicationProtocol
  checkClientHello config hello
  let offeredGroups ← groups hello.extensions
  let keyShares ← shares hello.extensions
  let suite ← select config.policy.cipherSuites hello.cipherSuites
  ensure (supportedSuite suite = true) .handshakeFailure
  let group ← select config.policy.groups offeredGroups
  ensure (Crypto.supportedGroup group = true) .handshakeFailure
  match state.retry with
  | none => pure ()
  | some retry =>
    checkSecondHello (← saved state.hello) hello retry
    ensure (suite = retry.suite ∧ retry.group = some group) .illegalParameter
  let state ← receive state input
  match keyShares.find? (fun share => share.group == group) with
  | some share => serverFlight config { state with hello := some hello } hello suite group share
  | none =>
    ensure (state.retry.isNone = true) .illegalParameter
    let extensions ← [Payload.selectedVersion 0x0304, .retryKeyShare group].mapM encodedPayload
    let retry : Retry := ⟨suite, some group, none⟩
    let (state, message) ← emit { state with hello := some hello, retry := some retry }
      .initial (.serverHello ⟨retryRandom, hello.legacySessionId, suite, extensions⟩)
    return ⟨state, [message], none⟩

/-- Read an optional retry group without confusing its payload with ServerHello's key share. -/
def retryGroup (extensions : List Extension) : Except Error (Option CodePoint) := do
  match extension 51 extensions with
  | none => return none
  | some value =>
    match ← wire (decodePayload .retryKeyShare value) with
    | .retryKeyShare group => return some group
    | _ => throw .decodeError

/-- Validate the cookie's opaque vector before echoing its exact bytes, RFC 8446 §4.2.2. -/
def retryCookie (extensions : List Extension) : Except Error (Option Extension) := do
  match extension 44 extensions with
  | none => return none
  | some value =>
    let _ ← wire (Wire.exact (Wire.blob 2 1 65535) value.data.data.toList)
    return some value

/-- Respond to one effective retry while retaining the first ClientHello's other fields. -/
def clientRetry (config : Config) (state : State) (hello : ClientHello)
    (server : ServerHello) (input : FlightMessage) : Except Error Step := do
  ensure (state.retry.isNone = true) .unexpectedMessage
  checkExtensions .retry (some hello.extensions) server.extensions
  let group ← retryGroup server.extensions
  let cookie ← retryCookie server.extensions
  ensure (group.isSome = true ∨ cookie.isSome = true) .illegalParameter
  let extensions ← match group with
    | none => pure hello.extensions
    | some group => do
      let offeredGroups ← groups hello.extensions
      let keyShares ← shares hello.extensions
      ensure (group ∈ offeredGroups ∧ ¬ group ∈ keyShares.map (·.group)) .illegalParameter
      let share ← localShare config group
      let replacement ← encodedPayload (.clientKeyShare [share])
      pure (hello.extensions.map fun value => if value.kind = 51 then replacement else value)
  let extensions := extensions.filter (fun value => value.kind != 42 && value.kind != 44)
  let extensions := extensions ++ cookie.toList
  let hello := { hello with extensions }
  let state ← receive state input
  let retry : Retry := ⟨server.cipherSuite, group, cookie⟩
  let (state, message) ← emit { state with hello := some hello, retry := some retry }
    .initial (.clientHello hello)
  return ⟨state, [message], none⟩

/-- Check ServerHello or HelloRetryRequest against the client offer, RFC 8446 §§4.1.3 and 4.1.4. -/
def clientServerHello (config : Config) (state : State) (server : ServerHello)
    (input : FlightMessage) : Except Error Step := do
  selectedVersion server.extensions
  let hello ← saved state.hello
  ensure (server.legacySessionIdEcho = hello.legacySessionId ∧
    server.cipherSuite ∈ hello.cipherSuites) .illegalParameter
  ensure (server.cipherSuite ∈ config.policy.cipherSuites ∧
    supportedSuite server.cipherSuite = true) .illegalParameter
  if server.random = retryRandom then
    clientRetry config state hello server input
  else
    checkExtensions .serverHello (some hello.extensions) server.extensions
    -- The client never offers a PSK, so a selected PSK identity is unsupported.
    ensure (extension 41 server.extensions = none) (.unsupportedExtension 41)
    let share ← match ← payload .serverKeyShare server.extensions with
      | .serverKeyShare share => pure share
      | _ => throw .decodeError
    let offered ← shares hello.extensions
    ensure (share.group ∈ offered.map (·.group) ∧ share.group ∈ config.policy.groups)
      .illegalParameter
    match state.retry with
    | none => pure ()
    | some retry =>
      ensure (server.cipherSuite = retry.suite ∧
        (retry.group = none ∨ retry.group = some share.group)) .illegalParameter
    let secret ← ephemeral config share.group
    let shared ← (Crypto.sharedSecret share.group secret share.keyExchange).mapError
      Error.crypto
    let state ← receive state input
    let state ← negotiate state server.cipherSuite share.group shared
    return ⟨{ state with phase := .encryptedExtensions }, [], none⟩

/-- Check EncryptedExtensions and the libp2p ALPN choice, RFC 8446 §4.3.1 and RFC 7301 §3.1. -/
def clientEncryptedExtensions (state : State) (extensions : List Extension)
    (input : FlightMessage) : Except Error Step := do
  let hello ← saved state.hello
  checkExtensions .encryptedExtensions (some hello.extensions) extensions
  let protocols ← alpn extensions
  ensure (protocols = [libp2p]) .noApplicationProtocol
  let _ ← payload .quicTransportParameters extensions
  let state ← receive state input
  return ⟨{ state with phase := .certificateRequest }, [], none⟩

/-- Require handshake client authentication with an empty request context, RFC 8446 §4.3.2. -/
def clientCertificateRequest (config : Config) (state : State) (request : CertificateRequest)
    (input : FlightMessage) : Except Error Step := do
  checkExtensions .certificateRequest none request.extensions
  ensure (request.context = ByteArray.empty) .illegalParameter
  let offered ← signatures request.extensions
  let _ ← select config.policy.signatureSchemes offered
  let state ← receive state input
  return ⟨{ state with phase := .serverCertificate, request := some request }, [], none⟩

/-- Verify server Finished, then send the client's Certificate, CertificateVerify and Finished. -/
def clientFinished (config : Config) (expected : ByteArray) (state : State)
    (value : ByteArray) (input : FlightMessage) : Except Error Step := do
  checkFinished true state value
  let state ← receive state input
  let state ← serverBoundary state
  let request ← saved state.request
  let offered ← signatures request.extensions
  let (state, certificate) ← emit state .handshake (certificateMessage config)
  let (state, cv) ← sendCertificateVerify config false offered state
  let (state, finished) ← sendFinished false state
  complete config (some expected) state [certificate, cv, finished]

/-- Accept a well-formed ticket without resuming or extending the main handshake transcript.

RFC 9001 §§4.5 and 4.6.1 allow tickets and constrain their early_data sentinel. -/
def receiveTicket (input : FlightMessage) : Except Error Unit := do
  checkLevel .application input
  let (kind, body) ← wire (Wire.exact readFrame input.data.data.toList)
  if kind = 13 then throw .protocolViolation
  ensure (kind = 4) .unexpectedMessage
  let reader : Wire.Reader (List Extension) := do
    let _ ← uint 4
    let _ ← uint 4
    let _ ← blob 1 0 255
    let _ ← blob 2 1 65535
    readExtensions 0
  let extensions ← wire (Wire.exact reader body)
  checkExtensions .newSessionTicket none extensions
  match extension 42 extensions with
  | none => pure ()
  | some value => ensure (value.data = [255, 255, 255, 255].toByteArray) .protocolViolation

/-- Advance the dialer's certificate handshake by one complete message.

An authenticated result follows verification of server Finished and transmission of client Finished.

Completed clients accept tickets, RFC 9001 §4.5.

They reject post-handshake authentication and TLS KeyUpdate, RFC 9001 §§4.4 and 6. -/
def clientStep (config : Config) (expected : ByteArray) (state : State)
    (input : FlightMessage) : Except Error Step := do
  match state.phase with
  | .serverHello =>
    match ← readMessage .initial input with
    | .serverHello server => clientServerHello config state server input
    | _ => throw .unexpectedMessage
  | .encryptedExtensions =>
    match ← readMessage .handshake input with
    | .encryptedExtensions extensions => clientEncryptedExtensions state extensions input
    | _ => throw .unexpectedMessage
  | .certificateRequest =>
    match ← readMessage .handshake input with
    | .certificateRequest request => clientCertificateRequest config state request input
    | _ => throw .unexpectedMessage
  | .serverCertificate =>
    match ← readMessage .handshake input with
    | .certificate certificate =>
      let hello ← saved state.hello
      let state ← receiveCertificate config (some expected) hello.extensions state certificate
      let state ← receive state input
      return ⟨{ state with phase := .serverCertificateVerify }, [], none⟩
    | _ => throw .unexpectedMessage
  | .serverCertificateVerify =>
    match ← readMessage .handshake input with
    | .certificateVerify algorithm signature =>
      let hello ← saved state.hello
      let offered ← signatures hello.extensions
      checkCertificateVerify config (some expected) true offered state algorithm signature
      let state ← receive state input
      return ⟨{ state with phase := .serverFinished }, [], none⟩
    | _ => throw .unexpectedMessage
  | .serverFinished =>
    match ← readMessage .handshake input with
    | .finished value => clientFinished config expected state value input
    | _ => throw .unexpectedMessage
  | .complete =>
    receiveTicket input
    return ⟨state, [], none⟩
  | _ => throw .unexpectedMessage

/-- Advance the listener's certificate handshake by one complete message.

The listener requires the client's certificate and verifies its signature and Finished.

Its authenticated result follows both Finished messages, RFC 9001 §4.1.1. -/
def serverStep (config : Config) (state : State) (input : FlightMessage) : Except Error Step := do
  match state.phase with
  | .clientHello =>
    match ← readMessage .initial input with
    | .clientHello hello => serverClientHello config state hello input
    | _ => throw .unexpectedMessage
  | .clientCertificate =>
    match ← readMessage .handshake input with
    | .certificate certificate =>
      -- Check the required client chain before reading any saved request state.
      ensure (certificate.entries ≠ []) .certificateRequired
      let request ← saved state.request
      let state ← receiveCertificate config none request.extensions state certificate
      let state ← receive state input
      return ⟨{ state with phase := .clientCertificateVerify }, [], none⟩
    | _ => throw .unexpectedMessage
  | .clientCertificateVerify =>
    match ← readMessage .handshake input with
    | .certificateVerify algorithm signature =>
      let request ← saved state.request
      let offered ← signatures request.extensions
      checkCertificateVerify config none false offered state algorithm signature
      let state ← receive state input
      return ⟨{ state with phase := .clientFinished }, [], none⟩
    | _ => throw .unexpectedMessage
  | .clientFinished =>
    match ← readMessage .handshake input with
    | .finished value =>
      checkFinished false state value
      let state ← receive state input
      complete config none state []
    | _ => throw .unexpectedMessage
  | .complete =>
    -- Data at an earlier level is a protocol violation; nothing else follows completion here.
    checkLevel .application input
    throw .unexpectedMessage
  | _ => throw .unexpectedMessage

end EthLib.Networking.Quic.Tls.Handshake
