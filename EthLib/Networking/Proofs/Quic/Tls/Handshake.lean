module

public import EthLib.Networking.Quic.Tls.Handshake
public import EthLib.Networking.Proofs.Libp2p.Tls
public import EthLib.Networking.Proofs.Quic.Tls.Crypto
public import EthLib.Base.Proofs.MapM

/-!
# Proofs: the libp2p QUIC certificate handshake

Completion reports the peer ID of certificate authentication and reconstructs the TLS key schedule.

Rejection theorems cover the libp2p ALPN check and the required client certificate.

Finished is accepted exactly when it matches the saved transcript.

CertificateVerify also needs an offered scheme and an authenticated certificate.

No theorem here ties a completion to an earlier CertificateVerify over every reachable state.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Handshake

open EthLib.Base

/-- Reading a saved value succeeds exactly when that value is present. -/
private theorem saved_eq_ok_iff {α : Type} (value : Option α) (out : α) :
    saved value = .ok out ↔ value = some out := by
  cases value <;> simp [saved]

/-- TLS signing-use checks retain the result of libp2p certificate authentication. -/
private theorem authenticate_source (config : Config) (expected : Option ByteArray)
    (chain : List ByteArray) (peer : Libp2p.Tls.AuthenticatedPeer)
    (accepted : authenticate config expected chain = .ok peer) :
    (match expected with
      | none => Libp2p.Tls.authenticate config.policy.certificates config.now chain
      | some id => Libp2p.Tls.authenticatePeer config.policy.certificates config.now id chain) =
        .ok peer := by
  simp only [authenticate, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨remote, original, _, _, same⟩ := accepted
  cases same
  exact mapError_ok_iff.mp original

/-- Completion authenticates the chain that it reports and returns exactly that peer ID. -/
theorem complete_peerId (config : Config) (expected : Option ByteArray) (state : State)
    (output : List FlightMessage) (step : Step) (result : Completion)
    (accepted : complete config expected state output = .ok step)
    (completed : step.completion = some result) :
    ∃ peer, authenticate config expected result.peerChain = .ok peer ∧
      result.peerId = peer.peerId := by
  simp only [complete, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨negotiated, _, secrets, _, peer, authenticated, rfl⟩ := accepted
  cases Option.some.inj completed
  exact ⟨peer, authenticated, rfl⟩

/-- Completion derives its reported secrets from its reported ECDHE and transcript inputs. -/
theorem complete_keySchedule (config : Config) (expected : Option ByteArray) (state : State)
    (output : List FlightMessage) (step : Step) (result : Completion)
    (accepted : complete config expected state output = .ok step)
    (completed : step.completion = some result) :
    keySchedule (packBytes result.negotiated.sharedSecret) result.negotiated.helloTranscript
      result.negotiated.serverTranscript = .ok result.negotiated.secrets := by
  simp only [complete, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨negotiated, _, secrets, schedule, peer, _, rfl⟩ := accepted
  cases Option.some.inj completed
  exact mapError_ok_iff.mp schedule

/-- ALPN rejects a parsed client offer without the libp2p application protocol. -/
theorem serverClientHello_alpn (config : Config) (state : State) (hello : ClientHello)
    (input : FlightMessage) (protocols : List ByteArray)
    (parsed : alpn hello.extensions = .ok protocols) (missing : libp2p ∉ protocols) :
    serverClientHello config state hello input = .error .noApplicationProtocol := by
  simp [serverClientHello, parsed, ensure, missing, bind, Except.bind]

/-- A listener rejects a ClientHello whose parsed ALPN list omits libp2p. -/
theorem serverStep_alpn (config : Config) (state : State) (hello : ClientHello)
    (input : FlightMessage) (protocols : List ByteArray)
    (phase : state.phase = .clientHello)
    (message : readMessage .initial input = .ok (.clientHello hello))
    (parsed : alpn hello.extensions = .ok protocols) (missing : libp2p ∉ protocols) :
    serverStep config state input = .error .noApplicationProtocol := by
  simp [serverStep, phase, message, serverClientHello_alpn config state hello input protocols
    parsed missing, bind, Except.bind]

/-- An empty client certificate is rejected before any saved request is read. -/
theorem serverStep_clientCertificate (config : Config) (state : State)
    (certificate : CertificateMessage) (input : FlightMessage)
    (phase : state.phase = .clientCertificate)
    (message : readMessage .handshake input = .ok (.certificate certificate))
    (empty : certificate.entries = []) :
    serverStep config state input = .error .certificateRequired := by
  simp [serverStep, phase, message, empty, ensure, bind, Except.bind]

/-- A successful ServerHello selection uses one of the implemented SHA-256 suites. -/
theorem clientServerHello_supportedSuite (config : Config) (state : State)
    (server : ServerHello) (input : FlightMessage) (step : Step)
    (accepted : clientServerHello config state server input = .ok step) :
    supportedSuite server.cipherSuite = true := by
  simp only [clientServerHello, bind_ok_iff] at accepted
  obtain ⟨_, _, _, _, _, _, _, supported, _⟩ := accepted
  exact (ensure_ok_iff.mp supported).2

/-- The SHA-384 cipher suite cannot complete ServerHello processing with a SHA-256 transcript. -/
theorem clientStep_rejects_sha384 (config : Config) (expected : ByteArray) (state : State)
    (server : ServerHello) (input : FlightMessage) (step : Step)
    (phase : state.phase = .serverHello)
    (message : readMessage .initial input = .ok (.serverHello server))
    (sha384 : server.cipherSuite.val = 0x1302) :
    clientStep config expected state input ≠ .ok step := by
  intro accepted
  have selected : clientServerHello config state server input = .ok step := by
    simpa only [clientStep, phase, message, bind, Except.bind] using accepted
  have supported := clientServerHello_supportedSuite config state server input step selected
  simp [supportedSuite, sha384] at supported

/-- Finished succeeds exactly for its derived HMAC under the saved sender's traffic secret. -/
theorem checkFinished_eq_ok_iff (server : Bool) (state : State) (value : ByteArray) :
    checkFinished server state value = .ok () ↔
      ∃ negotiated verifyData, state.negotiated = some negotiated ∧
        finished (if server then negotiated.secrets.serverHandshake
          else negotiated.secrets.clientHandshake) state.transcript.bytes =
            .ok verifyData ∧ value = packBytes verifyData := by
  simp only [checkFinished, bind_ok_iff, ensure_ok_iff, saved_eq_ok_iff, mapError_ok_iff]
  aesop

/-- CertificateVerify requires an offered scheme and a valid signature on this role's transcript.

The certificate and its signing-use check come from peer authentication. -/
theorem checkCertificateVerify_eq_ok_iff (config : Config) (expected : Option ByteArray)
    (server : Bool) (offered : List Wire.CodePoint) (state : State) (algorithm : Wire.CodePoint)
    (signature : ByteArray) :
    checkCertificateVerify config expected server offered state algorithm signature = .ok () ↔
      algorithm ∈ offered ∧ algorithm ∈ config.policy.signatureSchemes ∧
        algorithm.val = 0x0403 ∧ ∃ peer,
          authenticate config expected state.peerChain = .ok peer ∧
          Libp2p.Tls.verifyP256 peer.certificate.spki
            (certificateVerifyInput server state.transcript.hash)
            signature = true := by
  simp only [checkCertificateVerify, ensure_ok_iff, bind_ok_iff,
    Crypto.verifyCertificateVerify_eq_true_iff]
  aesop

/-- Accepting the server's CertificateVerify checks its exact role and pre-message transcript. -/
theorem clientStep_certificateVerify (config : Config) (expected : ByteArray) (state : State)
    (input : FlightMessage) (algorithm : Wire.CodePoint) (signature : ByteArray) (step : Step)
    (phase : state.phase = .serverCertificateVerify)
    (message : readMessage .handshake input = .ok (.certificateVerify algorithm signature))
    (accepted : clientStep config expected state input = .ok step) :
    ∃ hello offered, state.hello = some hello ∧ signatures hello.extensions = .ok offered ∧
      algorithm ∈ offered ∧ algorithm ∈ config.policy.signatureSchemes ∧
        algorithm.val = 0x0403 ∧ ∃ peer,
          authenticate config (some expected) state.peerChain = .ok peer ∧
          Libp2p.Tls.verifyP256 peer.certificate.spki
            (certificateVerifyInput true state.transcript.hash)
            signature = true := by
  simp only [clientStep, phase, bind_ok_iff, message, Except.ok.injEq] at accepted
  obtain ⟨_, rfl, accepted⟩ := accepted
  simp only [bind_ok_iff] at accepted
  obtain ⟨hello, helloSaved, offered, schemes, u, checked, _⟩ := accepted
  cases u
  exact ⟨hello, offered, (saved_eq_ok_iff state.hello hello).mp helloSaved, schemes,
    (checkCertificateVerify_eq_ok_iff config (some expected) true offered state algorithm
      signature).mp checked⟩

/-- Accepting the client's CertificateVerify checks its exact role and pre-message transcript. -/
theorem serverStep_certificateVerify (config : Config) (state : State) (input : FlightMessage)
    (algorithm : Wire.CodePoint) (signature : ByteArray) (step : Step)
    (phase : state.phase = .clientCertificateVerify)
    (message : readMessage .handshake input = .ok (.certificateVerify algorithm signature))
    (accepted : serverStep config state input = .ok step) :
    ∃ request offered, state.request = some request ∧ signatures request.extensions = .ok offered ∧
      algorithm ∈ offered ∧ algorithm ∈ config.policy.signatureSchemes ∧
        algorithm.val = 0x0403 ∧ ∃ peer,
          authenticate config none state.peerChain = .ok peer ∧
          Libp2p.Tls.verifyP256 peer.certificate.spki
            (certificateVerifyInput false state.transcript.hash)
            signature = true := by
  simp only [serverStep, phase, bind_ok_iff, message, Except.ok.injEq] at accepted
  obtain ⟨_, rfl, accepted⟩ := accepted
  simp only [bind_ok_iff] at accepted
  obtain ⟨request, requestSaved, offered, schemes, u, checked, _⟩ := accepted
  cases u
  exact ⟨request, offered, (saved_eq_ok_iff state.request request).mp requestSaved, schemes,
    (checkCertificateVerify_eq_ok_iff config none false offered state algorithm
      signature).mp checked⟩

/-- Accepting server Finished requires its derived HMAC on the pre-message transcript. -/
theorem clientStep_finished_eq (config : Config) (expected : ByteArray) (state : State)
    (input : FlightMessage) (value : ByteArray) (step : Step)
    (phase : state.phase = .serverFinished)
    (message : readMessage .handshake input = .ok (.finished value))
    (accepted : clientStep config expected state input = .ok step) :
    ∃ negotiated verifyData, state.negotiated = some negotiated ∧
      finished negotiated.secrets.serverHandshake state.transcript.bytes =
        .ok verifyData ∧ value = packBytes verifyData := by
  have final : clientFinished config expected state value input = .ok step := by
    simpa only [clientStep, phase, message, bind, Except.bind] using accepted
  simp only [clientFinished, bind_ok_iff] at final
  obtain ⟨u, checked, _⟩ := final
  cases u
  exact (checkFinished_eq_ok_iff true state value).mp checked

/-- Accepting client Finished requires its derived HMAC on the pre-message transcript. -/
theorem serverStep_finished_eq (config : Config) (state : State) (input : FlightMessage)
    (value : ByteArray) (step : Step) (phase : state.phase = .clientFinished)
    (message : readMessage .handshake input = .ok (.finished value))
    (accepted : serverStep config state input = .ok step) :
    ∃ negotiated verifyData, state.negotiated = some negotiated ∧
      finished negotiated.secrets.clientHandshake state.transcript.bytes =
        .ok verifyData ∧ value = packBytes verifyData := by
  simp only [serverStep, phase, bind_ok_iff, message, Except.ok.injEq] at accepted
  obtain ⟨_, rfl, accepted⟩ := accepted
  simp only [bind_ok_iff] at accepted
  obtain ⟨u, checked, _⟩ := accepted
  cases u
  exact (checkFinished_eq_ok_iff false state value).mp checked

/-- A Finished value different from the derived HMAC is rejected, RFC 8446 §4.4.4. -/
theorem checkFinished_rejects (server : Bool) (state : State) (negotiated : Negotiated)
    (value : ByteArray) (verifyData : Vector UInt8 32)
    (stored : state.negotiated = some negotiated)
    (computed : finished (if server then negotiated.secrets.serverHandshake
        else negotiated.secrets.clientHandshake) state.transcript.bytes = .ok verifyData)
    (different : value ≠ packBytes verifyData) :
    checkFinished server state value = .error .decryptError := by
  simp [checkFinished, stored, saved, computed, Except.mapError,
    ensure, different, bind, Except.bind]

/-- A dialer rejects a mismatching server Finished before emitting its final flight. -/
theorem clientStep_finished (config : Config) (expected : ByteArray) (state : State)
    (input : FlightMessage) (value : ByteArray)
    (phase : state.phase = .serverFinished)
    (message : readMessage .handshake input = .ok (.finished value))
    (rejected : checkFinished true state value = .error .decryptError) :
    clientStep config expected state input = .error .decryptError := by
  simp [clientStep, phase, message, clientFinished, rejected, bind, Except.bind]

/-- A listener rejects a mismatching client Finished before reporting completion. -/
theorem serverStep_finished (config : Config) (state : State) (input : FlightMessage)
    (value : ByteArray) (phase : state.phase = .clientFinished)
    (message : readMessage .handshake input = .ok (.finished value))
    (rejected : checkFinished false state value = .error .decryptError) :
    serverStep config state input = .error .decryptError := by
  simp [serverStep, phase, message, rejected, bind, Except.bind]

/-- A normal server flight cannot report an authenticated completion before the client replies. -/
private theorem serverFlight_completion (config : Config) (state : State) (hello : ClientHello)
    (suite group : Wire.CodePoint) (share : KeyShareEntry) (step : Step)
    (accepted : serverFlight config state hello suite group share = .ok step) :
    step.completion = none := by
  simp only [serverFlight, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  rfl

/-- EncryptedExtensions advances to certificate authentication without reporting completion. -/
private theorem clientEncryptedExtensions_completion (state : State) (extensions : List Extension)
    (input : FlightMessage) (step : Step)
    (accepted : clientEncryptedExtensions state extensions input = .ok step) :
    step.completion = none := by
  simp only [clientEncryptedExtensions, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  rfl

/-- A CertificateRequest advances to the server certificate without reporting completion. -/
private theorem clientCertificateRequest_completion (config : Config) (state : State)
    (request : CertificateRequest) (input : FlightMessage) (step : Step)
    (accepted : clientCertificateRequest config state request input = .ok step) :
    step.completion = none := by
  simp only [clientCertificateRequest, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  rfl

/-- A retry emits another ClientHello without reporting completion. -/
private theorem clientRetry_completion (config : Config) (state : State) (hello : ClientHello)
    (server : ServerHello) (input : FlightMessage) (step : Step)
    (accepted : clientRetry config state hello server input = .ok step) :
    step.completion = none := by
  simp only [clientRetry, bind_ok_iff] at accepted
  obtain ⟨_, _, _, _, group, _, cookie, _, _, _, accepted⟩ := accepted
  cases group <;>
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  all_goals aesop

/-- ServerHello and retry processing do not complete the dialer's handshake. -/
private theorem clientServerHello_completion (config : Config) (state : State)
    (server : ServerHello) (input : FlightMessage) (step : Step)
    (accepted : clientServerHello config state server input = .ok step) :
    step.completion = none := by
  simp only [clientServerHello, bind_ok_iff, pure, Except.pure] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward clientRetry_completion)

/-- A listener cannot complete its handshake while processing ClientHello. -/
private theorem serverClientHello_completion (config : Config) (state : State) (hello : ClientHello)
    (input : FlightMessage) (step : Step)
    (accepted : serverClientHello config state hello input = .ok step) :
    step.completion = none := by
  simp only [serverClientHello, bind_ok_iff, pure, Except.pure] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward serverFlight_completion)

/-- A dialer's final flight reports only the completion boundary's result. -/
private theorem clientFinished_complete (config : Config) (expected : ByteArray) (state : State)
    (value : ByteArray) (input : FlightMessage) (step : Step)
    (accepted : clientFinished config expected state value input = .ok step) :
    ∃ final output, complete config (some expected) final output = .ok step := by
  simp only [clientFinished, bind_ok_iff] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, accepted⟩
  exact ⟨_, _, accepted⟩

/-- Every completed client step has passed the common authentication and schedule boundary. -/
theorem clientStep_complete (config : Config) (expected : ByteArray) (state : State)
    (input : FlightMessage) (step : Step) (result : Completion)
    (accepted : clientStep config expected state input = .ok step)
    (completed : step.completion = some result) :
    ∃ final output, complete config (some expected) final output = .ok step := by
  simp only [clientStep] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward [clientServerHello_completion, clientEncryptedExtensions_completion,
      clientCertificateRequest_completion, clientFinished_complete])

/-- Every completed listener step has passed the common authentication and schedule boundary. -/
theorem serverStep_complete (config : Config) (state : State) (input : FlightMessage)
    (step : Step) (result : Completion)
    (accepted : serverStep config state input = .ok step)
    (completed : step.completion = some result) :
    ∃ final output, complete config none final output = .ok step := by
  simp only [serverStep] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward serverClientHello_completion)

/-- A completed dialer reports its certificate-derived peer ID, which is the identity it dialled. -/
theorem clientStep_peerId (config : Config) (expected : ByteArray) (state : State)
    (input : FlightMessage) (step : Step) (result : Completion)
    (accepted : clientStep config expected state input = .ok step)
    (completed : step.completion = some result) :
    ∃ peer, Libp2p.Tls.authenticate config.policy.certificates config.now result.peerChain =
        .ok peer ∧ result.peerId = peer.peerId ∧ result.peerId = expected := by
  obtain ⟨final, output, boundary⟩ :=
    clientStep_complete config expected state input step result accepted completed
  obtain ⟨peer, authenticated, identity⟩ :=
    complete_peerId config (some expected) final output step result boundary completed
  have checked : Libp2p.Tls.authenticatePeer config.policy.certificates config.now expected
      result.peerChain = .ok peer :=
    authenticate_source config (some expected) result.peerChain peer authenticated
  have dialled := EthLib.Networking.Proofs.Libp2p.Tls.authenticatePeer_peerId checked
  simp only [Libp2p.Tls.authenticatePeer, bind_ok_iff, ensure_ok_iff,
    pure, Except.pure, Except.ok.injEq] at checked
  obtain ⟨remote, checked, _, _, same⟩ := checked
  cases same
  exact ⟨peer, checked, identity, identity.trans dialled⟩

/-- A completed listener reports the peer ID returned by certificate authentication. -/
theorem serverStep_peerId (config : Config) (state : State) (input : FlightMessage)
    (step : Step) (result : Completion)
    (accepted : serverStep config state input = .ok step)
    (completed : step.completion = some result) :
    ∃ peer, Libp2p.Tls.authenticate config.policy.certificates config.now result.peerChain =
      .ok peer ∧ result.peerId = peer.peerId := by
  obtain ⟨final, output, boundary⟩ :=
    serverStep_complete config state input step result accepted completed
  obtain ⟨peer, authenticated, identity⟩ :=
    complete_peerId config none final output step result boundary completed
  exact ⟨peer, authenticate_source config none result.peerChain peer authenticated, identity⟩

/-- The secrets of two completions are equal when their ECDHE secrets and transcripts are equal.

The schedule is a function of those three inputs; no protocol agreement is claimed. -/
theorem completion_secrets_eq_of_inputs (clientConfig serverConfig : Config) (expected : ByteArray)
    (clientState serverState : State) (clientInput serverInput : FlightMessage)
    (clientStepResult serverStepResult : Step) (client server : Completion)
    (clientAccepted : clientStep clientConfig expected clientState clientInput =
      .ok clientStepResult)
    (serverAccepted : serverStep serverConfig serverState serverInput = .ok serverStepResult)
    (clientCompleted : clientStepResult.completion = some client)
    (serverCompleted : serverStepResult.completion = some server)
    (shared : client.negotiated.sharedSecret = server.negotiated.sharedSecret)
    (hello : client.negotiated.helloTranscript = server.negotiated.helloTranscript)
    (finished : client.negotiated.serverTranscript = server.negotiated.serverTranscript) :
    client.negotiated.secrets = server.negotiated.secrets := by
  obtain ⟨clientFinal, clientOutput, clientBoundary⟩ := clientStep_complete clientConfig expected
    clientState clientInput clientStepResult client clientAccepted clientCompleted
  obtain ⟨serverFinal, serverOutput, serverBoundary⟩ := serverStep_complete serverConfig
    serverState serverInput serverStepResult server serverAccepted serverCompleted
  have clientSchedule := complete_keySchedule clientConfig (some expected) clientFinal
    clientOutput clientStepResult client clientBoundary clientCompleted
  have serverSchedule := complete_keySchedule serverConfig none serverFinal
    serverOutput serverStepResult server serverBoundary serverCompleted
  rw [← shared, ← hello, ← finished] at serverSchedule
  exact Except.ok.inj (clientSchedule.symm.trans serverSchedule)

end EthLib.Networking.Quic.Tls.Handshake
