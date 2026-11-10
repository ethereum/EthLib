module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Exports.Libp2p
public import EthLib.Networking.Noise.Identity

/-!
# Exports: Noise XX and libp2p identities

State tuples contain keys and must be kept private and passed back without modification.

Use a fresh ephemeral private key for each handshake.

Do not reuse a cipher state after a successful operation; use its returned state instead.

Discard the handshake state after a handshake error.

The libp2p state holds the remote that the read of message 2 or 3 authenticated.

Completion returns that remote and does not verify its signature again.

Framing follows [noise-libp2p][libp2p], "Wire Format".

[libp2p]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md
-/

public section

namespace EthLib.Networking.Noise.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- A cipher key, possibly absent during the handshake, and the next nonce. -/
abbrev CipherValue := Option Cryptography.ChaCha20Poly1305.Key × UInt64

/-- Role, private keys, remote keys, phase, chaining key, hash, cipher key and nonce. -/
abbrev StateValue := Bool × Key × Key × Option Key × Option Key × Nat × Vector UInt8 32 ×
  Vector UInt8 32 × Option Cryptography.ChaCha20Poly1305.Key × UInt64

/-- The remote static key, identity key protobuf, signature and extensions. -/
abbrev RemoteValue := Key × ByteArray × ByteArray × Option ByteArray

/-- An XX state and its authenticated remote, if any. -/
abbrev Libp2pValue := StateValue × Option RemoteValue

def cipherToValue (s : CipherState) : CipherValue := (s.key, s.nonce)
def cipherOfValue (s : CipherValue) : CipherState := ⟨s.1, s.2⟩

def stateToValue (s : HandshakeState) : StateValue :=
  (s.initiator, s.staticKey, s.ephemeralKey, s.remoteStatic, s.remoteEphemeral, s.step,
    s.symmetric.chainingKey.bytes, s.symmetric.hash.bytes, s.symmetric.cipher.key,
    s.symmetric.cipher.nonce)

def stateOfValue (v : StateValue) : HandshakeState :=
  let (initiator, staticKey, ephemeralKey, remoteStatic, remoteEphemeral,
    step, ck, h, key, nonce) := v
  ⟨initiator, staticKey, ephemeralKey, remoteStatic, remoteEphemeral, step,
    ⟨⟨ck⟩, ⟨h⟩, ⟨key, nonce⟩⟩⟩

def remoteToValue (r : Remote) : RemoteValue :=
  (r.staticKey, r.publicKey, r.signature, r.extensions)

/-- Read back the remote of a returned state.

Only its key protobuf is decoded; its signature is not checked again. -/
def remoteOfValue (v : RemoteValue) : Except NoiseError Remote := do
  let (staticKey, publicKey, signature, extensions) := v
  let key ← (Libp2p.decodePublicKey publicKey).mapError fun _ => .savedRemote
  return ⟨staticKey, key, signature, extensions⟩

def libp2pToValue (s : Libp2pState) : Libp2pValue :=
  (stateToValue s.handshake, s.remote.map remoteToValue)

def libp2pOfValue (v : Libp2pValue) : Except NoiseError Libp2pState := do
  let remote ← match v.2 with
    | none => pure none
    | some r => some <$> remoteOfValue r
  return ⟨stateOfValue v.1, remote⟩

def result {α : Type} (r : Except NoiseError α) : Result α :=
  r.mapError fun error => (error.code, reprStr error)

/-- Initialize the raw XX state with explicit private keys and prologue, Noise §5.3. -/
@[export eth_noise_initialize]
def initializeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (initiator, staticKey, ephemeralKey, prologue) =>
    pure (stateToValue (initializeHandshake initiator staticKey ephemeralKey prologue))) args

/-- Write the next raw XX message and return the updated state, Noise §5.3. -/
@[export eth_noise_write_message]
def writeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, payload) => result (do
    let (state, message) ← writeMessage (stateOfValue value) payload
    return (stateToValue state, message))) args

/-- Read the next raw XX message and return its payload and updated state, Noise §5.3. -/
@[export eth_noise_read_message]
def readExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, message) => result (do
    let (state, payload) ← readMessage (stateOfValue value) message
    return (stateToValue state, payload))) args

/-- Split a completed raw XX state into its send cipher, receive cipher and hash.

The split is Noise §5.2, and its first cipher carries initiator-to-responder messages, Noise §5. -/
@[export eth_noise_transport]
def transportExport (args : PyValue) : Result PyValue :=
  letI : EthLib.Exports.FromPyItems StateValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => result (do
    let state := stateOfValue value
    let (send, receive) ← transport state
    return (cipherToValue send, cipherToValue receive, state.symmetric.hash.bytes))) args

/-- Encrypt with a cipher state and associated data, returning its next state, Noise §5.1. -/
@[export eth_noise_cipher_encrypt]
def cipherEncryptExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, aad, plaintext) => result (do
    let (state, ciphertext) ← encryptWithAd (cipherOfValue value) aad plaintext
    return (cipherToValue state, ciphertext))) args

/-- Authenticate and decrypt, advancing the nonce only on success, Noise §5.1. -/
@[export eth_noise_cipher_decrypt]
def cipherDecryptExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, aad, ciphertext) => result (do
    let (state, plaintext) ← decryptWithAd (cipherOfValue value) aad ciphertext
    return (cipherToValue state, plaintext))) args

/-- Prefix the 16-bit big-endian message length, noise-libp2p "Wire Format". -/
@[export eth_noise_frame]
def frameExport (args : PyValue) : Result PyValue :=
  pyExport (fun bytes => result (frame bytes)) args

/-- Read exactly one complete 16-bit frame, noise-libp2p "Wire Format". -/
@[export eth_noise_unframe]
def unframeExport (args : PyValue) : Result PyValue :=
  pyExport (fun bytes => result (unframe bytes)) args

/-- Initialize libp2p XX with explicit X25519 private keys and an empty prologue.

noise-libp2p sets no prologue. -/
@[export eth_noise_libp2p_initialize]
def initializeLibp2pExport (args : PyValue) : Result PyValue :=
  pyExport (fun (initiator, staticKey, ephemeralKey) =>
    pure (libp2pToValue (initializeLibp2p initiator staticKey ephemeralKey))) args

/-- Write the next libp2p message with a signed identity payload.

The identity secret is 32 big-endian bytes whose value is in [1, n), with n the group order.

It is checked before every other check, on every message. -/
@[export eth_noise_libp2p_write]
def writeLibp2pExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, identitySecret, extensions) => result (do
    let secret ← (Libp2p.Exports.secretOfBytes identitySecret).mapError identitySecretError
    let (state, message) ← writeLibp2p (← libp2pOfValue value) secret extensions
    return (libp2pToValue state, message))) args

/-- Read the next libp2p message, and authenticate the static key of message 2 or 3. -/
@[export eth_noise_libp2p_read]
def readLibp2pExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, message) => result (do
    let state ← readLibp2p (← libp2pOfValue value) message
    return libp2pToValue state)) args

/-- Return the authenticated peer and transport keys only after completion. -/
@[export eth_noise_libp2p_complete]
def completeExport (args : PyValue) : Result PyValue :=
  letI : EthLib.Exports.FromPyItems Libp2pValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => result (do
    let state ← libp2pOfValue value
    let (remote, send, receive) ← complete state
    return (remote.staticKey,
      (remote.publicKey, Libp2p.peerId remote.key, remote.signature, remote.extensions),
      cipherToValue send, cipherToValue receive, state.handshake.symmetric.hash.bytes))) args

end EthLib.Networking.Noise.Exports
