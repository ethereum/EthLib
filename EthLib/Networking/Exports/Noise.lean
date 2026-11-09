module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Noise.Identity

/-!
# Exports: Noise XX and libp2p identities

State tuples contain keys and must be kept private and passed back without modification.

Use a fresh ephemeral private key for each handshake.

Do not reuse a cipher state after a successful operation; use its returned state instead.

Discard the handshake state after a handshake error.

The libp2p completion result comes from a payload whose static-key signature verifies.

Framing follows [noise-libp2p][libp2p], "Wire Format".

[libp2p]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md
-/

public section

namespace EthLib.Networking.Noise.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- A cipher key, possibly absent during the handshake, and the next nonce. -/
abbrev CipherValue := Option Key × UInt64

/-- Role, private keys, remote keys, phase, chaining key, hash, cipher key and nonce. -/
abbrev StateValue := Bool × Key × Key × Option Key × Option Key × Nat × Key × Key ×
  Option Key × UInt64

/-- An XX state and the original encrypted message with its pre-read state. -/
abbrev Libp2pValue := StateValue × Option (StateValue × ByteArray)

def cipherToValue (s : CipherState) : CipherValue := (s.key, s.nonce)
def cipherOfValue (s : CipherValue) : CipherState := ⟨s.1, s.2⟩

def stateToValue (s : HandshakeState) : StateValue :=
  (s.initiator, s.staticKey, s.ephemeralKey, s.remoteStatic, s.remoteEphemeral, s.step,
    s.symmetric.chainingKey, s.symmetric.hash, s.symmetric.cipher.key, s.symmetric.cipher.nonce)

def stateOfValue (v : StateValue) : HandshakeState :=
  let (initiator, staticKey, ephemeralKey, remoteStatic, remoteEphemeral,
    step, ck, h, key, nonce) := v
  ⟨initiator, staticKey, ephemeralKey, remoteStatic, remoteEphemeral, step,
    ⟨ck, h, ⟨key, nonce⟩⟩⟩

def libp2pToValue (s : Libp2pState) : Libp2pValue :=
  (stateToValue s.handshake, s.remoteMessage.map fun (before, message) =>
    (stateToValue before, message))

def libp2pOfValue (v : Libp2pValue) : Libp2pState :=
  ⟨stateOfValue v.1, v.2.map fun (before, message) => (stateOfValue before, message)⟩

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

The split is Noise §5.2, and the order by role is Noise §5.3. -/
@[export eth_noise_transport]
def transportExport (args : PyValue) : Result PyValue :=
  letI : EthLib.Exports.FromPyItems StateValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => result (do
    let state := stateOfValue value
    let (send, receive) ← transport state
    return (cipherToValue send, cipherToValue receive, state.symmetric.hash))) args

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

/-- Initialize libp2p XX with the empty prologue and explicit X25519 private keys. -/
@[export eth_noise_libp2p_initialize]
def initializeLibp2pExport (args : PyValue) : Result PyValue :=
  pyExport (fun (initiator, staticKey, ephemeralKey) =>
    pure (libp2pToValue (initializeLibp2p initiator staticKey ephemeralKey))) args

/-- Write the next libp2p message with a signed identity payload. -/
@[export eth_noise_libp2p_write]
def writeLibp2pExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, identitySecret, extensions) => result (do
    let (state, message) ← writeLibp2p (libp2pOfValue value) identitySecret extensions
    return (libp2pToValue state, message))) args

/-- Read the next libp2p message, and authenticate the static key of message 2 or 3. -/
@[export eth_noise_libp2p_read]
def readLibp2pExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value, message) => result (do
    let state ← readLibp2p (libp2pOfValue value) message
    return libp2pToValue state)) args

/-- Return the authenticated peer and transport keys only after completion. -/
@[export eth_noise_libp2p_complete]
def completeExport (args : PyValue) : Result PyValue :=
  letI : EthLib.Exports.FromPyItems Libp2pValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => result (do
    let state := libp2pOfValue value
    let (staticKey, identity) ← complete state
    let (send, receive) ← transport state.handshake
    return (staticKey, identity, cipherToValue send, cipherToValue receive,
      state.handshake.symmetric.hash))) args

end EthLib.Networking.Noise.Exports
