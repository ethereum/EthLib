module

public import EthLib.Base.Bytes
public import EthLib.Base.BigEndian
public import EthLib.Base.LittleEndian
public import EthLib.Cryptography.X25519
public import EthLib.Cryptography.ChaCha20Poly1305
public import EthLib.Cryptography.Hash.Hkdf

/-!
# Noise XX

The state machine of [Noise revision 34, §§4, 5 and 7.5][noise].

Keys and ephemeral randomness are explicit inputs, so every operation is a pure function.

The concrete suite is `Noise_XX_25519_ChaChaPoly_SHA256`.

The protocol name and framing follow [noise-libp2p][libp2p].

Keys are secret, and this specification makes no constant-time claim.

[noise]: https://noiseprotocol.org/noise_rev34.pdf
[libp2p]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Base
open EthLib.Cryptography

abbrev Key := X25519.Key

/-- A malformed message, exhausted nonce, invalid phase, or primitive failure. -/
inductive NoiseError where
  | wrongPhase
  | missingKey
  | truncated
  | messageTooLong
  | frameLength
  | nonceExhausted
  | cipher (error : ChaCha20Poly1305.ChaCha20Poly1305Error)
  | protobuf
  | identity
  | firstMessageExtensions
deriving DecidableEq, Repr

def NoiseError.code : NoiseError → UInt32
  | .wrongPhase => 1
  | .missingKey => 2
  | .truncated => 3
  | .messageTooLong => 4
  | .frameLength => 5
  | .nonceExhausted => 6
  | .cipher _ => 7
  | .protobuf => 8
  | .identity => 9
  | .firstMessageExtensions => 10

/-- The exact concrete protocol name, Noise §8 and noise-libp2p "Noise Protocol Name". -/
def protocolName : ByteArray := "Noise_XX_25519_ChaChaPoly_SHA256".toUTF8

/-- Four zero bytes and the little-endian 64-bit nonce, Noise §12.3. -/
def cipherNonce (n : UInt64) : ChaCha20Poly1305.Nonce :=
  let low := uintToBytes 8 n.toNat
  Vector.ofFn fun i : Fin 12 => if h : i.val < 4 then 0 else low[i.val - 4]'(by omega)

/-- A key, which may be absent during the handshake, and its next nonce, Noise §5.1. -/
structure CipherState where
  key : Option Key
  nonce : UInt64

/-- Install a key and reset the nonce, Noise §5.1. -/
def initializeKey (key : Option Key) : CipherState := ⟨key, 0⟩

/-- Encrypt, appending the tag and advancing only a keyed nonce, Noise §5.1. -/
def encryptWithAd (s : CipherState) (aad plaintext : ByteArray) :
    Except NoiseError (CipherState × ByteArray) := do
  match s.key with
  | none =>
    if plaintext.size > 65535 then throw .messageTooLong
    return (s, plaintext)
  | some key =>
    if plaintext.size + 16 > 65535 then throw .messageTooLong
    if s.nonce = 2 ^ 64 - 1 then throw .nonceExhausted
    let (ciphertext, tag) ← (ChaCha20Poly1305.encrypt key (cipherNonce s.nonce)
      aad plaintext).mapError NoiseError.cipher
    return (⟨s.key, s.nonce + 1⟩, ciphertext ++ packBytes tag)

/-- Authenticate before advancing the nonce or returning plaintext, Noise §5.1. -/
def decryptWithAd (s : CipherState) (aad ciphertext : ByteArray) :
    Except NoiseError (CipherState × ByteArray) := do
  if ciphertext.size > 65535 then throw .messageTooLong
  match s.key with
  | none => return (s, ciphertext)
  | some key =>
    if s.nonce = 2 ^ 64 - 1 then throw .nonceExhausted
    if h : 16 ≤ ciphertext.size then
      let tag := readBytes ciphertext (ciphertext.size - 16) 16 (by omega)
      let plaintext ← (ChaCha20Poly1305.decrypt key (cipherNonce s.nonce) aad
        (ciphertext.extract 0 (ciphertext.size - 16)) tag).mapError NoiseError.cipher
      return (⟨s.key, s.nonce + 1⟩, plaintext)
    else throw .truncated

/-- Two HKDF outputs, with the chaining key as salt and empty info, Noise §4.3. -/
def hkdf2 (chainingKey : Key) (input : ByteArray) : Key × Key :=
  let output := Hash.Hkdf.expandBlocks (Hash.Hkdf.extract (packBytes chainingKey) input)
    .empty .empty 1 2
  have hmacSize (key message : ByteArray) : (Hash.Hmac.hmac key message).size = 32 := by
    unfold Hash.Hmac.hmac
    exact (Hash.Sha256.hash32 _).size_toArray
  have size : output.size = 64 := by
    simp only [output, Hash.Hkdf.expandBlocks, ByteArray.size_append, hmacSize]
    rfl
  (readBytes output 0 32 (by omega), readBytes output 32 32 (by omega))

/-- The chaining key, transcript hash and handshake cipher, Noise §5.2. -/
structure SymmetricState where
  chainingKey : Key
  hash : Key
  cipher : CipherState

/-- Set the padded protocol name, chaining key and empty cipher key, Noise §5.2. -/
def initializeSymmetric : SymmetricState :=
  let hash := if h : protocolName.size ≤ 32 then
      Vector.ofFn fun i : Fin 32 =>
        if hi : i.val < protocolName.size then protocolName[i.val] else 0
    else Hash.Sha256.hash32 protocolName
  ⟨hash, hash, initializeKey none⟩

/-- Hash the old transcript hash and the supplied bytes, Noise §5.2. -/
def mixHash (s : SymmetricState) (bytes : ByteArray) : SymmetricState :=
  { s with hash := Hash.Sha256.hash32 (packBytes s.hash ++ bytes) }

/-- Derive a new chaining key and cipher key, resetting the nonce, Noise §5.2. -/
def mixKey (s : SymmetricState) (input : Key) : SymmetricState :=
  let (chainingKey, key) := hkdf2 s.chainingKey (packBytes input)
  ⟨chainingKey, s.hash, initializeKey (some key)⟩

/-- Encrypt with the transcript as AAD, then hash the ciphertext, Noise §5.2. -/
def encryptAndHash (s : SymmetricState) (plaintext : ByteArray) :
    Except NoiseError (SymmetricState × ByteArray) := do
  let (cipher, ciphertext) ← encryptWithAd s.cipher (packBytes s.hash) plaintext
  return (mixHash { s with cipher := cipher } ciphertext, ciphertext)

/-- Decrypt with the transcript as AAD, then hash the ciphertext, Noise §5.2. -/
def decryptAndHash (s : SymmetricState) (ciphertext : ByteArray) :
    Except NoiseError (SymmetricState × ByteArray) := do
  let (cipher, plaintext) ← decryptWithAd s.cipher (packBytes s.hash) ciphertext
  return (mixHash { s with cipher := cipher } ciphertext, plaintext)

/-- Transport ciphers, ordered initiator-to-responder then responder-to-initiator, Noise §5.2. -/
def split (s : SymmetricState) : CipherState × CipherState :=
  let (first, second) := hkdf2 s.chainingKey .empty
  (initializeKey (some first), initializeKey (some second))

/-- The explicit keys, remote coordinates and next message number of XX, Noise §5.3. -/
structure HandshakeState where
  initiator : Bool
  staticKey : Key
  ephemeralKey : Key
  remoteStatic : Option Key
  remoteEphemeral : Option Key
  step : Nat
  symmetric : SymmetricState

/-- Initialize XX and hash the prologue, with no pre-messages, Noise §§5.3 and 7.5. -/
def initializeHandshake (initiator : Bool) (staticKey ephemeralKey : Key) (prologue : ByteArray) :
    HandshakeState :=
  ⟨initiator, staticKey, ephemeralKey, none, none, 0, mixHash initializeSymmetric prologue⟩

/-- Read a required remote coordinate instead of substituting one, Noise §5.3. -/
def requireKey : Option Key → Except NoiseError Key
  | some key => .ok key
  | none => .error .missingKey

/-- A decrypted static coordinate has exactly `DHLEN` bytes, Noise §5.3. -/
def readKey (bytes : ByteArray) : Except NoiseError Key :=
  if h : bytes.size = 32 then .ok ⟨bytes.data, h⟩ else .error .truncated

/-- The next XX outgoing message, including its implicit payload, Noise §§5.3 and 7.5. -/
def writeMessage (s : HandshakeState) (payload : ByteArray) :
    Except NoiseError (HandshakeState × ByteArray) := do
  let (symmetric, header) ← (match s.initiator, s.step with
    | true, 0 => do
      if payload.size + 32 > 65535 then throw .messageTooLong
      let ephemeral := packBytes (X25519.publicKey s.ephemeralKey)
      return (mixHash s.symmetric ephemeral, ephemeral)
    | false, 1 => do
      if payload.size + 96 > 65535 then throw .messageTooLong
      let remote ← requireKey s.remoteEphemeral
      let ephemeral := packBytes (X25519.publicKey s.ephemeralKey)
      let symmetric := mixKey (mixHash s.symmetric ephemeral) (X25519.x25519 s.ephemeralKey remote)
      let (symmetric, static) ← encryptAndHash symmetric (packBytes (X25519.publicKey s.staticKey))
      return (mixKey symmetric (X25519.x25519 s.staticKey remote), ephemeral ++ static)
    | true, 2 => do
      if payload.size + 64 > 65535 then throw .messageTooLong
      let remote ← requireKey s.remoteEphemeral
      let (symmetric, static) ← encryptAndHash s.symmetric
        (packBytes (X25519.publicKey s.staticKey))
      return (mixKey symmetric (X25519.x25519 s.staticKey remote), static)
    | _, _ => throw .wrongPhase : Except NoiseError (SymmetricState × ByteArray))
  let (symmetric, ciphertext) ← encryptAndHash symmetric payload
  return ({ s with symmetric := symmetric, step := s.step + 1 }, header ++ ciphertext)

/-- The next XX incoming message; each static key comes from its decrypted token, Noise §5.3. -/
def readMessage (s : HandshakeState) (message : ByteArray) :
    Except NoiseError (HandshakeState × ByteArray) := do
  if message.size > 65535 then throw .messageTooLong
  let (s, remaining) ← (match s.initiator, s.step with
    | false, 0 => do
      if h : 32 ≤ message.size then
        let remote := readBytes message 0 32 h
        return ({ s with
          remoteEphemeral := some remote
          symmetric := mixHash s.symmetric (packBytes remote) }, message.extract 32 message.size)
      else throw .truncated
    | true, 1 => do
      if h : 96 ≤ message.size then
        let remote := readBytes message 0 32 (by omega)
        let symmetric := mixKey (mixHash s.symmetric (packBytes remote))
          (X25519.x25519 s.ephemeralKey remote)
        let (symmetric, staticBytes) ← decryptAndHash symmetric (message.extract 32 80)
        let static ← readKey staticBytes
        let symmetric := mixKey symmetric (X25519.x25519 s.ephemeralKey static)
        return ({ s with
          remoteEphemeral := some remote
          remoteStatic := some static
          symmetric := symmetric }, message.extract 80 message.size)
      else throw .truncated
    | false, 2 => do
      if 64 ≤ message.size then
        let (symmetric, staticBytes) ← decryptAndHash s.symmetric (message.extract 0 48)
        let static ← readKey staticBytes
        let symmetric := mixKey symmetric (X25519.x25519 s.ephemeralKey static)
        return ({ s with remoteStatic := some static, symmetric := symmetric },
          message.extract 48 message.size)
      else throw .truncated
    | _, _ => throw .wrongPhase : Except NoiseError (HandshakeState × ByteArray))
  let (symmetric, payload) ← decryptAndHash s.symmetric remaining
  return ({ s with symmetric := symmetric, step := s.step + 1 }, payload)

/-- Return send and receive ciphers only after all three messages, Noise §§5.2 and 5.3. -/
def transport (s : HandshakeState) : Except NoiseError (CipherState × CipherState) :=
  if s.step = 3 then
    let (forward, backward) := split s.symmetric
    .ok (if s.initiator then (forward, backward) else (backward, forward))
  else .error .wrongPhase

/-- Prefix a message with its 16-bit big-endian length, noise-libp2p "Wire Format". -/
def frame (message : ByteArray) : Except NoiseError ByteArray :=
  if message.size ≤ 65535 then
    .ok (⟨(natToBytes 2 message.size).toArray⟩ ++ message)
  else .error .messageTooLong

/-- Decode exactly one complete frame, noise-libp2p "Wire Format". -/
def unframe (bytes : ByteArray) : Except NoiseError ByteArray := do
  if h : 2 ≤ bytes.size then
    let size := bytesToNat (readBytes bytes 0 2 h).toList
    if size + 2 = bytes.size then return bytes.extract 2 bytes.size else throw .frameLength
  else throw .truncated

end EthLib.Networking.Noise
