module

public import EthLib.Base.Bytes
public import EthLib.Base.BigEndian
public import EthLib.Base.ByteOrder
public import EthLib.Cryptography.X25519
public import EthLib.Cryptography.ChaCha20Poly1305
public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Cryptography.Secp256k1.Errors

/-!
# Noise XX

The state machine of [Noise revision 34, §§4, 5 and 7.5][noise].

Keys and ephemeral randomness are explicit inputs, so every operation is a pure function.

The concrete suite is `Noise_XX_25519_ChaChaPoly_SHA256`.

The protocol name follows the section Noise Protocol Name of [noise-libp2p][libp2p].

Framing follows its section Wire Format.

Keys are secret, and this specification makes no constant-time claim.

[noise]: https://noiseprotocol.org/noise_rev34.pdf
[libp2p]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/noise/README.md
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Base
open EthLib.Cryptography

/-- An X25519 private key, public coordinate or shared secret, Noise §12.1. -/
abbrev Key := X25519.Key

/-- The chaining key `ck` of Noise §5.2: `HASHLEN` bytes, 32 for SHA256 by §12.5. -/
structure ChainingKey where
  bytes : Vector UInt8 32
deriving DecidableEq

/-- The handshake hash `h` of Noise §5.2: `HASHLEN` bytes, 32 for SHA256 by §12.5. -/
structure HandshakeHash where
  bytes : Vector UInt8 32
deriving DecidableEq

/-- A malformed message, exhausted nonce, invalid phase or state, primitive or identity failure. -/
inductive NoiseError where
  /-- The operation does not belong to the current phase of the handshake.

  The fields hold the role, initiator or not, and the number of messages already handled. -/
  | wrongPhase (initiator : Bool) (step : Nat)
  /-- A remote public key that the message pattern needs has not been received. -/
  | missingKey
  /-- A message or frame is shorter than its fixed fields, or a decrypted key is not 32 bytes.

  The fields hold the bytes needed and the bytes available.

  For a decrypted key, the bytes available may be more than needed. -/
  | truncated (needed available : Nat)
  /-- A message or its payload would be `size` bytes, more than 65535, the limit of Noise §3.

  For a libp2p payload, `size` may be the sum of its fields, below the size of their encoding. -/
  | messageTooLong (size : Nat)
  /-- A frame declares a length of `declared` bytes, but `actual` bytes follow it. -/
  | frameLength (declared actual : Nat)
  /-- The nonce reached `2^64 - 1`, after which Noise §5.1 signals an error. -/
  | nonceExhausted
  /-- ChaCha20-Poly1305 rejected its input or the authentication tag. -/
  | cipher (error : ChaCha20Poly1305.ChaCha20Poly1305Error)
  /-- The libp2p payload is not well-formed protobuf. -/
  | protobuf
  /-- The remote identity key, or its signature on the received static key, does not verify. -/
  | identity
  /-- The first message carries libp2p extensions, which only later payloads may carry. -/
  | firstMessageExtensions
  /-- The local identity secret is 0.

  In the exports, it is also 32 bytes whose value is at least the secp256k1 group order. -/
  | identitySecret
  /-- ECDSA signing with the local identity secret failed. -/
  | signing (error : Secp256k1.Secp256k1Error)
  /-- At completion, the state holds no remote, or one without the handshake's remote static key.

  In the exports, it is also a stored remote whose key protobuf does not decode. -/
  | savedRemote
deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def NoiseError.code : NoiseError → UInt32
  | .wrongPhase .. => 1
  | .missingKey => 2
  | .truncated .. => 3
  | .messageTooLong _ => 4
  | .frameLength .. => 5
  | .nonceExhausted => 6
  | .cipher _ => 7
  | .protobuf => 8
  | .identity => 9
  | .firstMessageExtensions => 10
  | .identitySecret => 11
  | .signing _ => 12
  | .savedRemote => 13

/-- The protocol name, from Noise §8 and the section Noise Protocol Name of noise-libp2p. -/
def protocolName : ByteArray :=
  -- noise-libp2p: the Noise protocol name MUST be Noise_XX_25519_ChaChaPoly_SHA256.
  --
  -- Noise §8: Noise_, then the pattern XX and the DH, cipher and hash names, joined by underscores.
  "Noise_XX_25519_ChaChaPoly_SHA256".toUTF8

/-- Four zero bytes and the little-endian 64-bit nonce, Noise §12.3. -/
def cipherNonce (n : UInt64) : ChaCha20Poly1305.Nonce :=
  -- §12.3: the little-endian encoding of `n`, in 8 bytes.
  let low := ByteOrder.toLE 8 n.toNat
  -- §12.3: the 96-bit nonce is 32 bits of zeros, then those 8 bytes.
  Vector.ofFn fun i : Fin 12 => if h : i.val < 4 then 0 else low[i.val - 4]'(by omega)

/-- A key, which may be absent during the handshake, and its next nonce, Noise §5.1. -/
structure CipherState where
  key : Option ChaCha20Poly1305.Key
  nonce : UInt64

/-- Install a key and reset the nonce, Noise §5.1. -/
def initializeKey (key : Option ChaCha20Poly1305.Key) : CipherState :=
  -- `InitializeKey(key)`: sets `k = key` and `n = 0`.
  ⟨key, 0⟩

/-- Encrypt, appending the tag and advancing only a keyed nonce, Noise §5.1. -/
def encryptWithAd (s : CipherState) (aad plaintext : ByteArray) :
    Except NoiseError (CipherState × ByteArray) := do
  match s.key with
  | none =>
    -- §3: a message has at most 65535 bytes; EthLib checks it here, at the first point it can.
    if plaintext.size > 65535 then throw (.messageTooLong plaintext.size)
    -- `EncryptWithAd(ad, plaintext)`: if `k` is empty, returns plaintext.
    return (s, plaintext)
  | some key =>
    -- §3: the ciphertext, 16 bytes longer than the plaintext, has at most 65535 bytes.
    if plaintext.size + 16 > 65535 then throw (.messageTooLong (plaintext.size + 16))
    -- §5.1: the nonce `2^64 - 1` is reserved, so a call with it signals an error.
    if s.nonce = 2 ^ 64 - 1 then throw .nonceExhausted
    -- `ENCRYPT(k, n++, ad, plaintext)`: AEAD_CHACHA20_POLY1305, by §12.3.
    --
    -- §12.3 cites RFC 7539, which RFC 8439 obsoletes with the same AEAD construction.
    let (ciphertext, tag) ← (ChaCha20Poly1305.encrypt key (cipherNonce s.nonce)
      aad plaintext).mapError NoiseError.cipher
    -- The ciphertext with its 16-byte tag appended, and `n` incremented.
    return (⟨s.key, s.nonce + 1⟩, ciphertext ++ packBytes tag)

/-- Authenticate before advancing the nonce or returning plaintext, Noise §5.1. -/
def decryptWithAd (s : CipherState) (aad ciphertext : ByteArray) :
    Except NoiseError (CipherState × ByteArray) := do
  -- §3: a message has at most 65535 bytes, so a longer input is rejected first.
  if ciphertext.size > 65535 then throw (.messageTooLong ciphertext.size)
  match s.key with
  -- `DecryptWithAd(ad, ciphertext)`: if `k` is empty, returns ciphertext.
  | none => return (s, ciphertext)
  | some key =>
    -- §5.1: the nonce `2^64 - 1` is reserved, so a call with it signals an error.
    if s.nonce = 2 ^ 64 - 1 then throw .nonceExhausted
    -- The AEAD appends a 16-byte tag, so a shorter ciphertext cannot authenticate.
    if h : 16 ≤ ciphertext.size then
      -- The tag is the last 16 bytes.
      let tag := readBytes ciphertext (ciphertext.size - 16) 16 (by omega)
      -- `DECRYPT(k, n++, ad, ciphertext)`, by §12.3.
      --
      -- On an authentication failure, the error leaves `n` unchanged, as §5.1 asks.
      let plaintext ← (ChaCha20Poly1305.decrypt key (cipherNonce s.nonce) aad
        (ciphertext.extract 0 (ciphertext.size - 16)) tag).mapError NoiseError.cipher
      return (⟨s.key, s.nonce + 1⟩, plaintext)
    else throw (.truncated 16 ciphertext.size)

/-- The two outputs of `HKDF(chaining_key, input_key_material, 2)`, Noise §4.3. -/
def hkdf2 (chainingKey : ChainingKey) (input : ByteArray) :
    Vector UInt8 32 × Vector UInt8 32 :=
  -- Sets the temporary key to `HMAC-HASH(ck, input key material)`, SHA-256 by §12.5.
  let tempKey := Hash.Hmac.hmac (packBytes chainingKey.bytes) input
  -- Sets `output1` to `HMAC-HASH(temporary key, byte(0x01))`.
  let first := Hash.Hmac.hmac32 tempKey ⟨#[0x01]⟩
  -- Sets `output2` to `HMAC-HASH(temporary key, output1 || byte(0x02))`.
  --
  -- With two outputs, HKDF returns the pair `(output1, output2)`.
  (first, Hash.Hmac.hmac32 tempKey (packBytes first ++ ⟨#[0x02]⟩))

/-- The chaining key, transcript hash and handshake cipher, Noise §5.2. -/
structure SymmetricState where
  chainingKey : ChainingKey
  hash : HandshakeHash
  cipher : CipherState

/-- Set the padded protocol name, chaining key and empty cipher key, Noise §5.2. -/
def initializeSymmetric : SymmetricState :=
  -- InitializeSymmetric, step 1: a name of at most `HASHLEN` bytes, zero-padded, is `h`.
  --
  -- A longer name sets `h` to its hash.
  let hash := if h : protocolName.size ≤ 32 then
      Vector.ofFn fun i : Fin 32 =>
        if hi : i.val < protocolName.size then protocolName[i.val] else 0
    else Hash.Sha256.hash32 protocolName
  -- Step 2: `ck = h`; step 3: `InitializeKey(empty)`.
  ⟨⟨hash⟩, ⟨hash⟩, initializeKey none⟩

/-- Hash the old transcript hash and the supplied bytes, Noise §5.2. -/
def mixHash (s : SymmetricState) (bytes : ByteArray) : SymmetricState :=
  -- `MixHash(data)`: `h = HASH(h || data)`.
  { s with hash := ⟨Hash.Sha256.hash32 (packBytes s.hash.bytes ++ bytes)⟩ }

/-- Derive a new chaining key and cipher key, resetting the nonce, Noise §5.2. -/
def mixKey (s : SymmetricState) (input : Key) : SymmetricState :=
  -- MixKey, step 1: `ck` and the key `temp_k` are the two outputs of HKDF of `ck` and the input.
  --
  -- Step 2 truncates only for a `HASHLEN` of 64, so SHA-256 skips it.
  let (chainingKey, key) := hkdf2 s.chainingKey (packBytes input)
  -- Step 3: `InitializeKey(temp_k)`.
  ⟨⟨chainingKey⟩, s.hash, initializeKey (some key)⟩

/-- Encrypt with the transcript as AAD, then hash the ciphertext, Noise §5.2. -/
def encryptAndHash (s : SymmetricState) (plaintext : ByteArray) :
    Except NoiseError (SymmetricState × ByteArray) := do
  -- `ciphertext = EncryptWithAd(h, plaintext)`.
  let (cipher, ciphertext) ← encryptWithAd s.cipher (packBytes s.hash.bytes) plaintext
  -- `MixHash(ciphertext)`, then return the ciphertext.
  return (mixHash { s with cipher := cipher } ciphertext, ciphertext)

/-- Decrypt with the transcript as AAD, then hash the ciphertext, Noise §5.2. -/
def decryptAndHash (s : SymmetricState) (ciphertext : ByteArray) :
    Except NoiseError (SymmetricState × ByteArray) := do
  -- `plaintext = DecryptWithAd(h, ciphertext)`.
  let (cipher, plaintext) ← decryptWithAd s.cipher (packBytes s.hash.bytes) ciphertext
  -- `MixHash(ciphertext)`, then return the plaintext.
  return (mixHash { s with cipher := cipher } ciphertext, plaintext)

/-- Transport ciphers, ordered initiator-to-responder then responder-to-initiator, Noise §5. -/
def split (s : SymmetricState) : CipherState × CipherState :=
  -- `Split()`, step 1: `temp_k1, temp_k2 = HKDF(ck, zerolen, 2)`; step 2 truncates nothing here.
  let (first, second) := hkdf2 s.chainingKey .empty
  -- Steps 3 to 5: `c1.InitializeKey(temp_k1)`, `c2.InitializeKey(temp_k2)`, return `(c1, c2)`.
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
  -- Initialize, step 1: InitializeSymmetric of the protocol name; step 2: `MixHash(prologue)`.
  --
  -- Step 3 sets `initiator`, `s` and `e`, with `rs` and `re` empty, since XX has no pre-message.
  --
  -- EthLib takes the ephemeral key `e` here, as an input.
  --
  -- §5.3 instead sets `e`, which must be empty, to `GENERATE_KEYPAIR()` at the token `e`.
  --
  -- With the randomness as an input, every operation stays a pure function.
  --
  -- Step 4 hashes no pre-message key.
  --
  -- Step 5: EthLib keeps a message counter, whose 0 stands for the three patterns of XX.
  ⟨initiator, staticKey, ephemeralKey, none, none, 0, mixHash initializeSymmetric prologue⟩

/-- Read a required remote coordinate instead of substituting one, Noise §5.3. -/
def requireKey : Option Key → Except NoiseError Key
  | some key => .ok key
  -- Not in §5.3: a DH with an empty remote key is an error, never a DH with a default key.
  | none => .error .missingKey

/-- A decrypted static coordinate has exactly `DHLEN` bytes, Noise §5.3. -/
def readKey (bytes : ByteArray) : Except NoiseError Key :=
  -- `DHLEN = 32` for the 25519 DH functions, §12.1.
  exactBytes 32 bytes (.truncated 32)

/-- The next XX outgoing message, including its implicit payload, Noise §§5.3 and 7.5. -/
def writeMessage (s : HandshakeState) (payload : ByteArray) :
    Except NoiseError (HandshakeState × ByteArray) := do
  -- `WriteMessage`: fetch the next message pattern of XX, then process its tokens in order.
  let (symmetric, header) ← (match s.initiator, s.step with
    -- Message 1, `-> e`, written by the initiator.
    | true, 0 => do
      -- §3: the 32-byte key and the unencrypted payload fit in 65535 bytes.
      --
      -- EthLib checks the whole message before any token, so a failure changes no state.
      if payload.size + 32 > 65535 then throw (.messageTooLong (payload.size + 32))
      -- Token `e`: append the public key of `e`, then call MixHash on it.
      --
      -- The key pair `e` comes from initialization, not from `GENERATE_KEYPAIR()` here.
      let ephemeral := packBytes (X25519.publicKey s.ephemeralKey)
      return (mixHash s.symmetric ephemeral, ephemeral)
    -- Message 2, `<- e, ee, s, es`, written by the responder.
    | false, 1 => do
      -- §3: 32 key bytes, 48 for the encrypted static key and 16 for the tag of the payload.
      if payload.size + 96 > 65535 then throw (.messageTooLong (payload.size + 96))
      let remote ← requireKey s.remoteEphemeral
      -- Token `e`: append the public key of `e`, then call MixHash on it.
      let ephemeral := packBytes (X25519.publicKey s.ephemeralKey)
      -- Token `ee`: `MixKey(DH(e, re))`.
      let symmetric := mixKey (mixHash s.symmetric ephemeral) (X25519.x25519 s.ephemeralKey remote)
      -- Token `s`: append EncryptAndHash of the public key of `s`.
      let (symmetric, static) ← encryptAndHash symmetric (packBytes (X25519.publicKey s.staticKey))
      -- Token `es`, for the responder: `MixKey(DH(s, re))`.
      return (mixKey symmetric (X25519.x25519 s.staticKey remote), ephemeral ++ static)
    -- Message 3, `-> s, se`, written by the initiator.
    | true, 2 => do
      -- §3: 48 bytes for the encrypted static key and 16 for the tag of the payload.
      if payload.size + 64 > 65535 then throw (.messageTooLong (payload.size + 64))
      let remote ← requireKey s.remoteEphemeral
      -- Token `s`: append EncryptAndHash of the public key of `s`.
      let (symmetric, static) ← encryptAndHash s.symmetric
        (packBytes (X25519.publicKey s.staticKey))
      -- Token `se`, for the initiator: `MixKey(DH(s, re))`.
      return (mixKey symmetric (X25519.x25519 s.staticKey remote), static)
    -- No message pattern is left, or the next one is the other party's to write.
    | _, _ => throw (.wrongPhase s.initiator s.step)
    : Except NoiseError (SymmetricState × ByteArray))
  -- Append `EncryptAndHash(payload)`.
  let (symmetric, ciphertext) ← encryptAndHash symmetric payload
  -- The pattern is consumed; after message 3, the transport step calls `Split()`.
  return ({ s with symmetric := symmetric, step := s.step + 1 }, header ++ ciphertext)

/-- The next XX incoming message; each static key comes from its decrypted token, Noise §5.3. -/
def readMessage (s : HandshakeState) (message : ByteArray) :
    Except NoiseError (HandshakeState × ByteArray) := do
  -- §3: a handshake message has at most 65535 bytes.
  if message.size > 65535 then throw (.messageTooLong message.size)
  -- `ReadMessage`: fetch the next message pattern of XX, then process its tokens in order.
  let (s, remaining) ← (match s.initiator, s.step with
    -- Message 1, `-> e`, read by the responder.
    | false, 0 => do
      -- EthLib checks the 32 key bytes first, since §5.3 states no length check of its own.
      if h : 32 ≤ message.size then
        -- Token `e`: `re` is the next `DHLEN` bytes, then `MixHash(re)`.
        let remote := readBytes message 0 32 h
        return ({ s with
          remoteEphemeral := some remote
          symmetric := mixHash s.symmetric (packBytes remote) }, message.extract 32 message.size)
      else throw (.truncated 32 message.size)
    -- Message 2, `<- e, ee, s, es`, read by the initiator.
    | true, 1 => do
      -- 32 key bytes, 48 for the encrypted static key and 16 for the tag of the payload.
      --
      -- EthLib checks that minimum first, since §5.3 states no length check of its own.
      if h : 96 ≤ message.size then
        -- Token `e`: `re` is the next `DHLEN` bytes, then `MixHash(re)`.
        let remote := readBytes message 0 32 (by omega)
        -- Token `ee`: `MixKey(DH(e, re))`.
        let symmetric := mixKey (mixHash s.symmetric (packBytes remote))
          (X25519.x25519 s.ephemeralKey remote)
        -- Token `s`: `HasKey()` holds, so `temp` is the next `DHLEN + 16` bytes.
        --
        -- Then `rs = DecryptAndHash(temp)`.
        let (symmetric, staticBytes) ← decryptAndHash symmetric (message.extract 32 80)
        let static ← readKey staticBytes
        -- Token `es`, for the initiator: `MixKey(DH(e, rs))`.
        let symmetric := mixKey symmetric (X25519.x25519 s.ephemeralKey static)
        return ({ s with
          remoteEphemeral := some remote
          remoteStatic := some static
          symmetric := symmetric }, message.extract 80 message.size)
      else throw (.truncated 96 message.size)
    -- Message 3, `-> s, se`, read by the responder.
    | false, 2 => do
      -- 48 bytes for the encrypted static key and 16 for the tag of the payload, checked first.
      if 64 ≤ message.size then
        -- Token `s`: `temp` is the next `DHLEN + 16` bytes, then `rs = DecryptAndHash(temp)`.
        let (symmetric, staticBytes) ← decryptAndHash s.symmetric (message.extract 0 48)
        let static ← readKey staticBytes
        -- Token `se`, for the responder: `MixKey(DH(e, rs))`.
        let symmetric := mixKey symmetric (X25519.x25519 s.ephemeralKey static)
        return ({ s with remoteStatic := some static, symmetric := symmetric },
          message.extract 48 message.size)
      else throw (.truncated 64 message.size)
    -- No message pattern is left, or the next one is the other party's to read.
    | _, _ => throw (.wrongPhase s.initiator s.step)
    : Except NoiseError (HandshakeState × ByteArray))
  -- `DecryptAndHash()` on the remaining bytes of the message gives the payload.
  let (symmetric, payload) ← decryptAndHash s.symmetric remaining
  -- The pattern is consumed; after message 3, the transport step calls `Split()`.
  return ({ s with symmetric := symmetric, step := s.step + 1 }, payload)

/-- Return send and receive ciphers only after all three messages, Noise §§5.2 and 5.3. -/
def transport (s : HandshakeState) : Except NoiseError (CipherState × CipherState) :=
  -- §5.3: with no message pattern left, `Split()` returns the two transport ciphers.
  --
  -- EthLib calls it here, apart from the read or write of message 3.
  if s.step = 3 then
    -- §5: `c1` encrypts from initiator to responder, and `c2` the other way.
    let (forward, backward) := split s.symmetric
    -- So the initiator sends with `c1` and receives with `c2`, and the responder the reverse.
    .ok (if s.initiator then (forward, backward) else (backward, forward))
  else .error (.wrongPhase s.initiator s.step)

/-- Prefix a message with its 16-bit big-endian length, by the Wire Format of noise-libp2p. -/
def frame (message : ByteArray) : Except NoiseError ByteArray :=
  -- A Noise message has a maximum length of 65535 bytes.
  if message.size ≤ 65535 then
    -- The length field, a 16-bit big-endian unsigned integer in 2 bytes, then the message.
    .ok (⟨(natToBytes 2 message.size).toArray⟩ ++ message)
  else .error (.messageTooLong message.size)

/-- Decode exactly one complete frame, from the section Wire Format of noise-libp2p. -/
def unframe (bytes : ByteArray) : Except NoiseError ByteArray := do
  -- The length field: the first 2 bytes, a 16-bit big-endian unsigned integer.
  if h : 2 ≤ bytes.size then
    let size := bytesToNat (readBytes bytes 0 2 h).toList
    -- The message is the rest; EthLib reads one frame, so no byte may follow it.
    if size + 2 = bytes.size then return bytes.extract 2 bytes.size
    else throw (.frameLength size (bytes.size - 2))
  else throw (.truncated 2 bytes.size)

end EthLib.Networking.Noise
