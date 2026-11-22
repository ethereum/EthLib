module

public import EthLib.Networking.Noise
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Networking.Encoding.Protobuf

/-!
# The libp2p Noise identity payload

The secp256k1 profile and payload of the section The Noise Handshake of [noise-libp2p][libp2p].

Extensions stay opaque.

The state keeps them from the read of message 2 or 3, and completion returns them.

Other libp2p components should see them only after completion.

That is the rule of the section libp2p Data in Handshake Messages of noise-libp2p.

Protobuf fields follow the [wire format][protobuf].

[libp2p]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/noise/README.md#the-noise-handshake
[protobuf]: https://protobuf.dev/programming-guides/encoding/
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Cryptography.Secp256k1 (Fn)

/-- The two identity fields and optional opaque extension message of the libp2p payload. -/
structure Payload where
  publicKey : ByteArray := .empty
  signature : ByteArray := .empty
  extensions : Option ByteArray := none

/-- The bytes that the identity key signs: a domain prefix, then the Noise static public key.

The rule is in the section The libp2p Handshake Payload of noise-libp2p. -/
def signedStatic (staticKey : Key) : ByteArray :=
  -- The UTF-8 string `noise-libp2p-static-key:`, then the static public key.
  --
  -- That key is encoded by RFC 7748 §5, as its 32 bytes.
  "noise-libp2p-static-key:".toUTF8 ++ EthLib.Base.packBytes staticKey

/-- Serialize the payload, from the section The libp2p Handshake Payload of noise-libp2p. -/
def encodePayload (p : Payload) : Except NoiseError ByteArray := do
  -- The encoding is at least as long as its fields, so fields over 65535 bytes fail early.
  --
  -- That bound is EthLib's: it rejects the payload before it builds the encoding.
  let fields := p.publicKey.size + p.signature.size + (p.extensions.map ByteArray.size).getD 0
  if fields > 65535 then throw (.messageTooLong fields)
  -- The optional extensions field, number 4, only when the payload has extensions.
  let extension := match p.extensions with
    | none => []
    | some value => [⟨4, .len value⟩]
  -- The identity key, field 1, then the identity signature, field 2, as length-delimited bytes.
  --
  -- EthLib always writes both, in field order.
  let encoded := Encoding.Protobuf.serialize
    (⟨1, .len p.publicKey⟩ :: ⟨2, .len p.signature⟩ :: extension)
  -- The payload must fit in one Noise message of at most 65535 bytes.
  if encoded.size ≤ 65535 then return encoded else throw (.messageTooLong encoded.size)

/-- Decode protobuf singular bytes by last value and merge extension messages by concatenation. -/
def decodePayload (bytes : ByteArray) : Except NoiseError Payload := do
  -- A payload comes from one Noise message, so it has at most 65535 bytes.
  if 65535 < bytes.size then throw (.messageTooLong bytes.size)
  -- The records of the protobuf wire format; a malformed record fails the whole payload.
  let records ← (Encoding.Protobuf.records bytes.data.toList).mapError fun _ => .protobuf
  return records.foldl (init := {}) fun payload record =>
    match record with
    -- The identity key and the identity signature: a field seen twice keeps its last value.
    | ⟨1, .len value⟩ => { payload with publicKey := value }
    | ⟨2, .len value⟩ => { payload with signature := value }
    -- The extensions message: repeated instances merge, as their concatenation parses.
    | ⟨4, .len value⟩ =>
      { payload with extensions := some (payload.extensions.getD .empty ++ value) }
    -- Any other field number or wire type is skipped, as an unknown field.
    | _ => payload

/-- The error of a failure with the local identity secret.

Deriving the public key and signing fail only on an invalid secret or in ECDSA itself. -/
def identitySecretError : Libp2p.IdentityError → NoiseError
  -- ECDSA itself failed.
  | .signing error => .signing error
  -- Any other failure comes from the secret.
  | .privateKey | .publicKey | .peerId _ | .signature => .identitySecret

/-- Sign the Noise static public key with the secp256k1 identity secret.

The rule is in the noise-libp2p sections Static Key Authentication and The libp2p Handshake Payload.

The secret key must stay private, and this function makes no constant-time claim. -/
def makePayload (identitySecret : Fn) (staticKey : Key)
    (extensions : Option ByteArray) :
    Except NoiseError ByteArray := do
  -- The identity key field holds the serialized public key of the peer-IDs specification.
  let publicKey ← (Libp2p.publicKey identitySecret).mapError identitySecretError
  -- The identity signature: the identity private key signs the prefixed static key.
  --
  -- It follows the signing rules of the peer-IDs specification.
  let signature ← (Libp2p.sign identitySecret (signedStatic staticKey)).mapError identitySecretError
  -- The extensions go in the payload as they are, without alteration.
  encodePayload ⟨publicKey, signature, extensions⟩

/-- The authenticated remote: its Noise static key and the identity that signed it.

The identity key is kept as a point, whose canonical protobuf is the public key. -/
structure Remote where
  /-- The static public key that the remote's encrypted token carries. -/
  staticKey : Key
  /-- The secp256k1 identity key of the payload. -/
  key : Cryptography.Secp256k1.Point
  /-- The DER signature by that key over the prefixed static key. -/
  signature : ByteArray
  /-- The opaque libp2p extensions of the payload, if any. -/
  extensions : Option ByteArray

/-- The protobuf of the identity key, peer-IDs "Keys". -/
def Remote.publicKey (remote : Remote) : ByteArray := Libp2p.encodePublicKey remote.key

/-- Decode a payload, and verify it against the static key read from the encrypted token.

The rule is in the section The libp2p Handshake Payload of noise-libp2p. -/
def authenticatePayload (staticKey : Key) (bytes : ByteArray) : Except NoiseError Remote := do
  let p ← decodePayload bytes
  -- Decode the public key from the identity key field into a usable form.
  --
  -- Then validate the identity signature against the static Noise key of the handshake.
  --
  -- EthLib verifies first, and that check decodes the key itself.
  if Libp2p.verify p.publicKey (signedStatic staticKey) p.signature then
    match Libp2p.decodePublicKey p.publicKey with
    | .ok key => return ⟨staticKey, key, p.signature, p.extensions⟩
    -- A verified signature implies that the key decodes, so this branch never runs.
    | .error _ => throw .identity
  -- An invalid signature: the connection MUST be terminated immediately.
  else throw .identity

/-- The XX state, and the remote once the message that carries its static key is read. -/
structure Libp2pState where
  handshake : HandshakeState
  remote : Option Remote

/-- Initialize the libp2p suite.

noise-libp2p sets no prologue, so this specification uses the empty one. -/
def initializeLibp2p (initiator : Bool) (staticKey ephemeralKey : Key) : Libp2pState :=
  -- The pattern XX, under the protocol name Noise_XX_25519_ChaChaPoly_SHA256.
  ⟨initializeHandshake initiator staticKey ephemeralKey .empty, none⟩

/-- The authenticated remote and the send and receive ciphers, after all three messages.

Completion reads no message: the read of message 2 or 3 stored the remote.

It checks that the remote has the remote static key of the handshake. -/
def complete (s : Libp2pState) : Except NoiseError (Remote × CipherState × CipherState) := do
  -- After the three messages, two cipher states: one to send, one to receive.
  let (send, receive) ← transport s.handshake
  match s.remote with
  | some remote =>
    -- The remote was authenticated for the static key of this handshake.
    --
    -- Its extensions reach other libp2p components only now, after completion.
    if s.handshake.remoteStatic = some remote.staticKey then return (remote, send, receive)
    else throw .savedRemote
  | none => throw .savedRemote

/-- Write a libp2p message; first-message extensions are forbidden by the payload rules.

The identity secret must be nonzero, and it is checked first, on every message.

That check is a precondition of this specification; noise-libp2p puts no identity in message 1.

The secret key must stay private, and this function makes no constant-time claim. -/
def writeLibp2p (s : Libp2pState) (identitySecret : Fn)
    (extensions : Option ByteArray) :
    Except NoiseError (Libp2pState × ByteArray) := do
  -- EthLib's precondition: a nonzero identity secret, on every message.
  if identitySecret = 0 then throw .identitySecret
  -- Message 1: the initiator MUST NOT send extensions in its first message.
  --
  -- EthLib sends an empty payload: only messages 2 and 3 carry the handshake payload.
  let payload ← if s.handshake.step = 0 then
      if extensions.isSome then throw .firstMessageExtensions else pure .empty
    -- Messages 2 and 3: the payload signs the sender's own static public key.
    else makePayload identitySecret (Cryptography.X25519.publicKey s.handshake.staticKey) extensions
  -- The XX message that carries the payload.
  let (handshake, message) ← writeMessage s.handshake payload
  return ({ s with handshake := handshake }, message)

/-- Read a message, and authenticate the static key that message 2 or 3 carries.

The first message carries no static key, so it leaves no remote. -/
def readLibp2p (s : Libp2pState) (message : ByteArray) : Except NoiseError Libp2pState := do
  let (handshake, payload) ← readMessage s.handshake message
  -- Message 1 carries no identity.
  if handshake.step = 1 then
    -- The receiving side of the rule that message 1 carries no extensions.
    --
    -- EthLib reads its payload as a protobuf and rejects extensions there.
    let first ← decodePayload payload
    if first.extensions.isSome then throw .firstMessageExtensions
    return ⟨handshake, none⟩
  else
    -- Messages 2 and 3: the payload is checked against the static key received in the handshake.
    let staticKey ← requireKey handshake.remoteStatic
    return ⟨handshake, some (← authenticatePayload staticKey payload)⟩

end EthLib.Networking.Noise
