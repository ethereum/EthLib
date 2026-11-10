module

public import EthLib.Networking.Noise
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Networking.Encoding.Protobuf

/-!
# The libp2p Noise identity payload

The secp256k1 profile and payload of [noise-libp2p, "The Noise Handshake"][libp2p].

Extensions stay opaque.

The state keeps them from the read of message 2 or 3, and completion returns them.

Other libp2p components should see them only after completion.

That is the rule of noise-libp2p "libp2p Data in Handshake Messages".

Protobuf fields follow the [wire format][protobuf].

Repeated identity fields use the last value, and extension messages merge.

[libp2p]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md#the-noise-handshake
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

The rule is noise-libp2p "The libp2p Handshake Payload". -/
def signedStatic (staticKey : Key) : ByteArray :=
  "noise-libp2p-static-key:".toUTF8 ++ EthLib.Base.packBytes staticKey

/-- A length-delimited protobuf field: its tag byte, varint length and value. -/
def payloadField (tag : UInt8) (value : ByteArray) : ByteArray :=
  ⟨#[tag]⟩ ++ ⟨(Encoding.Varint.encode value.size.toUInt64).toArray⟩ ++ value

/-- Serialize the payload, noise-libp2p "The libp2p Handshake Payload". -/
def encodePayload (p : Payload) : Except NoiseError ByteArray := do
  if p.publicKey.size + p.signature.size +
      (p.extensions.map ByteArray.size).getD 0 > 65535 then throw .messageTooLong
  let extension := match p.extensions with
    | none => .empty
    | some value => payloadField 0x22 value
  let encoded := payloadField 0x0a p.publicKey ++ payloadField 0x12 p.signature ++ extension
  if encoded.size ≤ 65535 then return encoded else throw .messageTooLong

/-- Decode protobuf singular bytes by last value and merge extension messages by concatenation. -/
def decodePayload (bytes : ByteArray) : Except NoiseError Payload :=
  if bytes.size ≤ 65535 then go bytes.size bytes.data.toList {} else .error .messageTooLong
where
  go : Nat → List UInt8 → Payload → Except NoiseError Payload
    | _, [], payload => .ok payload
    | 0, _ :: _, _ => .error .protobuf
    | fuel + 1, bytes@(_ :: _), payload => do
      let (record, rest) ← (Encoding.Protobuf.readRecord fuel bytes).mapError fun _ => .protobuf
      let payload := match record with
        | ⟨1, .len value⟩ => { payload with publicKey := ⟨value.toArray⟩ }
        | ⟨2, .len value⟩ => { payload with signature := ⟨value.toArray⟩ }
        | ⟨4, .len value⟩ =>
          { payload with extensions := some ((payload.extensions.getD .empty) ++ ⟨value.toArray⟩) }
        | _ => payload
      go fuel rest payload

/-- The error of a failure with the local identity secret.

Deriving the public key and signing fail only on an invalid secret or in ECDSA itself. -/
def identitySecretError : Libp2p.IdentityError → NoiseError
  | .signing error => .signing error
  | .privateKey | .publicKey | .peerId | .signature => .identitySecret

/-- Sign the Noise static public key with the secp256k1 identity secret.

The rule is noise-libp2p "Static Key Authentication" and "The libp2p Handshake Payload".

The secret key must stay private, and this function makes no constant-time claim. -/
def makePayload (identitySecret : Fn) (staticKey : Key)
    (extensions : Option ByteArray) :
    Except NoiseError ByteArray := do
  let publicKey ← (Libp2p.publicKey identitySecret).mapError identitySecretError
  let signature ← (Libp2p.sign identitySecret (signedStatic staticKey)).mapError identitySecretError
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

The rule is noise-libp2p "The libp2p Handshake Payload". -/
def authenticatePayload (staticKey : Key) (bytes : ByteArray) : Except NoiseError Remote := do
  let p ← decodePayload bytes
  if Libp2p.verify p.publicKey (signedStatic staticKey) p.signature then
    match Libp2p.decodePublicKey p.publicKey with
    | .ok key => return ⟨staticKey, key, p.signature, p.extensions⟩
    -- A verified signature implies that the key decodes, so this branch never runs.
    | .error _ => throw .identity
  else throw .identity

/-- The XX state, and the remote once the message that carries its static key is read. -/
structure Libp2pState where
  handshake : HandshakeState
  remote : Option Remote

/-- Initialize the libp2p suite.

noise-libp2p sets no prologue, so this specification uses the empty one. -/
def initializeLibp2p (initiator : Bool) (staticKey ephemeralKey : Key) : Libp2pState :=
  ⟨initializeHandshake initiator staticKey ephemeralKey .empty, none⟩

/-- The authenticated remote and the send and receive ciphers, after all three messages.

Completion reads no message: the read of message 2 or 3 stored the remote.

It checks that the remote has the remote static key of the handshake. -/
def complete (s : Libp2pState) : Except NoiseError (Remote × CipherState × CipherState) := do
  let (send, receive) ← transport s.handshake
  match s.remote with
  | some remote =>
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
  if identitySecret = 0 then throw .identitySecret
  let payload ← if s.handshake.step = 0 then
      if extensions.isSome then throw .firstMessageExtensions else pure .empty
    else makePayload identitySecret (Cryptography.X25519.publicKey s.handshake.staticKey) extensions
  let (handshake, message) ← writeMessage s.handshake payload
  return ({ s with handshake := handshake }, message)

/-- Read a message, and authenticate the static key that message 2 or 3 carries.

The first message carries no static key, so it leaves no remote. -/
def readLibp2p (s : Libp2pState) (message : ByteArray) : Except NoiseError Libp2pState := do
  let (handshake, payload) ← readMessage s.handshake message
  if handshake.step = 1 then
    let first ← decodePayload payload
    if first.extensions.isSome then throw .firstMessageExtensions
    return ⟨handshake, none⟩
  else
    let staticKey ← requireKey handshake.remoteStatic
    return ⟨handshake, some (← authenticatePayload staticKey payload)⟩

end EthLib.Networking.Noise
