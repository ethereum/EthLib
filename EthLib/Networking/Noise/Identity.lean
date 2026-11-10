module

public import EthLib.Networking.Noise
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Networking.Encoding.Varint

/-!
# The libp2p Noise identity payload

The secp256k1 profile and payload of [noise-libp2p, "The Noise Handshake"][libp2p].

Extensions stay opaque and are returned only when the handshake has completed.

Protobuf fields follow the [wire format][protobuf].

Repeated identity fields use the last value, and extension messages merge.

[libp2p]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md#the-noise-handshake
[protobuf]: https://protobuf.dev/programming-guides/encoding/
-/

@[expose] public section

namespace EthLib.Networking.Noise

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

/-- Read one protobuf varint and retain the suffix, with the 64-bit bound of the wire format. -/
def payloadVarint (bytes : List UInt8) : Except NoiseError (Nat × List UInt8) := do
  let result ← go 10 bytes
  if result.1 < 2 ^ 64 then return result else throw .protobuf
where
  go : Nat → List UInt8 → Except NoiseError (Nat × List UInt8)
    | 0, _ => .error .protobuf
    | _, [] => .error .protobuf
    | fuel + 1, byte :: rest => do
      if byte.toNat < 128 then return (byte.toNat, rest)
      let (high, rest) ← go fuel rest
      return (byte.toNat % 128 + 128 * high, rest)

/-- Read a bounded length-delimited field without accepting a truncated value. -/
def payloadBytes (bytes : List UInt8) : Except NoiseError (ByteArray × List UInt8) := do
  let (size, rest) ← payloadVarint bytes
  if size ≤ rest.length then return (⟨(rest.take size).toArray⟩, rest.drop size)
  else throw .protobuf

/-- Skip one nongroup field of an unknown protobuf field number. -/
def skipPayloadScalar (wire : Nat) (bytes : List UInt8) : Except NoiseError (List UInt8) := do
  match wire with
  | 0 => return (← payloadVarint bytes).2
  | 1 => if 8 ≤ bytes.length then return bytes.drop 8 else throw .protobuf
  | 2 => return (← payloadBytes bytes).2
  | 5 => if 4 ≤ bytes.length then return bytes.drop 4 else throw .protobuf
  | _ => throw .protobuf

/-- Skip an unknown group, checking matched end tags without parsing extension contents. -/
def skipPayloadGroup : Nat → List Nat → List UInt8 → Except NoiseError (List UInt8)
  | 0, _, _ => .error .protobuf
  | _, [], rest => .ok rest
  | fuel + 1, expected :: stack, bytes => do
    let (tag, rest) ← payloadVarint bytes
    let field := tag / 8
    let wire := tag % 8
    if field = 0 ∨ field ≥ 2 ^ 29 then throw .protobuf
    match wire with
    | 3 => skipPayloadGroup fuel (field :: expected :: stack) rest
    | 4 =>
      if field = expected then
        match stack with
        | [] => return rest
        | _ => skipPayloadGroup fuel stack rest
      else throw .protobuf
    | _ => skipPayloadGroup fuel (expected :: stack) (← skipPayloadScalar wire rest)

/-- Decode protobuf singular bytes by last value and merge extension messages by concatenation. -/
def decodePayload (bytes : ByteArray) : Except NoiseError Payload :=
  if bytes.size ≤ 65535 then go bytes.size bytes.data.toList {} else .error .messageTooLong
where
  go : Nat → List UInt8 → Payload → Except NoiseError Payload
    | _, [], payload => .ok payload
    | 0, _ :: _, _ => .error .protobuf
    | fuel + 1, bytes@(_ :: _), payload => do
      let (tag, rest) ← payloadVarint bytes
      let field := tag / 8
      let wire := tag % 8
      if field = 0 ∨ field ≥ 2 ^ 29 then throw .protobuf
      if wire = 2 ∧ (field = 1 ∨ field = 2 ∨ field = 4) then
        let (value, rest) ← payloadBytes rest
        let payload := if field = 1 then { payload with publicKey := value }
          else if field = 2 then { payload with signature := value }
          else { payload with extensions := some ((payload.extensions.getD .empty) ++ value) }
        go fuel rest payload
      else
        let rest ← if wire = 3 then skipPayloadGroup fuel [field] rest
          else skipPayloadScalar wire rest
        go fuel rest payload

/-- The error of a failure with the local identity secret.

Deriving the public key and signing fail only on an invalid secret or in ECDSA itself. -/
def identitySecretError : Libp2p.IdentityError → NoiseError
  | .signing error => .signing error
  | .privateKey | .publicKey | .peerId | .signature => .identitySecret

/-- Sign the Noise static public key with the secp256k1 identity secret.

The rule is noise-libp2p "Static Key Authentication" and "The libp2p Handshake Payload".

The secret key must stay private, and this function makes no constant-time claim. -/
def makePayload (identitySecret : Cryptography.Secp256k1.Fn) (staticKey : Key)
    (extensions : Option ByteArray) :
    Except NoiseError ByteArray := do
  let publicKey ← (Libp2p.publicKey identitySecret).mapError identitySecretError
  let signature ← (Libp2p.sign identitySecret (signedStatic staticKey)).mapError identitySecretError
  encodePayload ⟨publicKey, signature, extensions⟩

/-- Successful authentication carries the real signature check on this static coordinate. -/
structure AuthenticatedRemote (staticKey : Key) where
  publicKey : ByteArray
  /-- The secp256k1 point that the public key encodes. -/
  key : Cryptography.Secp256k1.Point
  /-- The public key decodes to that point. -/
  decoded : Libp2p.decodePublicKey publicKey = .ok key
  signature : ByteArray
  extensions : Option ByteArray
  verified : Libp2p.verify publicKey (signedStatic staticKey) signature = true

/-- Verify the decoded payload against the static key actually read from the encrypted token. -/
def authenticatePayload (staticKey : Key) (bytes : ByteArray) :
    Except NoiseError (AuthenticatedRemote staticKey) := do
  let p ← decodePayload bytes
  if h : Libp2p.verify p.publicKey (signedStatic staticKey) p.signature = true then
    match hk : Libp2p.decodePublicKey p.publicKey with
    | .ok key => return ⟨p.publicKey, key, hk, p.signature, p.extensions, h⟩
    -- A verified signature implies that the key decodes, so this branch never runs.
    | .error _ => throw .identity
  else throw .identity

/-- An authenticated remote key, derived peer ID, signature and opaque extensions. -/
abbrev RemoteInfo := ByteArray × ByteArray × ByteArray × Option ByteArray

/-- Project authenticated data to the public result, deriving the ID from the signing key. -/
def remoteInfo {staticKey : Key} (remote : AuthenticatedRemote staticKey) : RemoteInfo :=
  (remote.publicKey, Libp2p.peerId remote.key, remote.signature, remote.extensions)

/-- The XX state and the original encrypted remote message with its pre-read state. -/
structure Libp2pState where
  handshake : HandshakeState
  remoteMessage : Option (HandshakeState × ByteArray)

/-- Initialize the libp2p suite.

noise-libp2p sets no prologue, so this specification uses the empty one. -/
def initializeLibp2p (initiator : Bool) (staticKey ephemeralKey : Key) : Libp2pState :=
  ⟨initializeHandshake initiator staticKey ephemeralKey .empty, none⟩

/-- Finish only with a verified payload bound to the stored, decrypted remote static key. -/
def complete (s : Libp2pState) : Except NoiseError (Key × RemoteInfo) := do
  if s.handshake.step = 3 then
    let (before, message) ← match s.remoteMessage with
      | some value => pure value
      | none => throw .savedRemote
    if before.initiator = s.handshake.initiator ∧
        before.step = (if s.handshake.initiator then 1 else 2) then
      -- Reading succeeded once, so a failure now means the caller changed the saved message.
      let (received, payload) ← (readMessage before message).mapError fun _ => .savedRemote
      if received.step = (if s.handshake.initiator then 2 else 3) then
        let staticKey ← (requireKey received.remoteStatic).mapError fun _ => .savedRemote
        if s.handshake.remoteStatic = some staticKey then
          let authenticated ← (authenticatePayload staticKey payload).mapError fun _ => .savedRemote
          return (staticKey, remoteInfo authenticated)
        else throw .savedRemote
      else throw .savedRemote
    else throw .savedRemote
  else throw .wrongPhase

/-- Write a libp2p message; first-message extensions are forbidden by the payload rules. -/
def writeLibp2p (s : Libp2pState) (identitySecret : Cryptography.Secp256k1.Fn)
    (extensions : Option ByteArray) :
    Except NoiseError (Libp2pState × ByteArray) := do
  let payload ← if s.handshake.step = 0 then
      if extensions.isSome then throw .firstMessageExtensions else pure .empty
    else makePayload identitySecret (Cryptography.X25519.publicKey s.handshake.staticKey) extensions
  let (handshake, message) ← writeMessage s.handshake payload
  let next := { s with handshake := handshake }
  if handshake.step = 3 then
    let _ ← complete next
    return (next, message)
  else return (next, message)

/-- Read and authenticate the real static-key payload before accepting messages 2 and 3. -/
def readLibp2p (s : Libp2pState) (message : ByteArray) : Except NoiseError Libp2pState := do
  let (handshake, payload) ← readMessage s.handshake message
  if handshake.step = 1 then
    let first ← decodePayload payload
    if first.extensions.isSome then throw .firstMessageExtensions
    return { s with handshake := handshake }
  else
    let staticKey ← requireKey handshake.remoteStatic
    let _ ← authenticatePayload staticKey payload
    return ⟨handshake, some (s.handshake, message)⟩

end EthLib.Networking.Noise
