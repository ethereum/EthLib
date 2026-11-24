module

public import EthLib.Base.Exports.PyValue
public import EthLib.Cryptography.Exports.Secp256k1
public import EthLib.Networking.Rlpx.Frame

/-!
# `Exports.Rlpx`

C-ABI exports for RLPx, callable from the Python C extension.

A key, an iv or a nonce that the export rejects has code 0.

The other errors keep their codes: ECIES from 1 to 5, the handshake from 101, frames from 201.
-/

public section

namespace EthLib.Networking.Rlpx.Exports

open EthLib.Exports (ExportError Result PyValue UnreadArgument pyExport rejectArgument toResult)

open EthLib.Cryptography.Secp256k1

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def eciesMessage : Ecies.EciesError → String
  | .tooShort size => s!"ciphertext has {size} bytes, fewer than {Ecies.OVERHEAD}"
  | .invalidEphemeralKey e => s!"bad ephemeral public key: {e.message}"
  | .keyAgreement e => s!"key agreement failed: {e.message}"
  | .keyDerivation _ => "key derivation failed"
  | .tagMismatch => "tag does not match"

/-- A rejected ciphertext reaches Python with its code, and its message names the fault. -/
instance : ExportError Ecies.EciesError where
  code := Ecies.EciesError.code
  message := eciesMessage

/-- A private key of 32 big-endian bytes, or an error unless it is below `n`. -/
def readPrivateKey (bytes : ByteArray) : Result Fn :=
  toResult none (Cryptography.Secp256k1.Exports.readPrivateKey bytes
    (fun size => UnreadArgument.mk s!"bad private key size: {size}, expected 32")
    (UnreadArgument.mk "private key is not below n"))

/-- An encoded public key, in either SEC 1 encoding, or an error. -/
def readPublicKey (bytes : ByteArray) : Result Point :=
  match Point.decode bytes with
  | .ok p => pure p
  | .error e => rejectArgument none e.message

/-- A 16-byte initialization vector, or an error for any other length. -/
def readIv (bytes : ByteArray) : Result (Vector UInt8 16) :=
  toResult none (Base.exactBytes 16 bytes fun size =>
    UnreadArgument.mk s!"bad iv size: {size}, expected 16")

/-! ## ECIES -/

/-- The ECIES ciphertext of a message to a public key, with the given ephemeral key and iv. -/
@[export eth_rlpx_ecies_encrypt]
def eciesEncryptExport (recipient ephemeral iv sharedMac message : ByteArray) :
    Result ByteArray := do
  let q ← readPublicKey recipient
  let r ← readPrivateKey ephemeral
  let iv ← readIv iv
  toResult none (Ecies.encrypt q r iv sharedMac message)

/-- The message of an ECIES ciphertext, under a private key. -/
@[export eth_rlpx_ecies_decrypt]
def eciesDecryptExport (key sharedMac ciphertext : ByteArray) : Result ByteArray := do
  let k ← readPrivateKey key
  toResult none (Ecies.decrypt k sharedMac ciphertext)

/-! ## The handshake -/

/-- A message for a rejection of the handshake. -/
def handshakeMessage : HandshakeError → String
  | .ecies e => eciesMessage e
  | .tooLarge size => s!"encrypted message has {size} bytes, more than 65535"
  | .badSize size => s!"packet of {size} bytes does not match its size prefix"
  | .rlp _ => "message body is not an RLP list of the expected fields"
  | .secp256k1 e => e.message
  | .badRecoveryId id => s!"bad recovery id: {id}, expected 0 or 1"

/-- A rejected handshake reaches Python with its code, and its message names the fault. -/
instance : ExportError HandshakeError where
  code := HandshakeError.code
  message := handshakeMessage

/-- A 32-byte nonce, or an error for any other length. -/
def readNonce (bytes : ByteArray) : Result (Vector UInt8 32) :=
  toResult none (Base.exactBytes 32 bytes fun size =>
    UnreadArgument.mk s!"bad nonce size: {size}, expected 32")

/-- The keys of one side: a static key, an ephemeral key and a nonce. -/
def readKeys (staticKey ephemeralKey nonce : ByteArray) : Result Keys := do
  return ⟨← readPrivateKey staticKey, ← readPrivateKey ephemeralKey, ← readNonce nonce⟩

/-- The randomness of one encryption and the padding of the body. -/
def readSealing (r iv padding : ByteArray) : Result Sealing := do
  return ⟨← readPrivateKey r, ← readIv iv, padding⟩

/-- The bytes of the secrets: the AES secret, the MAC secret and two MAC digests, 32 bytes each. -/
def SECRETS_SIZE : Nat := 4 * 32

/-- The number of bytes of the secrets that the handshake exports return. -/
@[export eth_rlpx_const_secrets_size]
def constSecretsSize (_ : Unit) : UInt64 := UInt64.ofNat SECRETS_SIZE

/-- The 128 bytes of the secrets, with the digests of the MAC states after the probe. -/
def secretsBytes (secrets : Secrets) (probe : ByteArray) : ByteArray :=
  -- Each digest is the Keccak-256 digest of a MAC state after it absorbs the probe bytes.
  let digest (h : Cryptography.Hash.Keccak.Hasher256) := (h.absorb probe).digest.toArray
  -- The secrets of a session: aes-secret, mac-secret, then the two digests.
  ⟨secrets.aesSecret.toArray ++ secrets.macSecret.toArray ++ digest secrets.egressMac ++
    digest secrets.ingressMac⟩

/-- The packet `auth` from the initiator to the recipient's public key. -/
@[export eth_rlpx_make_auth]
def makeAuthExport (staticKey ephemeralKey nonce recipient r iv padding : ByteArray) :
    Result ByteArray := do
  let keys ← readKeys staticKey ephemeralKey nonce
  let q ← readPublicKey recipient
  toResult none (makeAuth keys q (← readSealing r iv padding))

/-- The recipient's answer to `auth`: the packet `ack`, and the 128 bytes of its secrets. -/
def respondOf (args : ByteArray × ByteArray × ByteArray × ByteArray × ByteArray × ByteArray ×
    ByteArray × ByteArray) : Result (ByteArray × ByteArray) := do
  let (staticKey, ephemeralKey, nonce, r, iv, padding, auth, probe) := args
  let keys ← readKeys staticKey ephemeralKey nonce
  let (ack, secrets) ← toResult none (respond keys (← readSealing r iv padding) auth)
  return (ack, secretsBytes secrets probe)

/-- The recipient's answer to `auth`: the packet `ack`, and the 128 bytes of its secrets.

The arguments are the static key, the ephemeral key, the nonce, `r`, the IV and the padding.

Last come the packet `auth` and the probe that the MAC digests read after. -/
@[export eth_rlpx_respond]
def respondExport (args : PyValue) : Result PyValue :=
  pyExport respondOf args

/-- The recipient's secrets for an `auth` it received and an `ack` it sent. -/
@[export eth_rlpx_recipient_secrets]
def recipientSecretsExport (staticKey ephemeralKey nonce auth ack probe : ByteArray) :
    Result ByteArray := do
  let keys ← readKeys staticKey ephemeralKey nonce
  let (msg, _, remoteEphemeral) ← toResult none (readAuth keys.staticKey auth)
  let shared ←
    toResult none ((ecdh keys.ephemeralKey remoteEphemeral).mapError HandshakeError.secp256k1)
  return secretsBytes (deriveSecrets false shared msg.initiatorNonce keys.nonce auth ack) probe

/-- The initiator's secrets for its `auth` and the `ack` it received. -/
@[export eth_rlpx_finish]
def finishExport (staticKey ephemeralKey nonce auth ack probe : ByteArray) :
    Result ByteArray := do
  let keys ← readKeys staticKey ephemeralKey nonce
  return secretsBytes (← toResult none (finish keys auth ack)) probe

/-! ## Frames -/

/-- A message for a rejected frame. -/
def frameMessage : FrameError → String
  | .tooLarge size => s!"frame data has {size} bytes, more than 2^24 - 1"
  | .tooShort needed available => s!"input has {available} bytes, fewer than {needed}"
  | .headerMacMismatch => "header MAC does not match"
  | .frameMacMismatch => "frame MAC does not match"

/-- A rejected frame reaches Python with its code, and its message names the fault. -/
instance : ExportError FrameError where
  code := FrameError.code
  message := frameMessage

/-- A 32-byte secret as an AES-256 key, or an error for any other length. -/
def readSecret (bytes : ByteArray) : Result (Cryptography.Aes.Key .aes256) :=
  toResult none (Base.exactBytes 32 bytes fun size =>
    UnreadArgument.mk s!"bad secret size: {size}, expected 32")

/-- The state of one direction at its start: the zero counter, and the MAC after `macInit`. -/
def readFrameState (aesSecret macSecret macInit : ByteArray) : Result FrameState := do
  return ⟨← readSecret aesSecret, Vector.replicate 16 0, ← readSecret macSecret,
    Cryptography.Hash.Keccak.Hasher256.empty.absorb macInit⟩

/-- The frames of a list of frame data, one after another in one direction. -/
def writeFrames (st : FrameState) : List ByteArray → Except FrameError ByteArray
  | [] => .ok .empty
  | data :: rest => do
    let (frame, st) ← writeFrame st data
    return frame ++ (← writeFrames st rest)

/-- The frame data of the frames that fill `input`, one after another in one direction.

Each frame takes at least 32 bytes, so `fuel` frames cover an input of `fuel` bytes. -/
def readFrames : Nat → FrameState → ByteArray → Except FrameError (List ByteArray)
  | fuel + 1, st, input =>
    if input.size = 0 then .ok [] else do
      let (data, st, rest) ← readFrame st input
      return data :: (← readFrames fuel st rest)
  | 0, _, input => if input.size = 0 then .ok [] else .error (.tooShort 32 input.size)

/-- The frames of the frame data in the RLP list `frames`, from the start of a direction.

The direction starts at the zero counter, with its MAC state after the bytes `macInit`. -/
@[export eth_rlpx_write_frames]
def writeFramesExport (aesSecret macSecret macInit frames : ByteArray) : Result ByteArray := do
  let st ← readFrameState aesSecret macSecret macInit
  let datas ← match Serialization.Rlp.Codec.decode (α := List ByteArray) frames with
    | .ok datas => pure datas
    | .error _ => rejectArgument none "frames is not an RLP list of byte strings"
  toResult none (writeFrames st datas)

/-- The frame data of the frames in `input`, as an RLP list, from the start of a direction.

The input must hold whole frames only. -/
@[export eth_rlpx_read_frames]
def readFramesExport (aesSecret macSecret macInit input : ByteArray) : Result ByteArray := do
  let st ← readFrameState aesSecret macSecret macInit
  let datas ← toResult none (readFrames input.size st input)
  match Serialization.Rlp.Codec.encode datas with
  | .ok bytes => pure bytes
  | .error _ => rejectArgument none "frame data does not fit in RLP"

end EthLib.Networking.Rlpx.Exports
