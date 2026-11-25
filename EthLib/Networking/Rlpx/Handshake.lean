module

public import EthLib.Base.ByteOrder
public import EthLib.Networking.Rlpx.Ecies
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Secp256k1.Sign
public import EthLib.Cryptography.Ecdsa.Encoding
public import EthLib.Serialization.Rlp.Codec

/-!
# `Networking.Rlpx.Handshake`

The handshake of RLPx, from the section "Initial Handshake" of [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/rlpx.md#initial-handshake

The initiator sends `auth`, and the recipient answers with `ack`.

Each message is an RLP list encrypted with ECIES, as "Specification" of [EIP-8][eip8] fixes it.

[eip8]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8.md

EthLib reads only this form, and rejects the older fixed-size form of `auth` and `ack`.

Both sides then derive the secrets of the session from the two ephemeral keys and the nonces.

The keys and the nonces are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Networking.Rlpx

open EthLib.Base (xorBytes)
open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Serialization.Rlp

/-- Every way the handshake can reject its input. -/
inductive HandshakeError where
  /-- The encryption or the decryption of a message failed. -/
  | ecies (error : Ecies.EciesError)
  /-- The encrypted message had `size` bytes, more than a 16-bit size can give. -/
  | tooLarge (size : Nat)
  /-- The packet had no 2-byte size, or its size was not the number of bytes after it. -/
  | badSize (actual : Nat)
  /-- The body of a message was not an RLP list of the fields it needs. -/
  | rlp (error : RlpError)
  /-- A public key, a key agreement or a signature failed. -/
  | secp256k1 (error : Secp256k1Error)
  /-- The recovery id of the signature was not 0 or 1. -/
  | badRecoveryId (id : UInt8)
deriving DecidableEq, Repr

/--
The stable code of an error, for the C exports.

An ECIES failure keeps the code of its ECIES error, from 1 to 5.

The other constructors take the codes from 101, so no two constructors share a code.
-/
def HandshakeError.code : HandshakeError → UInt32
  | .ecies e => e.code
  | .tooLarge _ => 101
  | .badSize _ => 102
  | .rlp _ => 103
  | .secp256k1 _ => 104
  | .badRecoveryId _ => 105

/-- The version of the handshake messages, `auth-vsn` and `ack-vsn`. -/
def HANDSHAKE_VERSION : Nat := 4

/-! ## Public keys -/

/-- A public key as the 64 bytes `x || y`, the uncompressed form of SEC 1 without its prefix. -/
def encodePublicKey : Point → Vector UInt8 64
  -- No key pair has the point at infinity as its public key.
  --
  -- EthLib writes it as 64 zero bytes: `(0, 0)` is off the curve, so no decoder accepts it.
  | .infinity => Vector.replicate 64 0
  -- `x || y`, each coordinate in 32 big-endian bytes.
  | .affine x y => ⟨(x.toBytes ++ y.toBytes).toArray, by simp [Fp.length_toBytes]⟩

/-- The public key of 64 bytes `x || y`, which must lie on the curve. -/
def decodePublicKey (bytes : Vector UInt8 64) : Except HandshakeError Point :=
  -- `0x04 || x || y` is the uncompressed form of SEC 1 v2 §2.3.4, which the decoder checks.
  (Point.decode ⟨#[0x04] ++ bytes.toArray⟩).mapError .secp256k1

/-! ## Messages -/

/-- The body of `auth`: `[sig, initiator-pubk, initiator-nonce, auth-vsn, ...]`. -/
structure AuthMessage where
  /-- The signature `r || s || v` of the initiator's ephemeral key, with the recovery id `v`. -/
  signature : Vector UInt8 65
  /-- The initiator's static public key. -/
  initiatorPubkey : Vector UInt8 64
  /-- The initiator's nonce. -/
  initiatorNonce : Vector UInt8 32
  /-- `auth-vsn`, which the recipient ignores. -/
  version : Nat
deriving DecidableEq

/-- The body of `ack`: `[recipient-ephemeral-pubk, recipient-nonce, ack-vsn, ...]`. -/
structure AckMessage where
  /-- The recipient's ephemeral public key. -/
  ephemeralPubkey : Vector UInt8 64
  /-- The recipient's nonce. -/
  recipientNonce : Vector UInt8 32
  /-- `ack-vsn`, which the initiator ignores. -/
  version : Nat
deriving DecidableEq

/--
The fields of a message: a list of at least `count` items, of which the first `count` are kept.
-/
def leadingFields (count : Nat) (item : Item) : Except RlpError (List Item) := do
  -- The body is an RLP list.
  let items ← item.toItems
  -- Implementations must ignore any additional list elements in `auth-body` and `ack-body`.
  if count ≤ items.length then .ok (items.take count)
  -- A list with fewer items than the message has fields fails.
  else .error (.wrongFieldCount count items.length)

/-- `auth` as an RLP list of four items. -/
instance : Codec AuthMessage where
  -- `auth-body = [sig, initiator-pubk, initiator-nonce, auth-vsn, ...]`.
  --
  -- EthLib writes no further element.
  toItem m := .list [Codec.toItem m.signature, Codec.toItem m.initiatorPubkey,
    Codec.toItem m.initiatorNonce, Codec.toItem m.version]
  ofItem item := do
    match ← leadingFields 4 item with
    -- Implementations must ignore any mismatches in `auth-vsn`, so any version is read.
    | [s, p, n, v] =>
      return ⟨← Codec.ofItem s, ← Codec.ofItem p, ← Codec.ofItem n, ← Codec.ofItem v⟩
    | items => throw (RlpError.wrongFieldCount 4 items.length)

/-- `ack` as an RLP list of three items. -/
instance : Codec AckMessage where
  -- `ack-body = [recipient-ephemeral-pubk, recipient-nonce, ack-vsn, ...]`.
  --
  -- EthLib writes no further element.
  toItem m := .list [Codec.toItem m.ephemeralPubkey, Codec.toItem m.recipientNonce,
    Codec.toItem m.version]
  ofItem item := do
    match ← leadingFields 3 item with
    -- Implementations must ignore any mismatches in `ack-vsn`, so any version is read.
    | [p, n, v] => return ⟨← Codec.ofItem p, ← Codec.ofItem n, ← Codec.ofItem v⟩
    | items => throw (RlpError.wrongFieldCount 3 items.length)

/-- The message at the start of a decrypted body. -/
def decodeBody {α : Type} [Codec α] (body : ByteArray) : Except HandshakeError α :=
  -- EIP-8: decoding the RLP data should ignore any trailing data after the list.
  --
  -- So only the first item is read, and the bytes after it, the padding, are dropped.
  (do Codec.ofItem (← decodeItem body 0 body.size).1).mapError .rlp

/-! ## Packets -/

/-- `size` as two big-endian bytes. -/
def sizeBytes (size : Nat) : ByteArray := ⟨(Base.ByteOrder.toBE 2 size).toArray⟩

/-- The packet `size || ecies.encrypt(recipient, body || padding, size)`. -/
def sealPacket (recipient : Point) (r : Fn) (iv : Aes.Block) (body padding : ByteArray) :
    Except HandshakeError ByteArray := do
  -- `auth-size` is the size of `enc-auth-body`, and `ack-size` the size of `enc-ack-body`.
  --
  -- It is the size of the plaintext plus the fixed overhead of ECIES.
  --
  -- The overhead is `R`, `iv` and `d`: 65 + 16 + 32 = 113 bytes.
  let size := body.size + padding.size + Ecies.OVERHEAD
  -- `auth-size` is a big-endian 16-bit integer, so a larger size fails.
  if 2 ^ 16 ≤ size then throw (.tooLarge size)
  -- `enc-auth-body = ecies.encrypt(recipient-pubk, auth-body || auth-padding, auth-size)`.
  --
  -- The size is the AUTHDATA of ECIES, so the tag authenticates it.
  --
  -- EIP-8 asks for at least 100 bytes of padding; EthLib takes the padding the caller gives.
  let ciphertext ← (Ecies.encrypt recipient r iv (sizeBytes size) (body ++ padding)).mapError .ecies
  -- `auth = auth-size || enc-auth-body`, and the same for `ack`.
  return sizeBytes size ++ ciphertext

/-- The decrypted body of a packet: its size must count the bytes after it. -/
def openPacket (key : Fn) (packet : ByteArray) : Except HandshakeError ByteArray :=
  match packet.data.toList with
  -- `auth = auth-size || enc-auth-body`, with `auth-size` in 2 big-endian bytes.
  | hi :: lo :: rest =>
    -- EthLib takes one whole packet, so `auth-size` must count exactly the bytes after it.
    if Base.ByteOrder.ofBE [hi, lo] = rest.length then
      -- The inverse of `ecies.encrypt(recipient-pubk, auth-body || auth-padding, auth-size)`.
      --
      -- It checks the tag over `auth-size` before it decrypts.
      (Ecies.decrypt key ⟨#[hi, lo]⟩ ⟨rest.toArray⟩).mapError .ecies
    else .error (.badSize packet.size)
  -- Fewer than the 2 bytes of the size.
  | _ => .error (.badSize packet.size)

/-! ## The two sides -/

/-- The secret inputs of one side: its static key, its ephemeral key and its nonce. -/
structure Keys where
  /-- The static private key. -/
  staticKey : Fn
  /-- The ephemeral private key of this connection. -/
  ephemeralKey : Fn
  /-- The nonce of this connection. -/
  nonce : Vector UInt8 32

/-- The randomness of one ECIES encryption, and the padding of the body. -/
structure Sealing where
  /-- The ephemeral key `r` of ECIES. -/
  r : Fn
  /-- The `iv` of ECIES. -/
  iv : Aes.Block
  /-- The bytes after the RLP list, which EIP-8 asks to vary in length. -/
  padding : ByteArray

/-- The signature `r || s || v` of a hash, where `v` is the recovery id. -/
def signatureBytes (sig : Fn × Fn × Bool) : Vector UInt8 65 :=
  -- `r` and `s` in 32 big-endian bytes each, then `v`: 1 when the `y` of `R` is odd, else 0.
  Cryptography.Ecdsa.toRecoverableBytes sig.1.val sig.2.1.val sig.2.2

/-- The public key that signed a hash, from a signature `r || s || v`. -/
def recoverSigner (hash : Vector UInt8 32) (sig : Vector UInt8 65) : Except HandshakeError Point :=
  -- `r` and `s` are the first 64 bytes, and `v` is the last byte.
  let (r, s) := Cryptography.Ecdsa.toNats (sig.take Cryptography.Ecdsa.SIGNATURE_LEN)
  let v := sig[64]
  -- No source bounds `v`, and EthLib takes only the recovery ids 0 and 1, as a signer writes.
  if h : v.toNat < 2 then (Ecdsa.recover hash r s ⟨v.toNat, h⟩).mapError .secp256k1
  else .error (.badRecoveryId v)

/--
The packet `auth` of the initiator to the recipient with the static key `recipient`.

The pinned `rlpx.md` does not define `sig`, so the rule comes from its revision [`6504d41`][old].

[old]: https://github.com/ethereum/devp2p/blob/6504d410bc4b8dda2b43941e1cb48c804b90cf22/rlpx.md#handshake
-/
def makeAuth (keys : Keys) (recipient : Point) (sealing : Sealing) :
    Except HandshakeError ByteArray := do
  -- `static-shared-secret = ecdh.agree(privkey, remote-pubk)`.
  let shared ← (ecdh keys.staticKey recipient).mapError .secp256k1
  -- `sig = S(ephemeral-privk, static-shared-secret ^ nonce)`, in revision `6504d41`.
  --
  -- There `nonce` is the nonce of the initiator, which signs.
  --
  -- The signature is `r || s || v`, in the low-s form, with the recovery id `v`.
  let sig ← (Ecdsa.sign keys.ephemeralKey (xorBytes shared keys.nonce)).mapError .secp256k1
  -- `auth-body = [sig, initiator-pubk, initiator-nonce, auth-vsn]`, with `auth-vsn = 4`.
  --
  -- `initiator-pubk` is the static public key `privkey * G`.
  let auth : AuthMessage := ⟨signatureBytes sig,
    encodePublicKey (Point.mul keys.staticKey .generator), keys.nonce, HANDSHAKE_VERSION⟩
  let body ← (Codec.encode auth).mapError .rlp
  -- Step 1: the initiator sends `auth = auth-size || enc-auth-body`.
  sealPacket recipient sealing.r sealing.iv body sealing.padding

/--
What the recipient learns from `auth`: the message and two public keys of the initiator.

The first is its static key, and the second is the ephemeral key that the signature names.
-/
def readAuth (staticKey : Fn) (packet : ByteArray) :
    Except HandshakeError (AuthMessage × Point × Point) := do
  -- Step 2: the recipient decrypts `auth` with its static key, and decodes `auth-body`.
  let auth : AuthMessage ← decodeBody (← openPacket staticKey packet)
  -- `remote-pubk` is `initiator-pubk`.
  let remoteStatic ← decodePublicKey auth.initiatorPubkey
  -- `static-shared-secret = ecdh.agree(privkey, remote-pubk)`.
  let shared ← (ecdh staticKey remoteStatic).mapError .secp256k1
  -- Step 2: the recovery of `sig` over `static-shared-secret ^ initiator-nonce`.
  --
  -- It gives `remote-ephemeral-pubk`, and a failed recovery rejects `auth`.
  --
  -- Step 2 compares it with `keccak256(ephemeral-pubk)`, a field that EIP-8 removed.
  --
  -- So nothing is compared: the recovered key is the ephemeral key.
  let remoteEphemeral ← recoverSigner (xorBytes shared auth.initiatorNonce) auth.signature
  return (auth, remoteStatic, remoteEphemeral)

/-- The packet `ack` of the recipient to the initiator with the static key `initiator`. -/
def makeAck (keys : Keys) (initiator : Point) (sealing : Sealing) :
    Except HandshakeError ByteArray := do
  -- Step 3: `ack-body = [recipient-ephemeral-pubk, recipient-nonce, ack-vsn]`, with `ack-vsn = 4`.
  --
  -- `recipient-ephemeral-pubk` is `ephemeral-privkey * G`.
  let ack : AckMessage :=
    ⟨encodePublicKey (Point.mul keys.ephemeralKey .generator), keys.nonce, HANDSHAKE_VERSION⟩
  let body ← (Codec.encode ack).mapError .rlp
  -- `ack = ack-size || ecies.encrypt(initiator-pubk, ack-body || ack-padding, ack-size)`.
  sealPacket initiator sealing.r sealing.iv body sealing.padding

/-- What the initiator learns from `ack`: the message and the recipient's ephemeral key. -/
def readAck (staticKey : Fn) (packet : ByteArray) : Except HandshakeError (AckMessage × Point) := do
  -- Step 5: the initiator decrypts `ack` with its static key, and decodes `ack-body`.
  let ack : AckMessage ← decodeBody (← openPacket staticKey packet)
  -- `remote-ephemeral-pubk` is `recipient-ephemeral-pubk`.
  return (ack, ← decodePublicKey ack.ephemeralPubkey)

/-! ## Secrets -/

/-- The secrets of one side of a session. -/
structure Secrets where
  /-- `aes-secret`, the key of the frame cipher. -/
  aesSecret : Vector UInt8 32
  /-- `mac-secret`, the key of the frame MAC. -/
  macSecret : Vector UInt8 32
  /-- `egress-mac`, the Keccak-256 state of the bytes this side sends. -/
  egressMac : Hash.Keccak.Hasher256
  /-- `ingress-mac`, the Keccak-256 state of the bytes this side receives. -/
  ingressMac : Hash.Keccak.Hasher256

/--
The secrets of the session, from `ephemeral-key`, the two nonces and the two packets.

Each side receives what the other sends, so each ingress state is the other egress state.
-/
def deriveSecrets (initiator : Bool) (ephemeralKey initiatorNonce recipientNonce : Vector UInt8 32)
    (auth ack : ByteArray) : Secrets :=
  let keccak (a b : Vector UInt8 32) := Hash.Keccak.keccak256 ⟨a.toArray ++ b.toArray⟩
  -- `shared-secret = keccak256(ephemeral-key || keccak256(nonce || initiator-nonce))`.
  --
  -- `rlpx.md` leaves `nonce` undefined, and EthLib reads it as `recipient-nonce`.
  let sharedSecret := keccak ephemeralKey (keccak recipientNonce initiatorNonce)
  -- `aes-secret = keccak256(ephemeral-key || shared-secret)`.
  let aesSecret := keccak ephemeralKey sharedSecret
  -- `mac-secret = keccak256(ephemeral-key || aes-secret)`.
  let macSecret := keccak ephemeralKey aesSecret
  -- `keccak256.init(x)`: the Keccak-256 state that has absorbed `x`.
  let start (nonce : Vector UInt8 32) (packet : ByteArray) :=
    Hash.Keccak.Hasher256.empty.absorb (⟨(xorBytes macSecret nonce).toArray⟩ ++ packet)
  -- `keccak256.init((mac-secret ^ recipient-nonce) || auth)`, over the whole packet `auth`.
  let authMac := start recipientNonce auth
  -- `keccak256.init((mac-secret ^ initiator-nonce) || ack)`, over the whole packet `ack`.
  let ackMac := start initiatorNonce ack
  -- Initiator: `egress-mac` is the state of `auth`, and `ingress-mac` the state of `ack`.
  if initiator then ⟨aesSecret, macSecret, authMac, ackMac⟩
  -- Recipient: `egress-mac` is the state of `ack`, and `ingress-mac` the state of `auth`.
  else ⟨aesSecret, macSecret, ackMac, authMac⟩

/-- The recipient's answer to `auth`: the packet `ack` and the secrets of the session. -/
def respond (keys : Keys) (sealing : Sealing) (auth : ByteArray) :
    Except HandshakeError (ByteArray × Secrets) := do
  -- Step 2: the recipient decrypts and verifies `auth`.
  let (msg, remoteStatic, remoteEphemeral) ← readAuth keys.staticKey auth
  -- Step 3: the recipient generates `ack`, encrypted to `initiator-pubk`.
  let ack ← makeAck keys remoteStatic sealing
  -- `ephemeral-key = ecdh.agree(ephemeral-privkey, remote-ephemeral-pubk)`.
  let shared ← (ecdh keys.ephemeralKey remoteEphemeral).mapError .secp256k1
  -- Step 4: the recipient derives the secrets; its first frame is left to the caller.
  return (ack, deriveSecrets false shared msg.initiatorNonce keys.nonce auth ack)

/-- The initiator's secrets of the session, once `ack` answers its `auth`. -/
def finish (keys : Keys) (auth ack : ByteArray) : Except HandshakeError Secrets := do
  -- Step 5: the initiator receives `ack`.
  let (msg, remoteEphemeral) ← readAck keys.staticKey ack
  -- `ephemeral-key = ecdh.agree(ephemeral-privkey, remote-ephemeral-pubk)`.
  let shared ← (ecdh keys.ephemeralKey remoteEphemeral).mapError .secp256k1
  -- Step 5: the initiator derives the secrets.
  --
  -- Steps 6 to 9, the first frames of both sides, are left to the caller.
  return deriveSecrets true shared keys.nonce msg.recipientNonce auth ack

end EthLib.Networking.Rlpx
