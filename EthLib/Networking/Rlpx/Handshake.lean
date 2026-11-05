module

public import EthLib.Networking.Rlpx.Ecies
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Secp256k1.Sign
public import EthLib.Serialization.Rlp.Codec

/-!
# `Networking.Rlpx.Handshake`

The handshake of RLPx, from the section "Initial Handshake" of [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#initial-handshake

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
  | .infinity => Vector.replicate 64 0
  | .affine x y => ⟨(x.toBytes ++ y.toBytes).toArray, by simp [Fp.length_toBytes]⟩

/-- The public key of 64 bytes `x || y`, which must lie on the curve. -/
def decodePublicKey (bytes : Vector UInt8 64) : Except HandshakeError Point :=
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

EIP-8 asks the reader to ignore any further items.
-/
def leadingFields (count : Nat) (item : Item) : Except RlpError (List Item) := do
  let items ← item.toItems
  if count ≤ items.length then .ok (items.take count)
  else .error (.wrongFieldCount count items.length)

/-- `auth` as an RLP list of four items. -/
instance : Codec AuthMessage where
  toItem m := .list [Codec.toItem m.signature, Codec.toItem m.initiatorPubkey,
    Codec.toItem m.initiatorNonce, Codec.toItem m.version]
  ofItem item := do
    match ← leadingFields 4 item with
    | [s, p, n, v] =>
      return ⟨← Codec.ofItem s, ← Codec.ofItem p, ← Codec.ofItem n, ← Codec.ofItem v⟩
    | items => throw (RlpError.wrongFieldCount 4 items.length)

/-- `ack` as an RLP list of three items. -/
instance : Codec AckMessage where
  toItem m := .list [Codec.toItem m.ephemeralPubkey, Codec.toItem m.recipientNonce,
    Codec.toItem m.version]
  ofItem item := do
    match ← leadingFields 3 item with
    | [p, n, v] => return ⟨← Codec.ofItem p, ← Codec.ofItem n, ← Codec.ofItem v⟩
    | items => throw (RlpError.wrongFieldCount 3 items.length)

/--
The message at the start of a decrypted body.

EIP-8 asks the reader to ignore the bytes after the RLP list, which are padding.
-/
def decodeBody {α : Type} [Codec α] (body : ByteArray) : Except HandshakeError α :=
  (do Codec.ofItem (← decodeItem body.data.toList).1).mapError .rlp

/-! ## Packets -/

/-- `size` as two big-endian bytes. -/
def sizeBytes (size : Nat) : ByteArray := ⟨#[(size / 256).toUInt8, size.toUInt8]⟩

/--
The packet `size || ecies.encrypt(recipient, body || padding, size)`.

The size is the number of bytes of the ciphertext, and it must fit in 16 bits.

The ciphertext authenticates the size as its shared data.
-/
def sealPacket (recipient : Point) (r : Fn) (iv : Aes.Block) (body padding : ByteArray) :
    Except HandshakeError ByteArray := do
  let size := body.size + padding.size + Ecies.OVERHEAD
  if 2 ^ 16 ≤ size then throw (.tooLarge size)
  let ciphertext ← (Ecies.encrypt recipient r iv (sizeBytes size) (body ++ padding)).mapError .ecies
  return sizeBytes size ++ ciphertext

/-- The decrypted body of a packet: its size must count the bytes after it. -/
def openPacket (key : Fn) (packet : ByteArray) : Except HandshakeError ByteArray :=
  match packet.data.toList with
  | hi :: lo :: rest =>
    if hi.toNat * 256 + lo.toNat = rest.length then
      (Ecies.decrypt key ⟨#[hi, lo]⟩ ⟨rest.toArray⟩).mapError .ecies
    else .error (.badSize packet.size)
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
  ⟨(toBytesBE 32 sig.1.val ++ toBytesBE 32 sig.2.1.val ++ [if sig.2.2 then 1 else 0]).toArray,
    by simp [length_toBytesBE]⟩

/-- The public key that signed a hash, from a signature `r || s || v`. -/
def recoverSigner (hash : Vector UInt8 32) (sig : Vector UInt8 65) : Except HandshakeError Point :=
  let bytes := sig.toList
  let v := sig[64]
  if h : v.toNat < 2 then
    (Ecdsa.recover hash (ofBytesBE (bytes.take 32)) (ofBytesBE ((bytes.drop 32).take 32))
      ⟨v.toNat, h⟩).mapError .secp256k1
  else .error (.badRecoveryId v)

/--
The packet `auth` of the initiator to the recipient with the static key `recipient`.

`sig` signs `static-shared-secret ^ initiator-nonce` with the initiator's ephemeral key.

The pinned `rlpx.md` does not define `sig`, so the rule comes from its revision [`6504d41`][old].

[old]: https://github.com/ethereum/devp2p/blob/6504d410bc4b8dda2b43941e1cb48c804b90cf22/rlpx.md#handshake

The signature is `r || s || v`, in the low-s form, with the recovery id `v`.
-/
def makeAuth (keys : Keys) (recipient : Point) (sealing : Sealing) :
    Except HandshakeError ByteArray := do
  let shared ← (ecdh keys.staticKey recipient).mapError .secp256k1
  let sig ← (Ecdsa.sign keys.ephemeralKey (xorBytes shared keys.nonce)).mapError .secp256k1
  let auth : AuthMessage := ⟨signatureBytes sig,
    encodePublicKey (Point.mul keys.staticKey .generator), keys.nonce, HANDSHAKE_VERSION⟩
  let body ← (Codec.encode auth).mapError .rlp
  sealPacket recipient sealing.r sealing.iv body sealing.padding

/--
What the recipient learns from `auth`: the message and two public keys of the initiator.

The first is its static key, and the second is the ephemeral key that the signature names.
-/
def readAuth (staticKey : Fn) (packet : ByteArray) :
    Except HandshakeError (AuthMessage × Point × Point) := do
  let auth : AuthMessage ← decodeBody (← openPacket staticKey packet)
  let remoteStatic ← decodePublicKey auth.initiatorPubkey
  let shared ← (ecdh staticKey remoteStatic).mapError .secp256k1
  let remoteEphemeral ← recoverSigner (xorBytes shared auth.initiatorNonce) auth.signature
  return (auth, remoteStatic, remoteEphemeral)

/-- The packet `ack` of the recipient to the initiator with the static key `initiator`. -/
def makeAck (keys : Keys) (initiator : Point) (sealing : Sealing) :
    Except HandshakeError ByteArray := do
  let ack : AckMessage :=
    ⟨encodePublicKey (Point.mul keys.ephemeralKey .generator), keys.nonce, HANDSHAKE_VERSION⟩
  let body ← (Codec.encode ack).mapError .rlp
  sealPacket initiator sealing.r sealing.iv body sealing.padding

/-- What the initiator learns from `ack`: the message and the recipient's ephemeral key. -/
def readAck (staticKey : Fn) (packet : ByteArray) : Except HandshakeError (AckMessage × Point) := do
  let ack : AckMessage ← decodeBody (← openPacket staticKey packet)
  return (ack, ← decodePublicKey ack.ephemeralPubkey)

/-! ## Secrets -/

/-- The secrets of one side of a session. -/
structure Secrets where
  /-- `aes-secret`, the key of the frame cipher. -/
  aesSecret : Vector UInt8 32
  /-- `mac-secret`, the key of the frame MAC. -/
  macSecret : Vector UInt8 32
  /-- `egress-mac`, the Keccak-256 state of the bytes this side sends. -/
  egressMac : Hash.Keccak.Hasher
  /-- `ingress-mac`, the Keccak-256 state of the bytes this side receives. -/
  ingressMac : Hash.Keccak.Hasher

/--
The secrets of the session, from `ephemeral-key`, the two nonces and the two packets.

The initiator's egress state starts from `(mac-secret ^ recipient-nonce) || auth`.

The recipient's egress state starts from `(mac-secret ^ initiator-nonce) || ack`.

Each side receives what the other sends, so each ingress state is the other egress state.
-/
def deriveSecrets (initiator : Bool) (ephemeralKey initiatorNonce recipientNonce : Vector UInt8 32)
    (auth ack : ByteArray) : Secrets :=
  let keccak (a b : Vector UInt8 32) := Hash.Keccak.keccak256 ⟨a.toArray ++ b.toArray⟩
  let sharedSecret := keccak ephemeralKey (keccak recipientNonce initiatorNonce)
  let aesSecret := keccak ephemeralKey sharedSecret
  let macSecret := keccak ephemeralKey aesSecret
  let start (nonce : Vector UInt8 32) (packet : ByteArray) :=
    Hash.Keccak.Hasher.empty.absorb (⟨(xorBytes macSecret nonce).toArray⟩ ++ packet)
  let authMac := start recipientNonce auth
  let ackMac := start initiatorNonce ack
  if initiator then ⟨aesSecret, macSecret, authMac, ackMac⟩
  else ⟨aesSecret, macSecret, ackMac, authMac⟩

/-- The recipient's answer to `auth`: the packet `ack` and the secrets of the session. -/
def respond (keys : Keys) (sealing : Sealing) (auth : ByteArray) :
    Except HandshakeError (ByteArray × Secrets) := do
  let (msg, remoteStatic, remoteEphemeral) ← readAuth keys.staticKey auth
  let ack ← makeAck keys remoteStatic sealing
  let shared ← (ecdh keys.ephemeralKey remoteEphemeral).mapError .secp256k1
  return (ack, deriveSecrets false shared msg.initiatorNonce keys.nonce auth ack)

/-- The initiator's secrets of the session, once `ack` answers its `auth`. -/
def finish (keys : Keys) (auth ack : ByteArray) : Except HandshakeError Secrets := do
  let (msg, remoteEphemeral) ← readAck keys.staticKey ack
  let shared ← (ecdh keys.ephemeralKey remoteEphemeral).mapError .secp256k1
  return deriveSecrets true shared keys.nonce msg.recipientNonce auth ack

end EthLib.Networking.Rlpx
