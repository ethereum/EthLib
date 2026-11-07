module

public import EthLib.Networking.Discv5.Identity

/-!
# `Networking.Discv5.Handshake`

The two sides of the discv5 handshake for the "v4" identity scheme.

The source is "Handshake Steps" of `discv5-theory.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-theory.md#handshake-steps>

Node A starts the handshake, and node B sent it the WHOAREYOU challenge.

In step 3, node A makes an ephemeral key pair.

It derives the session keys from `ecdh(dest-pubkey, ephemeral-key)`.

It then signs the challenge data, its ephemeral public key and the ID of node B.

In step 4, node B verifies that signature under the public key of node A.

It then derives the session keys from its own static key and the ephemeral public key.

The ephemeral public key is the 33-byte compressed point.

"Handshake Message Packet" of `discv5-wire.md` gives that size for "v4".

The challenge data, the node IDs and the public key of each peer are inputs here.

The packet of the handshake, the record of node A and the message are not part of this module.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Hash

/-- What node A sends in its handshake message packet, and the session keys it derives. -/
structure HandshakeInit where
  /-- The ephemeral public key, as 33 compressed bytes. -/
  ephemeralPubkey : ByteArray
  /-- The ID signature, as the 64 bytes `r || s`. -/
  idSignature : ByteArray
  /-- The session keys of node A. -/
  keys : SessionKeys
  deriving DecidableEq

/-- Every way a side of the handshake can fail. -/
inductive HandshakeError where
  /-- The key agreement failed, because a key or a point is not valid. -/
  | keyAgreement (error : Secp256k1Error)
  /-- The key derivation failed. -/
  | keyDerivation (error : Hkdf.HkdfError)
  /-- The ID signature could not be made.

  This happens for the private key zero, and with negligible probability when no nonce is usable. -/
  | signing (error : Secp256k1Error)
  /-- The ephemeral public key has `size` bytes, not the 33 of a compressed point. -/
  | ephemeralKeySize (size : Nat)
  /-- The ephemeral public key is not a point of the curve. -/
  | ephemeralKey (error : Secp256k1Error)
  /-- The ID signature does not verify under the public key of node A. -/
  | idSignature
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def HandshakeError.code : HandshakeError → UInt32
  | .keyAgreement _ => 1
  | .keyDerivation _ => 2
  | .signing _ => 3
  | .ephemeralKey _ => 4
  | .idSignature => 5
  | .ephemeralKeySize _ => 6

/-- Step 3, for node A: the ephemeral public key, the ID signature and the session keys.

`ephemeralKey` is the random private key of the handshake, and `staticKey` that of node A.

`destPubkey` is the static public key of node B. -/
def initiateHandshake (ephemeralKey staticKey : Fn) (challengeData : ByteArray)
    (nodeIdA nodeIdB : NodeId) (destPubkey : Point) : Except HandshakeError HandshakeInit := do
  let ephemeralPubkey := (Point.mul ephemeralKey Point.generator).encodeCompressed
  let secret ← (ecdh ephemeralKey destPubkey).mapError .keyAgreement
  let keys ← (deriveKeys secret challengeData nodeIdA nodeIdB).mapError .keyDerivation
  let idSignature ← (idSign staticKey challengeData ephemeralPubkey nodeIdB).mapError .signing
  return ⟨ephemeralPubkey, idSignature, keys⟩

/-- Step 4, for node B: the session keys, once the ID signature of node A verifies.

`staticKey` is the private key of node B, and `srcPubkey` the public key of node A. -/
def acceptHandshake (staticKey : Fn) (challengeData : ByteArray) (nodeIdA nodeIdB : NodeId)
    (srcPubkey : Point) (ephemeralPubkey idSignature : ByteArray) :
    Except HandshakeError SessionKeys := do
  unless idVerify srcPubkey challengeData ephemeralPubkey nodeIdB idSignature do
    throw .idSignature
  unless ephemeralPubkey.size = 33 do throw (.ephemeralKeySize ephemeralPubkey.size)
  let ephemeral ← (Point.decode ephemeralPubkey).mapError .ephemeralKey
  let secret ← (ecdh staticKey ephemeral).mapError .keyAgreement
  (deriveKeys secret challengeData nodeIdA nodeIdB).mapError .keyDerivation

end EthLib.Networking.Discv5
