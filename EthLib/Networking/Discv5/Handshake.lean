module

public import EthLib.Networking.Discv5.Identity
public import EthLib.Networking.Discv5.Packet

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

The module also seals and opens the handshake message packet of node A.

"Handshake Message Packet" of `discv5-wire.md` defines it:
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-wire.md>

Node B verifies the ID signature under a public key of node A that it already holds.

It does not check the record of node A that the packet carries.
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
  /-- The packet could not be written or read. -/
  | packet (error : PacketError)
  /-- The message could not be encrypted. -/
  | encryption (error : Cryptography.Aes.Gcm.Error)
  /-- The message does not authenticate under the initiator key. -/
  | decryption (error : Cryptography.Aes.Gcm.Error)
  /-- The packet is not a handshake message packet: its flag is `flag`, not 2. -/
  | notHandshake (flag : UInt8)
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
  | .packet _ => 7
  | .encryption _ => 8
  | .decryption _ => 9
  | .notHandshake _ => 10

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

/-! ## The handshake message packet -/

/-- A session key of 16 bytes as an AES-128 key.

The key derivation gives 16 bytes, so the default byte is never read. -/
def sessionKey (key : ByteArray) : Cryptography.Aes.Key .aes128 :=
  Vector.ofFn fun i => key.data.getD i.val 0

/-- What node B reads from a handshake message packet. -/
structure HandshakeReceived where
  /-- The node ID of node A, from the authdata. -/
  srcId : NodeId
  /-- The node record of node A, empty when node A left it out. -/
  record : ByteArray
  /-- The plaintext of the message. -/
  message : ByteArray
  /-- The session keys of node B. -/
  keys : SessionKeys
  deriving DecidableEq

/-- Node A's handshake message packet for node B, and the session keys of node A.

"Handshake Message Packet" of `discv5-wire.md` gives the authdata.

It holds the ID of node A, two sizes, the ID signature, the ephemeral key, then the record.

The message is AES-GCM under the initiator key, with the nonce of the header.

Its additional data is the masking IV, then the unmasked header.

The caller chooses the masking IV, the nonce and whether to send the record. -/
def sealHandshake (ephemeralKey staticKey : Fn) (challengeData : ByteArray)
    (nodeIdA nodeIdB : NodeId) (destPubkey : Point) (maskingIv : Vector UInt8 16)
    (nonce : Vector UInt8 12) (record plaintext : ByteArray) :
    Except HandshakeError (ByteArray × SessionKeys) := do
  let init ← initiateHandshake ephemeralKey staticKey challengeData nodeIdA nodeIdB destPubkey
  let header : Header :=
    ⟨nonce, .handshake nodeIdA init.idSignature init.ephemeralPubkey record⟩
  let ad ← (Packet.messageAd ⟨maskingIv, header, .empty⟩).mapError .packet
  let message ← (encryptMessage (sessionKey init.keys.initiatorKey) nonce plaintext ad).mapError
    .encryption
  let bytes ← (Packet.encode nodeIdB ⟨maskingIv, header, message⟩).mapError .packet
  return (bytes, init.keys)

/-- Node B's reading of a handshake message packet from node A.

Node B unmasks the packet, and completes step 4 with the ID and the keys of the authdata.

It then decrypts the message with the initiator key.

`srcPubkey` is the public key of node A, which node B takes from the record it trusts.

This does not check that the record in the packet is that of node A.

It does not check that the key of node A comes from that record, or the source ID against it. -/
def openHandshake (staticKey : Fn) (challengeData : ByteArray) (nodeIdB : NodeId)
    (srcPubkey : Point) (bytes : ByteArray) : Except HandshakeError HandshakeReceived := do
  let packet ← (Packet.decode nodeIdB bytes).mapError .packet
  let .handshake srcId idSignature ephemeralPubkey record := packet.header.authdata
    | throw (.notHandshake packet.header.authdata.flag)
  let keys ← acceptHandshake staticKey challengeData srcId nodeIdB srcPubkey ephemeralPubkey
    idSignature
  let ad ← packet.messageAd.mapError .packet
  let plaintext ← (decryptMessage (sessionKey keys.initiatorKey) packet.header.nonce
    packet.message ad).mapError .decryption
  return ⟨srcId, record, plaintext, keys⟩

end EthLib.Networking.Discv5
