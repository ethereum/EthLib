module

public import EthLib.Networking.Discv5.Identity
public import EthLib.Networking.Discv5.Packet

/-!
# `Networking.Discv5.Handshake`

The two sides of the discv5 handshake for the identity scheme v4.

The source is the section Handshake Steps of `discv5-theory.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv5/discv5-theory.md#handshake-steps>

Node A starts the handshake, and node B sent it the WHOAREYOU challenge.

The challenge data, the node IDs and the public key of each peer are inputs here.
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

The codes start at 301, since the packet, message and session errors share their Python class.

A new constructor takes a new code, so that each code keeps its meaning. -/
def HandshakeError.code : HandshakeError → UInt32
  | .keyAgreement _ => 301
  | .keyDerivation _ => 302
  | .signing _ => 303
  | .ephemeralKey _ => 304
  | .idSignature => 305
  | .ephemeralKeySize _ => 306
  | .packet _ => 307
  | .encryption _ => 308
  | .decryption _ => 309
  | .notHandshake _ => 310

/-- Step 3, for node A: the ephemeral public key, the ID signature and the session keys.

`ephemeralKey` is the random private key of the handshake, and `staticKey` that of node A.

`destPubkey` is the static public key of node B. -/
def initiateHandshake (ephemeralKey staticKey : Fn) (challengeData : ByteArray)
    (nodeIdA nodeIdB : NodeId) (destPubkey : Point) : Except HandshakeError HandshakeInit := do
  -- Step 3: `ephemeral-pubkey` is the public key of `ephemeral-key`, on secp256k1 for v4.
  --
  -- It is the 33-byte compressed point, the `eph-key-size` of `discv5-wire.md` for v4.
  let ephemeralPubkey := (Point.mul ephemeralKey Point.generator).encodeCompressed
  -- Step 3: `secret = ecdh(dest-pubkey, ephemeral-key)`.
  let secret ← (ecdh ephemeralKey destPubkey).mapError .keyAgreement
  -- Step 3: `initiator-key` and `recipient-key`, by HKDF of `secret`, salted by `challenge-data`.
  let keys ← (deriveKeys secret challengeData nodeIdA nodeIdB).mapError .keyDerivation
  -- `id-signature` signs `sha256(id-signature-input)` with the static private key of node A.
  --
  -- `id-signature-input = id-signature-text || challenge-data || ephemeral-pubkey || node-id-B`.
  let idSignature ← (idSign staticKey challengeData ephemeralPubkey nodeIdB).mapError .signing
  return ⟨ephemeralPubkey, idSignature, keys⟩

/-- Step 4, for node B: the session keys, once the ID signature of node A verifies.

`staticKey` is the private key of node B, and `srcPubkey` the public key of node A. -/
def acceptHandshake (staticKey : Fn) (challengeData : ByteArray) (nodeIdA nodeIdB : NodeId)
    (srcPubkey : Point) (ephemeralPubkey idSignature : ByteArray) :
    Except HandshakeError SessionKeys := do
  -- Step 4: node B verifies `id-signature` against the identity public key of A.
  unless idVerify srcPubkey challengeData ephemeralPubkey nodeIdB idSignature do
    throw .idSignature
  -- `discv5-wire.md` gives `eph-key-size = 33` for v4, so EthLib rejects any other size.
  unless ephemeralPubkey.size = 33 do throw (.ephemeralKeySize ephemeralPubkey.size)
  -- `ephemeral-pubkey` is a public key on secp256k1, so it must decode to a point of the curve.
  let ephemeral ← (Point.decode ephemeralPubkey).mapError .ephemeralKey
  -- Step 4: the key derivation, from the static private key of B and `ephemeral-pubkey`.
  --
  -- This secret equals `ecdh(dest-pubkey, ephemeral-key)` of step 3, as `d_B (e G) = e (d_B G)`.
  let secret ← (ecdh staticKey ephemeral).mapError .keyAgreement
  -- The HKDF of step 3, so both nodes hold the same `initiator-key` and `recipient-key`.
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

The section Handshake Message Packet of `discv5-wire.md` defines the packet:
<https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv5/discv5-wire.md#handshake-message-packet-flag--2>

The caller chooses the masking IV, the nonce and whether to send the record.

It fails when the packet would exceed 1280 bytes. -/
def sealHandshake (ephemeralKey staticKey : Fn) (challengeData : ByteArray)
    (nodeIdA nodeIdB : NodeId) (destPubkey : Point) (maskingIv : Vector UInt8 16)
    (nonce : Vector UInt8 12) (record plaintext : ByteArray) :
    Except HandshakeError (ByteArray × SessionKeys) := do
  -- Step 3: the ephemeral key pair, the session keys and the ID signature of node A.
  let init ← initiateHandshake ephemeralKey staticKey challengeData nodeIdA nodeIdB destPubkey
  -- Handshake Message Packet: `flag = 2`, with the `nonce` of the header.
  --
  -- `authdata = authdata-head || id-signature || eph-pubkey || record`, with `src-id = node-id-A`.
  let header : Header :=
    ⟨nonce, .handshake nodeIdA init.idSignature init.ephemeralPubkey record⟩
  -- Step 3: the request is re-sent, encrypted under the new `initiator-key`.
  --
  -- `message` is AES-GCM of `message-pt` and `message-ad`, under `initiator-key` and `nonce`.
  --
  -- `message-ad = masking-iv || header`, and the packet masks the header under `node-id-B[:16]`.
  let bytes ← sealPacket .packet .encryption (sessionKey init.keys.initiatorKey) nodeIdB maskingIv
    header plaintext
  return (bytes, init.keys)

/-- Node B's reading of a handshake message packet from node A.

`srcPubkey` is the public key of node A, which node B takes from the record it trusts.

This does not check that the record in the packet is that of node A.

It does not check that the key of node A comes from that record, or the source ID against it. -/
def openHandshake (staticKey : Fn) (challengeData : ByteArray) (nodeIdB : NodeId)
    (srcPubkey : Point) (bytes : ByteArray) : Except HandshakeError HandshakeReceived := do
  -- Protocol Header: node B unmasks the header under `dest-id[:16]`, with `dest-id = node-id-B`.
  let packet ← (Packet.decode nodeIdB bytes).mapError .packet
  -- Handshake Message Packet: `flag = 2`; EthLib takes `src-id` of `authdata-head` as `node-id-A`.
  let .handshake srcId idSignature ephemeralPubkey record := packet.header.authdata
    | throw (.notHandshake packet.header.authdata.flag)
  -- Step 4: verify `id-signature`, then derive the session keys from `ephemeral-pubkey`.
  let keys ← acceptHandshake staticKey challengeData srcId nodeIdB srcPubkey ephemeralPubkey
    idSignature
  -- Step 4: node B decrypts and authenticates the message under the new `initiator-key`.
  let plaintext ← openPacket .packet .decryption (sessionKey keys.initiatorKey) packet
  return ⟨srcId, record, plaintext, keys⟩

end EthLib.Networking.Discv5
