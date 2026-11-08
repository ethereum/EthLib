module

public import EthLib.Networking.Discv5.Packet

/-!
# `Networking.Discv5.Session`

The WHOAREYOU challenge and the ordinary message packet of discv5.

The sources are three sections of `discv5-wire.md` in `ethereum/devp2p`.

They are "WHOAREYOU Packet", "Ordinary Message Packet" and "Protocol Header":
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-wire.md#packet-encoding>

Steps 1 and 2 of "Handshake Steps" in `discv5-theory.md` use them:
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-theory.md#handshake-steps>

Node B answers a message it cannot decrypt with a WHOAREYOU packet.

Its authdata is `id-nonce || enr-seq`, and its message is empty.

The challenge data of the handshake is the unmasked packet.

It is `masking-iv || static-header || authdata`.

An ordinary message packet has the source node ID as its authdata.

Its message is AES-GCM under a session key, with `masking-iv || header` as additional data.

The caller chooses the masking IV, the nonce, the ID nonce and the session key.

This module does not check that a nonce or an ID nonce is fresh, or that the `enr-seq` is current.

It does not keep sessions: the caller finds the key of a source node ID.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Cryptography

/-- Every way the WHOAREYOU challenge or an ordinary message packet can fail. -/
inductive SessionError where
  /-- The packet could not be written or read. -/
  | packet (error : PacketError)
  /-- The message could not be encrypted. -/
  | encryption (error : Aes.Gcm.Error)
  /-- The message does not authenticate under the session key. -/
  | decryption (error : Aes.Gcm.Error)
  /-- The packet has the flag `flag`, not the flag `expected` that the reader asks for. -/
  | wrongFlag (flag expected : UInt8)
  /-- No session key is known for the source node ID `srcId`. -/
  | noSession (srcId : NodeId)
  deriving DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor.

The codes start at 201, since the packet and message errors share their Python class.

A new constructor takes a new code, so that each code keeps its meaning. -/
def SessionError.code : SessionError → UInt32
  | .packet _ => 201
  | .encryption _ => 202
  | .decryption _ => 203
  | .wrongFlag .. => 204
  | .noSession _ => 205

/-- What node A reads from a WHOAREYOU packet. -/
structure Challenge where
  /-- The nonce of the message packet that caused the challenge. -/
  nonce : Vector UInt8 12
  /-- The random ID nonce of node B. -/
  idNonce : Vector UInt8 16
  /-- The sequence number of the record of node A that node B knows, or 0. -/
  enrSeq : UInt64
  /-- The challenge data: the masking IV, then the unmasked header. -/
  challengeData : ByteArray
  deriving DecidableEq

/-- Node B's WHOAREYOU packet for node A, and its challenge data.

`nonce` is the nonce of the message packet that caused the challenge. -/
def makeWhoareyou (nodeIdA : NodeId) (maskingIv : Vector UInt8 16) (nonce : Vector UInt8 12)
    (idNonce : Vector UInt8 16) (enrSeq : UInt64) :
    Except SessionError (ByteArray × ByteArray) := do
  let packet : Packet := ⟨maskingIv, ⟨nonce, .whoareyou idNonce enrSeq⟩, .empty⟩
  let challengeData ← packet.messageAd.mapError .packet
  let bytes ← (packet.encode nodeIdA).mapError .packet
  return (bytes, challengeData)

/-- Node A's reading of a WHOAREYOU packet.

It gives the nonce, the ID nonce, the `enr-seq` and the challenge data. -/
def readWhoareyou (nodeIdA : NodeId) (bytes : ByteArray) : Except SessionError Challenge := do
  let packet ← (Packet.decode nodeIdA bytes).mapError .packet
  let .whoareyou idNonce enrSeq := packet.header.authdata
    | throw (.wrongFlag packet.header.authdata.flag 1)
  let challengeData ← packet.messageAd.mapError .packet
  return ⟨packet.header.nonce, idNonce, enrSeq, challengeData⟩

/-- An ordinary message packet from node A to node B, encrypted under a session key.

It fails when the packet would exceed 1280 bytes. -/
def sealMessage (key : Aes.Key .aes128) (nodeIdA nodeIdB : NodeId) (maskingIv : Vector UInt8 16)
    (nonce : Vector UInt8 12) (plaintext : ByteArray) : Except SessionError ByteArray :=
  sealPacket .packet .encryption key nodeIdB maskingIv ⟨nonce, .message nodeIdA⟩ plaintext

/-- Node B's reading of an ordinary message packet: the source node ID and the plaintext.

`keyOf` gives the session key that node B holds for a source node ID, if any. -/
def openMessage (keyOf : NodeId → Option (Aes.Key .aes128)) (nodeIdB : NodeId)
    (bytes : ByteArray) : Except SessionError (NodeId × ByteArray) := do
  let packet ← (Packet.decode nodeIdB bytes).mapError .packet
  let .message srcId := packet.header.authdata
    | throw (.wrongFlag packet.header.authdata.flag 0)
  let some key := keyOf srcId | throw (.noSession srcId)
  return (srcId, ← openPacket .packet .decryption key packet)

end EthLib.Networking.Discv5
