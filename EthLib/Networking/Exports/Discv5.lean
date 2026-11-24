module

public import EthLib.Base.Exports.PyValue
public import EthLib.Networking.Exports.Enr
public import EthLib.Networking.Discv5.Exchange
public import EthLib.Networking.Discv5.Identity
public import EthLib.Networking.Discv5.Message
public import EthLib.Networking.Discv5.Node
public import EthLib.Networking.Discv5.Packet
public import EthLib.Networking.Discv5.Handshake
public import EthLib.Networking.Discv5.Session

/-!
# `Exports.Discv5`

C-ABI exports of the Node Discovery Protocol v5, for the Python bindings.

A packet, message, handshake or session-packet error comes back with its own code.

When a handshake or session failure is in the packet itself, the code is that of the packet error.

Any other rejected input, such as an AES-GCM failure or an argument Lean cannot read, has code 0.

The exports that read a packet, a message or a handshake return typed Python values.
-/

public section

namespace EthLib.Networking.Discv5.Exports

open EthLib.Exports (ExportError Result PyValue UnreadArgument toPy pyExport rejectArgument
  toResult)

open EthLib.Cryptography.Secp256k1
-- A private key crosses the boundary as 32 big-endian bytes.
open EthLib.Networking.Enr.Exports (privateKeyOf)

/-- A node ID of 32 bytes. -/
def nodeIdOf (bytes : ByteArray) : Result NodeId :=
  toResult none (Base.exactBytes 32 bytes fun size =>
    UnreadArgument.mk s!"node ID has {size} bytes, not 32")

/-- A public key in a SEC 1 encoding. -/
def publicKeyOf (bytes : ByteArray) : Result Point :=
  match Point.decode bytes with
  | .ok p => pure p
  | .error _ => rejectArgument none "public key is not a point of secp256k1"

/-- The logarithmic distance between two node IDs. -/
@[export eth_discv5_log_distance]
def logDistanceExport (a b : ByteArray) : Result UInt64 := do
  return (logDistance (← nodeIdOf a) (← nodeIdOf b)).toUInt64

/-- The 33-byte shared secret of a private key and a public key. -/
@[export eth_discv5_ecdh]
def ecdhExport (sk pk : ByteArray) : Result ByteArray := do
  match ecdh (← privateKeyOf sk) (← publicKeyOf pk) with
  | .ok secret => pure secret
  | .error _ => rejectArgument none "no shared secret"

/-- The session keys: the 16-byte initiator key and the 16-byte recipient key.

The secret is the ECDH of the ephemeral private key and the public key of node B. -/
def deriveKeysOf (args : ByteArray × ByteArray × ByteArray × ByteArray × ByteArray) :
    Result (ByteArray × ByteArray) := do
  let (ephemeralKey, destPubkey, nodeIdA, nodeIdB, challengeData) := args
  let some secret := (ecdh (← privateKeyOf ephemeralKey) (← publicKeyOf destPubkey)).toOption
    | rejectArgument none "no shared secret"
  match deriveKeys secret challengeData (← nodeIdOf nodeIdA) (← nodeIdOf nodeIdB) with
  | .ok keys => pure (keys.initiatorKey, keys.recipientKey)
  | .error _ => rejectArgument none "key derivation failed"

/-- The session keys: the 16-byte initiator key and the 16-byte recipient key.

The arguments are the ephemeral key of node A and the public key of node B.

Then come the two node IDs and the challenge data. -/
@[export eth_discv5_derive_keys]
def deriveKeysExport (args : PyValue) : Result PyValue :=
  pyExport deriveKeysOf args

/-- The 64-byte ID signature of node A. -/
@[export eth_discv5_id_sign]
def idSignExport (staticKey challengeData ephemeralPubkey nodeIdB : ByteArray) :
    Result ByteArray := do
  match idSign (← privateKeyOf staticKey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB) with
  | .ok signature => pure signature
  | .error _ => rejectArgument none "signing failed"

/-- Whether an ID signature verifies under the public key of node A. -/
@[export eth_discv5_id_verify]
def idVerifyExport (pubkey challengeData ephemeralPubkey nodeIdB signature : ByteArray) :
    Result UInt8 := do
  let ok := idVerify (← publicKeyOf pubkey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB)
    signature
  return if ok then 1 else 0

/-! ## Packets -/

/-- A rejected packet reaches Python with its code, and its message is the printed error. -/
instance : ExportError PacketError where
  code := PacketError.code
  message e := s!"{repr e}"

/-- The fields of an authdata, as Python values. -/
def authdataFields : Authdata → List (String × PyValue)
  | .message srcId => [("src_id", toPy srcId)]
  | .whoareyou idNonce enrSeq => [("id_nonce", toPy idNonce), ("enr_seq", toPy enrSeq)]
  | .handshake srcId idSignature ephemeralPubkey record =>
    [("src_id", toPy srcId), ("id_signature", toPy idSignature),
      ("ephemeral_pubkey", toPy ephemeralPubkey), ("record", toPy record)]

/-- The packet that a destination node reads, as a `dict`.

It holds the flag, the masking IV, the nonce, the authdata fields and the message.

It also holds the additional data of the message. -/
def decodePacketOf (args : ByteArray × ByteArray) : Result PyValue := do
  let (destId, bytes) := args
  let p ← toResult "invalid packet" (Packet.decode (← nodeIdOf destId) bytes)
  let ad ← toResult "invalid packet" p.messageAd
  return .dict <| (#[
    ("flag", toPy p.header.authdata.flag),
    ("masking_iv", toPy p.maskingIv),
    ("nonce", toPy p.header.nonce),
    ("message", toPy p.message),
    ("message_ad", toPy ad)] ++ (authdataFields p.header.authdata).toArray)

/-- The packet that a destination node reads, as a `dict`.

The arguments are the node ID of the destination and the packet.

It holds the flag, the masking IV, the nonce, the authdata fields and the message.

It also holds the additional data of the message. -/
@[export eth_discv5_decode_packet]
def decodePacketExport (args : PyValue) : Result PyValue :=
  pyExport decodePacketOf args

/-- The bytes of the packet that the decoder reads, written again by the encoder. -/
@[export eth_discv5_reencode_packet]
def reencodePacketExport (destId bytes : ByteArray) : Result ByteArray := do
  let id ← nodeIdOf destId
  toResult "invalid packet" ((Packet.decode id bytes).bind (Packet.encode id))

/-- An AES-128 key of 16 bytes. -/
def aesKeyOf (bytes : ByteArray) : Result (Cryptography.Aes.Key .aes128) :=
  toResult none (Base.exactBytes 16 bytes fun _ => UnreadArgument.mk "key is not 16 bytes")

/-- A nonce of 12 bytes. -/
def nonceOf (bytes : ByteArray) : Result (Vector UInt8 12) :=
  toResult none (Base.exactBytes 12 bytes fun _ => UnreadArgument.mk "nonce is not 12 bytes")

/-- The encrypted message, the ciphertext then the 16-byte tag. -/
@[export eth_discv5_encrypt_message]
def encryptMessageExport (key nonce plaintext ad : ByteArray) : Result ByteArray := do
  match encryptMessage (← aesKeyOf key) (← nonceOf nonce) plaintext ad with
  | .ok message => pure message
  | .error _ => rejectArgument none "encryption failed"

/-- The plaintext of an encrypted message, or an error if it does not authenticate. -/
@[export eth_discv5_decrypt_message]
def decryptMessageExport (key nonce message ad : ByteArray) : Result ByteArray := do
  match decryptMessage (← aesKeyOf key) (← nonceOf nonce) message ad with
  | .ok plaintext => pure plaintext
  | .error _ => rejectArgument none "message does not authenticate"

/-! ## Messages -/

/-- A rejected message reaches Python with its code, and its message names the fault. -/
instance : ExportError MessageError where
  code := MessageError.code
  message
    | .empty => "invalid message: empty"
    | .unknownType t => s!"invalid message: unknown type {t}"
    | .rlp _ => "invalid message: not one RLP list, or a field of the wrong form"
    | .fields t count => s!"invalid message: type {t} with {count} fields"
    | .invalid t => s!"invalid message: type {t} has a size or a distance out of range"

/-- The RLP bytes of an item, for a record inside a message, or `None` when it has none. -/
def itemBytes (item : Serialization.Rlp.Item) : PyValue :=
  match Serialization.Rlp.encode item with
  | .ok bytes => .bytes bytes
  | .error _ => .none

/-- The fields of a message, as Python values: byte strings as `bytes`, integers as `int`. -/
def messageFields : Message → List (String × PyValue)
  | .ping id seq => [("request_id", toPy id), ("enr_seq", toPy seq)]
  | .pong id seq ip port =>
    [("request_id", toPy id), ("enr_seq", toPy seq),
      ("recipient_ip", toPy ip), ("recipient_port", toPy port)]
  | .findnode id ds => [("request_id", toPy id), ("distances", toPy ds)]
  | .nodes id total rs =>
    [("request_id", toPy id), ("total", toPy total),
      ("records", .list (rs.map itemBytes).toArray)]
  | .talkreq id p r =>
    [("request_id", toPy id), ("protocol", toPy p),
      ("request", toPy r)]
  | .talkresp id r => [("request_id", toPy id), ("response", toPy r)]
  | .regtopic id t rec ticket ds =>
    [("request_id", toPy id), ("topic", toPy t), ("record", itemBytes rec),
      ("ticket", toPy ticket), ("distances", toPy ds)]
  | .regconfirmation id total ticket wait =>
    [("request_id", toPy id), ("total", toPy total),
      ("ticket", toPy ticket), ("wait_time", toPy wait)]
  | .topicquery id t ds =>
    [("request_id", toPy id), ("topic", toPy t), ("distances", toPy ds)]
  | .topicnodes id total rs =>
    [("request_id", toPy id), ("total", toPy total),
      ("records", .list (rs.map itemBytes).toArray)]

/-- The message of a plaintext, as a `dict` of its type and its fields. -/
def decodeMessageOf (plaintext : ByteArray) : Result PyValue := do
  let m ← toResult none (Message.decode plaintext)
  return .dict (("type", toPy m.type) :: messageFields m).toArray

/-- The message of a plaintext, as a `dict` of its type and its fields. -/
@[export eth_discv5_decode_message]
def decodeMessageExport (args : PyValue) : Result PyValue :=
  pyExport decodeMessageOf args

/-- The plaintext of the decoded message, written again by the encoder. -/
@[export eth_discv5_reencode_message]
def reencodeMessageExport (plaintext : ByteArray) : Result ByteArray := do
  let m ← toResult none (Message.decode plaintext)
  match m.encode with
  | .ok bytes => pure bytes
  | .error _ => rejectArgument none "message has no RLP encoding"

/-! ## Requests and answers -/

/-- Whether a message plaintext answers a request plaintext.

It must have the answer type of the request and the same request ID. -/
def answersRequestOf (args : ByteArray × ByteArray) : Result Bool := do
  let (request, answer) := args
  let request ← toResult none (Message.decode request)
  return answersRequest request (← toResult none (Message.decode answer))

/-- Whether a message plaintext answers a request plaintext.

It must have the answer type of the request and the same request ID.

PING is answered by PONG, FINDNODE by NODES, and TALKREQ by TALKRESP.

A plaintext that is not a valid message comes back with the code of its message error. -/
@[export eth_discv5_answers_request]
def answersRequestExport (args : PyValue) : Result PyValue :=
  pyExport answersRequestOf args

/-- The plaintext of the TALKRESP of a node that knows no protocol, for a TALKREQ plaintext. -/
def talkResponseOf (request : ByteArray) : Result ByteArray := do
  let some answer := talkResponse (fun _ => none) (← toResult none (Message.decode request))
    | rejectArgument none "message is not a TALKREQ"
  toResult none (answer.encode.mapError fun _ => UnreadArgument.mk "message has no RLP encoding")

/-- The plaintext of the TALKRESP of a node that knows no protocol, for a TALKREQ plaintext.

It has the request ID of the TALKREQ and an empty response.

Another message comes back with code 0. -/
@[export eth_discv5_talk_response]
def talkResponseExport (args : PyValue) : Result PyValue :=
  pyExport talkResponseOf args

/-- Whether records match the distances of a FINDNODE, from the node ID of its recipient. -/
def nodesMatchOf (args : ByteArray × List Nat × List ByteArray) : Result Bool := do
  let (recipient, distances, records) := args
  let items ← records.mapM fun bytes =>
    toResult none ((Serialization.Rlp.decode bytes).mapError fun _ =>
      UnreadArgument.mk "record is not one RLP item")
  return nodesMatch (← nodeIdOf recipient) distances items

/-- Whether records match the distances of a FINDNODE, from the node ID of its recipient.

Each record is its RLP bytes, and must be a "v4" record that verifies.

Its node ID must be at one of the logarithmic distances from the recipient.

Bytes that are not one RLP item come back with code 0. -/
@[export eth_discv5_nodes_match]
def nodesMatchExport (args : PyValue) : Result PyValue :=
  pyExport nodesMatchOf args

/-! ## Session packets -/

/-- A vector of `n` bytes, or an error that names the field. -/
def vectorOf (n : Nat) (field : String) (bytes : ByteArray) : Result (Vector UInt8 n) :=
  toResult none (Base.exactBytes n bytes fun size =>
    UnreadArgument.mk s!"{field} has {size} bytes, not {n}")

/-- A session error reaches Python with its code, or that of its packet error, and the reason. -/
instance : ExportError SessionError where
  code
    | .packet p => p.code
    | e => e.code
  message
    | .packet p => s!"invalid packet: {ExportError.message p}"
    | .encryption _ => "encryption failed"
    | .decryption _ => "message does not authenticate"
    | .wrongFlag flag expected => s!"packet has flag {flag}, not {expected}"
    | .noSession _ => "no session key for the source node ID"

/-- A handshake error reaches Python with its code, or that of its packet error, and the reason. -/
instance : ExportError HandshakeError where
  code
    | .packet p => p.code
    | e => e.code
  message
    | .packet p => s!"invalid packet: {ExportError.message p}"
    | .keyAgreement _ => "no shared secret"
    | .keyDerivation _ => "key derivation failed"
    | .signing _ => "signing failed"
    | .ephemeralKeySize size => s!"ephemeral key has {size} bytes, not 33"
    | .ephemeralKey _ => "ephemeral key is not a point of secp256k1"
    | .idSignature => "ID signature does not verify"
    | .encryption _ => "encryption failed"
    | .decryption _ => "message does not authenticate"
    | .notHandshake flag => s!"packet has flag {flag}, not 2"

/-- Node B's WHOAREYOU packet for node A, and its challenge data. -/
def makeWhoareyouOf (args : ByteArray × ByteArray × ByteArray × ByteArray × UInt64) :
    Result (ByteArray × ByteArray) := do
  let (destId, maskingIv, nonce, idNonce, enrSeq) := args
  toResult none (makeWhoareyou (← nodeIdOf destId) (← vectorOf 16 "masking IV" maskingIv)
    (← nonceOf nonce) (← vectorOf 16 "ID nonce" idNonce) enrSeq)

/-- Node B's WHOAREYOU packet for node A, and its challenge data.

The arguments are the node ID of node A, the masking IV, the nonce, the ID nonce and the seq. -/
@[export eth_discv5_make_whoareyou]
def makeWhoareyouExport (args : PyValue) : Result PyValue :=
  pyExport makeWhoareyouOf args

/-- Node A's reading of a WHOAREYOU packet, as a `dict`. -/
def readWhoareyouOf (args : ByteArray × ByteArray) : Result PyValue := do
  let (destId, packet) := args
  let c ← toResult none (readWhoareyou (← nodeIdOf destId) packet)
  return .dict #[("nonce", toPy c.nonce), ("id_nonce", toPy c.idNonce),
    ("enr_seq", toPy c.enrSeq), ("challenge_data", toPy c.challengeData)]

/-- Node A's reading of a WHOAREYOU packet, as a `dict`.

The arguments are the node ID of node A and the packet. -/
@[export eth_discv5_read_whoareyou]
def readWhoareyouExport (args : PyValue) : Result PyValue :=
  pyExport readWhoareyouOf args

/-- An ordinary message packet from one node to another, under a session key. -/
@[export eth_discv5_seal_message]
def sealMessageExport (key srcId destId maskingIv nonce plaintext : ByteArray) :
    Result ByteArray := do
  toResult none (sealMessage (← aesKeyOf key) (← nodeIdOf srcId) (← nodeIdOf destId)
    (← vectorOf 16 "masking IV" maskingIv) (← nonceOf nonce) plaintext)

/-- The plaintext of an ordinary message packet from a given node, under its session key.

It fails when the packet names another source node ID. -/
@[export eth_discv5_open_message]
def openMessageExport (key srcId destId packet : ByteArray) : Result ByteArray := do
  let k ← aesKeyOf key
  let src ← nodeIdOf srcId
  let (_, plaintext) ← toResult none (openMessage (fun id => if id = src then some k else none)
    (← nodeIdOf destId) packet)
  return plaintext

/-- The arguments of a handshake that node A seals.

They are the ephemeral key and the static key of node A, the challenge data and the two node IDs.

Then come the public key of node B, the masking IV, the nonce, the record and the plaintext. -/
abbrev SealHandshakeArgs := ByteArray × ByteArray × ByteArray × ByteArray × ByteArray ×
  ByteArray × ByteArray × ByteArray × ByteArray × ByteArray

/-- Node A's handshake message packet for node B, and its two session keys. -/
def sealHandshakeOf (args : SealHandshakeArgs) : Result (ByteArray × ByteArray × ByteArray) := do
  let (ephemeralKey, staticKey, challengeData, srcId, destId, destPubkey, maskingIv, nonce, record,
    plaintext) := args
  let (packet, keys) ← toResult none (sealHandshake (← privateKeyOf ephemeralKey)
    (← privateKeyOf staticKey) challengeData (← nodeIdOf srcId) (← nodeIdOf destId)
    (← publicKeyOf destPubkey) (← vectorOf 16 "masking IV" maskingIv) (← nonceOf nonce) record
    plaintext)
  return (packet, keys.initiatorKey, keys.recipientKey)

/-- Node A's handshake message packet for node B, and its two session keys.

The arguments are the ephemeral key and the static key of node A, the challenge data and the IDs.

Then come the public key of node B, the masking IV, the nonce, the record and the plaintext. -/
@[export eth_discv5_seal_handshake]
def sealHandshakeExport (args : PyValue) : Result PyValue :=
  pyExport sealHandshakeOf args

/-- Node B's reading of a handshake message packet, as a `dict`. -/
def openHandshakeOf (args : ByteArray × ByteArray × ByteArray × ByteArray × ByteArray) :
    Result PyValue := do
  let (staticKey, challengeData, destId, srcPubkey, packet) := args
  let r ← toResult none (openHandshake (← privateKeyOf staticKey) challengeData
    (← nodeIdOf destId) (← publicKeyOf srcPubkey) packet)
  return .dict #[("src_id", toPy r.srcId), ("record", toPy r.record),
    ("plaintext", toPy r.message), ("initiator_key", toPy r.keys.initiatorKey),
    ("recipient_key", toPy r.keys.recipientKey)]

/-- Node B's reading of a handshake message packet, as a `dict`.

The arguments are the static key of node B, the challenge data and the node ID of node B.

Then come the public key of node A and the packet. -/
@[export eth_discv5_open_handshake]
def openHandshakeExport (args : PyValue) : Result PyValue :=
  pyExport openHandshakeOf args

/-! ## Node states -/

/-- A session as Python values: the peer, its endpoint, the two keys, the side and the counter. -/
abbrev SessionValue := NodeId × ByteArray × UInt16 × ByteArray × ByteArray × Bool × UInt32

/-- A sent challenge as Python values: the peer, its endpoint, the packet and the challenge data. -/
abbrev ChallengeValue := NodeId × ByteArray × UInt16 × ByteArray × ByteArray

/-- A pending request as Python values: the endpoint, the peer, the nonce and the plaintext. -/
abbrev RequestValue := ByteArray × UInt16 × NodeId × Vector UInt8 12 × ByteArray

/-- A node state as Python values: its sessions, challenges and requests. -/
abbrev StateValue := List SessionValue × List ChallengeValue × List RequestValue

/-- What a node knows, as Python values.

They are its private key, node ID, record and record sequence number.

Then come its peers, each a node ID, a compressed public key and a record sequence number.

Last comes the plaintext of its answer to any message, if it answers. -/
abbrev LocalValue :=
  ByteArray × NodeId × ByteArray × UInt64 × List (NodeId × ByteArray × UInt64) × Option ByteArray

/-- The random values of a step: masking IV, nonce tail, ID nonce and ephemeral private key. -/
abbrev RandomsValue := Vector UInt8 16 × Vector UInt8 8 × Vector UInt8 16 × ByteArray

/-- The node of its Python values. -/
def localOf (value : LocalValue) : Result Local := do
  let (staticKey, nodeId, record, enrSeq, peers, reply) := value
  let peers ← peers.mapM fun (id, key, seq) => do return (id, ← publicKeyOf key, seq)
  return { staticKey := ← privateKeyOf staticKey, nodeId, record, enrSeq
           publicKeyOf := fun id => (peers.find? (·.1 = id)).map (·.2.1)
           knownSeq := fun id => ((peers.find? (·.1 = id)).map (·.2.2)).getD 0
           answer := fun _ => reply }

/-- The random values of their Python values. -/
def randomsOf (value : RandomsValue) : Result Randoms := do
  let (maskingIv, nonceTail, idNonce, ephemeralKey) := value
  return ⟨maskingIv, nonceTail, idNonce, ← privateKeyOf ephemeralKey⟩

/-- The state of its Python values. -/
def stateOf (value : StateValue) : NodeState :=
  let (sessions, challenges, requests) := value
  ⟨sessions.map fun (id, ip, port, ik, rk, init, counter) =>
      (⟨id, ⟨ip, port⟩⟩, ⟨⟨ik, rk⟩, init, counter⟩),
    challenges.map fun (id, ip, port, packet, cd) => (⟨id, ⟨ip, port⟩⟩, ⟨packet, cd⟩),
    requests.map fun (ip, port, id, nonce, plaintext) => (⟨ip, port⟩, ⟨id, nonce, plaintext⟩)⟩

/-- The Python values of a state. -/
def stateValue (state : NodeState) : StateValue :=
  (state.sessions.map fun (k, s) =>
      (k.id, k.endpoint.ip, k.endpoint.port, s.keys.initiatorKey, s.keys.recipientKey,
        s.initiator, s.counter),
    state.challenges.map fun (k, c) => (k.id, k.endpoint.ip, k.endpoint.port, c.packet,
      c.challengeData),
    state.requests.map fun (e, r) => (e.ip, e.port, r.id, r.nonce, r.plaintext))

/-- A node's state after a packet from an endpoint, and the packets it sends back. -/
def nodeStepOf (args : LocalValue × RandomsValue × StateValue × ByteArray × UInt16 × ByteArray) :
    Result (StateValue × List ByteArray) := do
  let (node, rand, state, ip, port, bytes) := args
  let (state, replies) := step (← localOf node) (← randomsOf rand) (stateOf state) ⟨ip, port⟩ bytes
  return (stateValue state, replies)

/-- A node's state after a packet from an endpoint, and the packets it sends back.

The node is its private key, node ID, record, record sequence number, peers and answer.

The random values are the masking IV, the nonce tail, the ID nonce and the ephemeral key.

The state is its sessions, its sent challenges and its pending requests. -/
@[export eth_discv5_node_step]
def nodeStepExport (args : PyValue) : Result PyValue :=
  pyExport nodeStepOf args

/-- A node's state after it sends a request to a peer, and the packet it sends. -/
def nodeSendOf (args : LocalValue × RandomsValue × StateValue × NodeId × ByteArray × UInt16 ×
    Vector UInt8 16 × ByteArray) : Result (StateValue × List ByteArray) := do
  let (node, rand, state, id, ip, port, unknownKey, plaintext) := args
  let (state, sent) := sendRequest (← localOf node) (← randomsOf rand) (stateOf state)
    ⟨id, ⟨ip, port⟩⟩ unknownKey plaintext
  return (stateValue state, sent)

/-- A node's state after it sends a request to a peer, and the packet it sends.

Without a session, the packet is sealed under the given key, which the peer does not have. -/
@[export eth_discv5_node_send]
def nodeSendExport (args : PyValue) : Result PyValue :=
  pyExport nodeSendOf args

end EthLib.Networking.Discv5.Exports
