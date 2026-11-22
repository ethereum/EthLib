module

public import EthLib.Networking.Discv5.Handshake
public import EthLib.Networking.Discv5.Session
public import EthLib.Networking.Enr.V4

/-!
# `Networking.Discv5.Node`

The session states of a discv5 node, from "Sessions" to "Session Cache" of [the theory text].

A node keeps session keys, the WHOAREYOU challenges it sent, and the requests it sent.

The keys of a session are tied to the node ID and to the IP address and UDP port of the peer.

So keys from one endpoint never open a packet from another, and the peer must handshake again.

- A message that opens under the keys of its sender is answered.
- One that does not open gets a WHOAREYOU, which the node stores.
- While that challenge is pending, another such message gets the same WHOAREYOU again.
- A WHOAREYOU that mirrors the nonce of a pending request is answered by a handshake packet.
- A WHOAREYOU that mirrors no pending request is ignored.
- A handshake packet that answers a stored challenge sets up the session, and is answered.

The counter of a session numbers its outgoing messages, and fills the first 4 bytes of each nonce.

The other 8 bytes, the ID nonce, the masking IV and the ephemeral key are inputs.

A packet that cannot be read, or a step that fails, leaves the state as it is and sends nothing.

The text gives no lifetime for a challenge or a session, so they last until replaced.

The counter wraps after `2^32` messages, a bound that the text leaves to the node.

After a wrap, two nonces repeat only if their 8 random bytes repeat too.

[the theory text]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv5/discv5-theory.md#sessions
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1

/-- The UDP endpoint of a peer: its IP address and port. -/
structure Endpoint where
  /-- The IP address, 4 or 16 bytes. -/
  ip : ByteArray
  /-- The UDP port. -/
  port : UInt16
  deriving DecidableEq

/-- The key of the session cache: the node ID of the peer and its endpoint. -/
structure SessionKey where
  /-- The node ID of the peer. -/
  id : NodeId
  /-- The endpoint that the packets of the peer come from. -/
  endpoint : Endpoint
  deriving DecidableEq

/-- An established session: its keys, which side this node took, and its outgoing counter. -/
structure Session where
  /-- The session keys of the handshake. -/
  keys : SessionKeys
  /-- Whether this node started the handshake, and so sends with the initiator key. -/
  initiator : Bool
  /-- The number of messages that this node has sealed in the session. -/
  counter : UInt32
  deriving DecidableEq

/-- The key with which this node seals its messages in a session. -/
def Session.outgoingKey (s : Session) : Aes.Key .aes128 :=
  sessionKey (if s.initiator then s.keys.initiatorKey else s.keys.recipientKey)

/-- The key with which this node opens the messages of its peer in a session. -/
def Session.incomingKey (s : Session) : Aes.Key .aes128 :=
  sessionKey (if s.initiator then s.keys.recipientKey else s.keys.initiatorKey)

/-- A WHOAREYOU challenge that this node sent: the packet, and the challenge data it keeps. -/
structure SentChallenge where
  /-- The WHOAREYOU packet, which this node sends again while the challenge is pending. -/
  packet : ByteArray
  /-- The challenge data, which the handshake of the peer signs. -/
  challengeData : ByteArray
  deriving DecidableEq

/-- A request that this node sent and that no answer has met yet. -/
structure Request where
  /-- The node ID of the peer. -/
  id : NodeId
  /-- The nonce of its packet, which a WHOAREYOU mirrors. -/
  nonce : Vector UInt8 12
  /-- The plaintext of the message, which a handshake packet sends again. -/
  plaintext : ByteArray
  deriving DecidableEq

/-- What a node keeps: its sessions and challenges by session key, and its requests by endpoint.

Each list holds at most one entry per key, the most recent first. -/
structure NodeState where
  /-- The session cache. -/
  sessions : List (SessionKey × Session)
  /-- The WHOAREYOU challenges that this node sent and that no handshake has answered. -/
  challenges : List (SessionKey × SentChallenge)
  /-- The requests that this node sent, one per endpoint. -/
  requests : List (Endpoint × Request)
  deriving DecidableEq

/-- The value of a key in a list of pairs, if any. -/
def lookupKey {κ α : Type} [DecidableEq κ] (pairs : List (κ × α)) (key : κ) : Option α :=
  (pairs.find? (·.1 = key)).map (·.2)

/-- A list of pairs with the value of a key replaced, or added. -/
def setKey {κ α : Type} [DecidableEq κ] (pairs : List (κ × α)) (key : κ) (value : α) :
    List (κ × α) :=
  (key, value) :: pairs.filter (·.1 ≠ key)

/-- A list of pairs without a key. -/
def eraseKey {κ α : Type} [DecidableEq κ] (pairs : List (κ × α)) (key : κ) : List (κ × α) :=
  pairs.filter (·.1 ≠ key)

/-- The state of a node that has met no peer. -/
def NodeState.empty : NodeState := ⟨[], [], []⟩

/-- What a node knows of itself and of its peers. -/
structure Local where
  /-- The static private key of the node. -/
  staticKey : Fn
  /-- The node ID of the node. -/
  nodeId : NodeId
  /-- The record of the node, which a handshake packet carries when the peer's copy is older. -/
  record : ByteArray
  /-- The sequence number of the record of the node. -/
  enrSeq : UInt64
  /-- The public key of a peer, from its record, if the node has it. -/
  publicKeyOf : NodeId → Option Point
  /-- The sequence number of the record of a peer that the node has, or 0. -/
  knownSeq : NodeId → UInt64
  /-- The plaintext of the answer to a message, if the node answers it. -/
  answer : ByteArray → Option ByteArray

/-- The random values of one step. -/
structure Randoms where
  /-- The masking IV of a packet that the node sends. -/
  maskingIv : Vector UInt8 16
  /-- The last 8 bytes of a nonce. -/
  nonceTail : Vector UInt8 8
  /-- The ID nonce of a new WHOAREYOU. -/
  idNonce : Vector UInt8 16
  /-- The ephemeral private key of a handshake. -/
  ephemeralKey : Fn

/-- The nonce of the message numbered `counter`: the counter in 4 big-endian bytes, then 8 bytes.

The text "strongly" recommends this layout, so that the nonces of a session differ. -/
def counterNonce (counter : UInt32) (tail : Vector UInt8 8) : Vector UInt8 12 :=
  (Vector.ofFn fun i : Fin 4 => UInt8.ofNat (counter.toNat / 256 ^ (3 - i.val))) ++ tail

/-- An ordinary message packet sealed in a session, and the session with its counter raised. -/
def sealInSession (node : Local) (rand : Randoms) (peer : NodeId) (session : Session)
    (plaintext : ByteArray) : Except SessionError (ByteArray × Session) := do
  let nonce := counterNonce session.counter rand.nonceTail
  let bytes ← sealMessage session.outgoingKey node.nodeId peer rand.maskingIv nonce plaintext
  return (bytes, { session with counter := session.counter + 1 })

/-- The answer to a plaintext in a session, sealed, and the state with the raised counter.

Nothing is sent when the node does not answer, or when sealing fails. -/
def answerIn (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (session : Session) (plaintext : ByteArray) : NodeState × List ByteArray :=
  match node.answer plaintext with
  | none => (state, [])
  | some reply =>
    match sealInSession node rand key.id session reply with
    | .ok (bytes, session) =>
      ({ state with sessions := setKey state.sessions key session }, [bytes])
    | .error _ => (state, [])

/-- The step for an ordinary message packet from a peer.

It opens under the keys of that peer at that endpoint.

Otherwise it gets the pending WHOAREYOU of that peer, or a new one. -/
def receiveMessage (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (nonce : Vector UInt8 12) (packet : Packet) : NodeState × List ByteArray :=
  let opened := match lookupKey state.sessions key with
    | some session => (openPacket SessionError.packet SessionError.decryption
        session.incomingKey packet).toOption.map (session, ·)
    | none => none
  match opened with
  | some (session, plaintext) =>
    -- An answer from the peer of a request of this node settles that request.
    let settled := match lookupKey state.requests key.endpoint with
      | some request => decide (request.id = key.id)
      | none => false
    let state := if settled then { state with requests := eraseKey state.requests key.endpoint }
      else state
    answerIn node rand state key session plaintext
  | none =>
    match lookupKey state.challenges key with
    | some challenge => (state, [challenge.packet])
    | none =>
      match makeWhoareyou key.id rand.maskingIv nonce rand.idNonce (node.knownSeq key.id) with
      | .ok (bytes, challengeData) =>
        ({ state with challenges := setKey state.challenges key ⟨bytes, challengeData⟩ }, [bytes])
      | .error _ => (state, [])

/-- The step for a WHOAREYOU from an endpoint: a handshake packet for the request it mirrors.

The handshake packet sends the plaintext of that request again.

It carries the record of the node when the challenge holds an older sequence number. -/
def receiveWhoareyou (node : Local) (rand : Randoms) (state : NodeState) (endpoint : Endpoint)
    (bytes : ByteArray) : NodeState × List ByteArray :=
  match lookupKey state.requests endpoint, readWhoareyou node.nodeId bytes with
  | some request, .ok challenge =>
    if challenge.nonce = request.nonce then
      match node.publicKeyOf request.id with
      | some destKey =>
        let nonce := counterNonce 0 rand.nonceTail
        let record := if challenge.enrSeq < node.enrSeq then node.record else .empty
        match sealHandshake rand.ephemeralKey node.staticKey challenge.challengeData node.nodeId
            request.id destKey rand.maskingIv nonce record request.plaintext with
        | .ok (packet, keys) =>
          let key : SessionKey := ⟨request.id, endpoint⟩
          ({ state with
              sessions := setKey state.sessions key ⟨keys, true, 1⟩
              requests := setKey state.requests endpoint { request with nonce := nonce } },
            [packet])
        | .error _ => (state, [])
      | none => (state, [])
    else (state, [])
  | _, _ => (state, [])

/-- The public key of a peer from the record in its handshake packet.

The record must verify, and its node ID must be the source ID of the packet. -/
def recordKey (srcId : NodeId) (record : ByteArray) : Option Point :=
  match Enr.decode record with
  | .ok r =>
    match Enr.nodeId r with
    | .ok id => if Enr.verifyV4 r && id == srcId then r.publicKeyV4.toOption else none
    | .error _ => none
  | .error _ => none

/-- The step for a handshake packet from an endpoint, which answers a stored challenge.

The public key of the peer comes from the record of it that the node has.

Without one, it comes from the record in the packet, which "must" then be there and verify.

Its keys set up the session, and its message is answered in it. -/
def receiveHandshake (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (record bytes : ByteArray) : NodeState × List ByteArray :=
  match lookupKey state.challenges key, node.publicKeyOf key.id <|> recordKey key.id record with
  | some challenge, some srcKey =>
    match openHandshake node.staticKey challenge.challengeData node.nodeId srcKey bytes with
    | .ok received =>
      let session : Session := ⟨received.keys, false, 0⟩
      let state := { state with
        sessions := setKey state.sessions key session
        challenges := eraseKey state.challenges key }
      answerIn node rand state key session received.message
    | .error _ => (state, [])
  | _, _ => (state, [])

/-- The state of a node after a packet from an endpoint, and the packets it sends back. -/
def step (node : Local) (rand : Randoms) (state : NodeState) (endpoint : Endpoint)
    (bytes : ByteArray) : NodeState × List ByteArray :=
  match Packet.decode node.nodeId bytes with
  | .ok packet =>
    match packet.header.authdata with
    | .message srcId => receiveMessage node rand state ⟨srcId, endpoint⟩ packet.header.nonce packet
    | .whoareyou .. => receiveWhoareyou node rand state endpoint bytes
    | .handshake srcId _ _ record =>
      receiveHandshake node rand state ⟨srcId, endpoint⟩ record bytes
  | .error _ => (state, [])

/-- A request to a peer: in its session if one exists, and otherwise as a packet it cannot open.

Without a session, the packet is sealed under a key the peer does not have.

So the peer cannot open it, and answers with a WHOAREYOU that starts a handshake. -/
def sendRequest (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (unknownKey : Aes.Key .aes128) (plaintext : ByteArray) : NodeState × List ByteArray :=
  match lookupKey state.sessions key with
  | some session =>
    match sealInSession node rand key.id session plaintext with
    | .ok (bytes, next) =>
      ({ state with
          sessions := setKey state.sessions key next
          requests := setKey state.requests key.endpoint
            ⟨key.id, counterNonce session.counter rand.nonceTail, plaintext⟩ }, [bytes])
    | .error _ => (state, [])
  | none =>
    let nonce := counterNonce 0 rand.nonceTail
    match sealMessage unknownKey node.nodeId key.id rand.maskingIv nonce plaintext with
    | .ok bytes =>
      ({ state with requests := setKey state.requests key.endpoint ⟨key.id, nonce, plaintext⟩ },
        [bytes])
    | .error _ => (state, [])

end EthLib.Networking.Discv5
