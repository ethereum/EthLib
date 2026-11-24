module

public import EthLib.Base.ByteOrder
public import EthLib.Networking.Discv5.Handshake
public import EthLib.Networking.Discv5.Session
public import EthLib.Networking.Enr.V4

/-!
# `Networking.Discv5.Node`

The session states of a discv5 node.

The sources are the sections Sessions to Session Cache of [the theory text].

The text gives no lifetime for a challenge or a session, so they last until replaced.

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

/-- The key of the session cache: the node ID of the peer and its endpoint.

The keys of a session are tied to the node ID and to the IP address and UDP port of the peer.

So keys from one endpoint never open a packet from another, and the peer must handshake again. -/
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
  -- Node A sends under `initiator-key` from step 3, and node B under `recipient-key` from step 4.
  sessionKey (if s.initiator then s.keys.initiatorKey else s.keys.recipientKey)

/-- The key with which this node opens the messages of its peer in a session. -/
def Session.incomingKey (s : Session) : Aes.Key .aes128 :=
  -- Each side opens under the key with which the other side sends.
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

A packet that cannot be read, or a step that fails, leaves the state as it is and sends nothing.

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

/-- The random values of one step, which the caller supplies.

They are the last 8 bytes of a nonce, the ID nonce, the masking IV and the ephemeral key. -/
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

The section Session Cache strongly recommends this layout, so that the nonces of a session differ.

The counter wraps after `2^32` messages, a bound that the text leaves to the node.

After a wrap, two nonces repeat only if their 8 random bytes repeat too.
-/
def counterNonce (counter : UInt32) (tail : Vector UInt8 8) : Vector UInt8 12 :=
  -- Session Cache: the outgoing message count in the first 32 bits of the 96-bit nonce.
  --
  -- The remaining 64 bits are random; the source gives no byte order, and EthLib takes big-endian.
  (Base.ByteOrder.toBE 4 counter.toNat : Vector UInt8 4)
    ++ tail

/-- An ordinary message packet sealed in a session, and the session with its counter raised. -/
def sealInSession (node : Local) (rand : Randoms) (peer : NodeId) (session : Session)
    (plaintext : ByteArray) : Except SessionError (ByteArray × Session) := do
  -- Session Cache: the nonce encodes the count of outgoing messages of the session.
  let nonce := counterNonce session.counter rand.nonceTail
  -- An ordinary message packet, under the key with which this side of the session sends.
  let bytes ← sealMessage session.outgoingKey node.nodeId peer rand.maskingIv nonce plaintext
  -- The count grows by one per sealed message, so the nonces differ until it wraps.
  return (bytes, { session with counter := session.counter + 1 })

/-- The answer to a plaintext in a session, sealed, and the state with the raised counter.

Nothing is sent when the node does not answer, or when sealing fails. -/
def answerIn (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (session : Session) (plaintext : ByteArray) : NodeState × List ByteArray :=
  match node.answer plaintext with
  -- A message that the node does not answer sends nothing.
  | none => (state, [])
  | some reply =>
    -- The response, sealed in the session; the session keeps its raised counter.
    match sealInSession node rand key.id session reply with
    | .ok (bytes, session) =>
      ({ state with sessions := setKey state.sessions key session }, [bytes])
    -- A response that cannot be sealed, such as one over 1280 bytes, is not sent.
    | .error _ => (state, [])

/-- The step for an ordinary message packet from a peer. -/
def receiveMessage (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (nonce : Vector UInt8 12) (packet : Packet) : NodeState × List ByteArray :=
  -- Step 2: with session keys for the source node ID, node B tries to decrypt the message.
  --
  -- Session Cache: the keys are those of that node ID at that IP address and port.
  let opened := match lookupKey state.sessions key with
    | some session => (openPacket SessionError.packet SessionError.decryption
        session.incomingKey packet).toOption.map (session, ·)
    | none => none
  match opened with
  -- Step 2: decryption and authentication succeed, so node B responds to the message.
  | some (session, plaintext) =>
    -- An answer from the peer of a request of this node settles that request.
    --
    -- Not in the source: any message that opens from that peer settles it, not only the response.
    let settled := match lookupKey state.requests key.endpoint with
      | some request => decide (request.id = key.id)
      | none => false
    let state := if settled then { state with requests := eraseKey state.requests key.endpoint }
      else state
    answerIn node rand state key session plaintext
  | none =>
    match lookupKey state.challenges key with
    -- Handshake Implementation Considerations: a message packet while a challenge is pending.
    --
    -- The node re-sends the challenge already in progress, instead of creating a new one.
    | some challenge => (state, [challenge.packet])
    | none =>
      -- Step 2: no keys, or no decryption, so node B sends a WHOAREYOU with a new `id-nonce`.
      --
      -- Its `enr-seq` is that of the record of A that node B has, or zero without one.
      --
      -- Its `nonce` is that of the message packet that caused it.
      match makeWhoareyou key.id rand.maskingIv nonce rand.idNonce (node.knownSeq key.id) with
      -- Step 2: node B stores the challenge for step 4.
      --
      -- The record of A stays among what the node knows of its peers, not in the challenge.
      | .ok (bytes, challengeData) =>
        ({ state with challenges := setKey state.challenges key ⟨bytes, challengeData⟩ }, [bytes])
      | .error _ => (state, [])

/-- The step for a WHOAREYOU from an endpoint: a handshake packet for the request it mirrors. -/
def receiveWhoareyou (node : Local) (rand : Randoms) (state : NodeState) (endpoint : Endpoint)
    (bytes : ByteArray) : NodeState × List ByteArray :=
  -- Not in the source: EthLib keeps one pending request per endpoint, the last one sent.
  --
  -- So a WHOAREYOU for an earlier request is ignored, where the source re-sends that request.
  --
  -- A node with at most one request in flight per peer meets the source exactly.
  match lookupKey state.requests endpoint, readWhoareyou node.nodeId bytes with
  | some request, .ok challenge =>
    -- Step 3: the `nonce` of the WHOAREYOU mirrors the `nonce` of the request packet.
    if challenge.nonce = request.nonce then
      -- Step 1: node A must have a copy of the record of node B, here its public key.
      match node.publicKeyOf request.id with
      | some destKey =>
        -- A new session, whose count of outgoing messages starts at 0.
        let nonce := counterNonce 0 rand.nonceTail
        -- Step 3: node A includes its record when the `enr-seq` of the challenge is lower.
        --
        -- Handshake Message Packet also requires the record when `enr-seq` is zero.
        --
        -- The two rules differ only for a record of sequence number 0; EthLib follows step 3.
        let record := if challenge.enrSeq < node.enrSeq then node.record else .empty
        -- Step 3: the request is re-sent as a handshake message packet, under `initiator-key`.
        match sealHandshake rand.ephemeralKey node.staticKey challenge.challengeData node.nodeId
            request.id destKey rand.maskingIv nonce record request.plaintext with
        | .ok (packet, keys) =>
          -- Session Cache: the session is tied to the node ID of B and to this endpoint.
          --
          -- The handshake message took nonce count 0, so the counter is 1.
          --
          -- The request keeps the new nonce, which the next WHOAREYOU would mirror.
          let key : SessionKey := ⟨request.id, endpoint⟩
          ({ state with
              sessions := setKey state.sessions key ⟨keys, true, 1⟩
              requests := setKey state.requests endpoint { request with nonce := nonce } },
            [packet])
        | .error _ => (state, [])
      | none => (state, [])
    -- A WHOAREYOU that mirrors no pending request is ignored.
    else (state, [])
  -- Handshake Implementation Considerations: with no request pending, the WHOAREYOU is ignored.
  --
  -- So is a packet that is not a WHOAREYOU addressed to this node.
  | _, _ => (state, [])

/-- The public key of a peer from the record in its handshake packet.

The record must verify, and its node ID must be the source ID of the packet. -/
def recordKey (srcId : NodeId) (record : ByteArray) : Option Point :=
  -- Step 4: node B must first validate the record, by checking its signature.
  match Enr.decode record with
  | .ok r =>
    match Enr.nodeId r with
    -- Not in step 4: the node ID of the record must be the `src-id` of the packet.
    | .ok id => if Enr.verifyV4 r && id == srcId then r.publicKeyV4.toOption else none
    | .error _ => none
  | .error _ => none

/-- The step for a handshake packet from an endpoint, which answers a stored challenge. -/
def receiveHandshake (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (record bytes : ByteArray) : NodeState × List ByteArray :=
  -- Step 4: node B loads the WHOAREYOU challenge that it stored, and the record of node A.
  --
  -- Without a record of A, the packet must contain one, and it must verify.
  --
  -- With one, EthLib takes the public key from it, and does not check the record in the packet.
  --
  -- That departs from step 4: the key that B already holds decides the handshake.
  match lookupKey state.challenges key, node.publicKeyOf key.id <|> recordKey key.id record with
  | some challenge, some srcKey =>
    -- Step 4: verify `id-signature`, derive the session keys, then decrypt the message.
    match openHandshake node.staticKey challenge.challengeData node.nodeId srcKey bytes with
    | .ok received =>
      -- Step 4: the message decrypts and authenticates, so the new session keys are valid.
      --
      -- Node B is the recipient of the handshake, and the answered challenge leaves the store.
      let session : Session := ⟨received.keys, false, 0⟩
      let state := { state with
        sessions := setKey state.sessions key session
        challenges := eraseKey state.challenges key }
      -- Step 4: node B responds to the message, under `recipient-key`.
      answerIn node rand state key session received.message
    | .error _ => (state, [])
  -- No stored challenge, or no public key of node A: the packet is ignored.
  | _, _ => (state, [])

/-- The state of a node after a packet from an endpoint, and the packets it sends back. -/
def step (node : Local) (rand : Randoms) (state : NodeState) (endpoint : Endpoint)
    (bytes : ByteArray) : NodeState × List ByteArray :=
  -- Protocol Header: the node unmasks the header under `dest-id[:16]`, with its own ID.
  match Packet.decode node.nodeId bytes with
  | .ok packet =>
    -- The `flag` identifies the kind of packet.
    match packet.header.authdata with
    -- Flag 0: an ordinary message packet, from `src-id` at this endpoint.
    | .message srcId => receiveMessage node rand state ⟨srcId, endpoint⟩ packet.header.nonce packet
    -- Flag 1: a WHOAREYOU, matched to a pending request by its endpoint.
    | .whoareyou .. => receiveWhoareyou node rand state endpoint bytes
    -- Flag 2: a handshake message packet, from `src-id` at this endpoint.
    | .handshake srcId _ _ record =>
      receiveHandshake node rand state ⟨srcId, endpoint⟩ record bytes
  -- A packet that cannot be read changes nothing, and gets no answer.
  | .error _ => (state, [])

/-- A request to a peer: in its session if one exists, and otherwise as a packet it cannot open.

Without a session, the request is sealed under a key that the peer does not have. -/
def sendRequest (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (unknownKey : Aes.Key .aes128) (plaintext : ByteArray) : NodeState × List ByteArray :=
  match lookupKey state.sessions key with
  -- Step 1: with session keys for node B, node A encrypts its request with those keys.
  | some session =>
    match sealInSession node rand key.id session plaintext with
    | .ok (bytes, next) =>
      -- Handshake Implementation Considerations: the node keeps a reference to the sent request.
      --
      -- Its nonce is the one that a WHOAREYOU would mirror.
      ({ state with
          sessions := setKey state.sessions key next
          requests := setKey state.requests key.endpoint
            ⟨key.id, counterNonce session.counter rand.nonceTail, plaintext⟩ }, [bytes])
    | .error _ => (state, [])
  -- Step 1: without keys, node A sends an ordinary message packet with random message content.
  --
  -- Here it is the request under a key that B does not have, as in the example of step 1.
  --
  -- Node B cannot open it, and answers with a WHOAREYOU that starts the handshake.
  | none =>
    let nonce := counterNonce 0 rand.nonceTail
    match sealMessage unknownKey node.nodeId key.id rand.maskingIv nonce plaintext with
    -- The request is kept, for the WHOAREYOU that mirrors its nonce.
    | .ok bytes =>
      ({ state with requests := setKey state.requests key.endpoint ⟨key.id, nonce, plaintext⟩ },
        [bytes])
    | .error _ => (state, [])

end EthLib.Networking.Discv5
