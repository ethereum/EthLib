module

public import EthLib.Networking.Discv5.Node
public import EthLib.Networking.Proofs.Discv5.Handshake
public import EthLib.Networking.Proofs.Discv5.Session

/-!
# `Networking.Proofs.Discv5.Node`

Properties of the session states of a discv5 node.

- While a challenge is pending, a message that does not open gets the same WHOAREYOU again.
- Without a session and a challenge at an endpoint, a message gets a new WHOAREYOU there.
- A WHOAREYOU that mirrors no pending request changes nothing and gets no answer.
- A handshake packet with no stored challenge changes nothing.
- After a handshake run by both nodes, each opens what the other seals.
- Two packets sealed at two counters of a session carry two different nonces.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Cryptography.Secp256k1

/-! ## Lists of pairs -/

/-- A key that was just set has the value it was set to. -/
theorem lookupKey_setKey_self {κ α : Type} [DecidableEq κ] (pairs : List (κ × α)) (key : κ)
    (value : α) : lookupKey (setKey pairs key value) key = some value := by
  simp [lookupKey, setKey]

/-- Sealing in a session gives the same session with its counter raised by one. -/
theorem sealInSession_next {node : Local} {rand : Randoms} {peer : NodeId}
    {session next : Session} {plaintext bytes : ByteArray}
    (h : sealInSession node rand peer session plaintext = .ok (bytes, next)) :
    next = { session with counter := session.counter + 1 } := by
  unfold sealInSession at h
  cases hs : sealMessage session.outgoingKey node.nodeId peer rand.maskingIv
    (counterNonce session.counter rand.nonceTail) plaintext with
  | error e => simp [hs, bind, Except.bind] at h
  | ok b =>
    simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- Answering in a session keeps the keys of the session stored under that key, and its side. -/
theorem answerIn_keys (node : Local) (rand : Randoms) (state : NodeState) (key : SessionKey)
    (session : Session) (plaintext : ByteArray)
    (stored : lookupKey state.sessions key = some session) :
    (lookupKey (answerIn node rand state key session plaintext).1.sessions key).map
        (fun s => (s.incomingKey, s.outgoingKey)) =
      some (session.incomingKey, session.outgoingKey) := by
  unfold answerIn
  split
  · simp [stored]
  · split
    · rename_i bytes next sealed
      simp [sealInSession_next sealed, lookupKey_setKey_self, Session.incomingKey,
        Session.outgoingKey]
    · simp [stored]

/-! ## Decoding what a node sends -/

/-- A WHOAREYOU packet decodes back to its header, with an empty message. -/
theorem decode_makeWhoareyou {nodeId : NodeId} {maskingIv : Vector UInt8 16}
    {nonce : Vector UInt8 12} {idNonce : Vector UInt8 16} {enrSeq : UInt64}
    {bytes challengeData : ByteArray}
    (h : makeWhoareyou nodeId maskingIv nonce idNonce enrSeq = .ok (bytes, challengeData)) :
    Packet.decode nodeId bytes =
      .ok ⟨maskingIv, ⟨nonce, .whoareyou idNonce enrSeq⟩, .empty⟩ := by
  unfold makeWhoareyou at h
  cases ha : (Packet.messageAd ⟨maskingIv, ⟨nonce, .whoareyou idNonce enrSeq⟩, .empty⟩) with
  | error err => simp [ha, Except.mapError, bind, Except.bind] at h
  | ok ad =>
    cases hb : Packet.encode nodeId ⟨maskingIv, ⟨nonce, .whoareyou idNonce enrSeq⟩, .empty⟩ with
    | error err => simp [ha, hb, Except.mapError, bind, Except.bind] at h
    | ok b =>
      simp only [ha, hb, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]
      exact Proofs.Discv5.Packet.Packet.decode_encode hb fun _ => rfl

/-- A handshake packet decodes back to a header with the source ID, the nonce and the record. -/
theorem decode_sealHandshake {e a : Fn} {challengeData : ByteArray} {nodeIdA nodeIdB : NodeId}
    {destKey : Point} {maskingIv : Vector UInt8 16} {nonce : Vector UInt8 12}
    {record plaintext bytes : ByteArray} {keys : SessionKeys}
    (h : sealHandshake e a challengeData nodeIdA nodeIdB destKey maskingIv nonce record
      plaintext = .ok (bytes, keys)) :
    ∃ signature ephemeral message, Packet.decode nodeIdB bytes =
      .ok ⟨maskingIv, ⟨nonce, .handshake nodeIdA signature ephemeral record⟩, message⟩ := by
  unfold sealHandshake at h
  cases hi : initiateHandshake e a challengeData nodeIdA nodeIdB destKey with
  | error err => simp [hi, bind, Except.bind] at h
  | ok init =>
    simp only [hi, bind, Except.bind] at h
    cases hs : sealPacket HandshakeError.packet HandshakeError.encryption
        (sessionKey init.keys.initiatorKey) nodeIdB maskingIv
        ⟨nonce, .handshake nodeIdA init.idSignature init.ephemeralPubkey record⟩ plaintext with
    | error err => simp [hs] at h
    | ok b =>
      simp only [hs, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      obtain ⟨message, hdec, -⟩ := Proofs.Discv5.Packet.openPacket_sealPacket
        (decryptionError := HandshakeError.encryption) hs (by simp [Authdata.flag])
      exact ⟨_, _, message, hdec⟩

/-- A message sealed in a session decodes back to a header with the nonce of its counter. -/
theorem decode_sealInSession {node : Local} {rand : Randoms} {peer : NodeId}
    {session next : Session} {plaintext bytes : ByteArray}
    (h : sealInSession node rand peer session plaintext = .ok (bytes, next)) :
    ∃ message, Packet.decode peer bytes = .ok ⟨rand.maskingIv,
      ⟨counterNonce session.counter rand.nonceTail, .message node.nodeId⟩, message⟩ := by
  unfold sealInSession at h
  cases hs : sealMessage session.outgoingKey node.nodeId peer rand.maskingIv
    (counterNonce session.counter rand.nonceTail) plaintext with
  | error e => simp [hs, bind, Except.bind] at h
  | ok b =>
    simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    unfold sealMessage at hs
    obtain ⟨message, hdec, -⟩ := Proofs.Discv5.Packet.openPacket_sealPacket
      (decryptionError := SessionError.decryption) hs (by simp [Authdata.flag])
    exact ⟨message, hdec⟩

/-! ## Challenges -/

/-- No session of a peer at an endpoint opens a packet: there is none, or its key fails. -/
def NoOpen (state : NodeState) (key : SessionKey) (packet : Packet) : Prop :=
  ∀ session, lookupKey state.sessions key = some session →
    (openPacket SessionError.packet SessionError.decryption session.incomingKey packet).toOption =
      none

/-- While a challenge is pending and no session opens a message, it gets that WHOAREYOU again. -/
theorem receiveMessage_pending {node : Local} {rand : Randoms} {state : NodeState}
    {key : SessionKey} {nonce : Vector UInt8 12} {packet : Packet} {challenge : SentChallenge}
    (noOpen : NoOpen state key packet)
    (pending : lookupKey state.challenges key = some challenge) :
    receiveMessage node rand state key nonce packet = (state, [challenge.packet]) := by
  cases hs : lookupKey state.sessions key with
  | none => simp [receiveMessage, hs, pending]
  | some session => simp [receiveMessage, hs, noOpen session hs, pending]

/-- A second message that does not open gets the WHOAREYOU of the first, byte for byte.

The second step may have other random values and another nonce, and it changes nothing. -/
theorem receiveMessage_resend {node : Local} {rand rand' : Randoms} {state state' : NodeState}
    {key : SessionKey} {nonce nonce' : Vector UInt8 12} {packet packet' : Packet}
    {whoareyou : ByteArray}
    (noOpen : NoOpen state key packet) (noOpen' : NoOpen state key packet')
    (noChallenge : lookupKey state.challenges key = none)
    (first : receiveMessage node rand state key nonce packet = (state', [whoareyou])) :
    receiveMessage node rand' state' key nonce' packet' = (state', [whoareyou]) := by
  cases hm : makeWhoareyou key.id rand.maskingIv nonce rand.idNonce (node.knownSeq key.id) with
  | error e =>
    cases hs : lookupKey state.sessions key with
    | none => simp [receiveMessage, hs, noChallenge, hm] at first
    | some session => simp [receiveMessage, hs, noOpen session hs, noChallenge, hm] at first
  | ok r =>
    have unopened : receiveMessage node rand state key nonce packet =
        ({ state with challenges := setKey state.challenges key ⟨r.1, r.2⟩ }, [r.1]) := by
      cases hs : lookupKey state.sessions key with
      | none => simp [receiveMessage, hs, noChallenge, hm]
      | some session => simp [receiveMessage, hs, noOpen session hs, noChallenge, hm]
    rw [unopened] at first
    simp only [Prod.mk.injEq, List.cons.injEq, and_true] at first
    obtain ⟨rfl, rfl⟩ := first
    exact receiveMessage_pending
      (state := { state with challenges := setKey state.challenges key ⟨r.1, r.2⟩ })
      noOpen' (lookupKey_setKey_self _ _ _)

/-- A message that no session opens, with no pending challenge, gets a new WHOAREYOU.

The sessions that the peer holds at other endpoints play no part, since keys are per endpoint. -/
theorem receiveMessage_new {node : Local} {rand : Randoms} {state : NodeState}
    {key : SessionKey} {nonce : Vector UInt8 12} {packet : Packet}
    {whoareyou challengeData : ByteArray}
    (noOpen : NoOpen state key packet)
    (noChallenge : lookupKey state.challenges key = none)
    (made : makeWhoareyou key.id rand.maskingIv nonce rand.idNonce (node.knownSeq key.id) =
      .ok (whoareyou, challengeData)) :
    receiveMessage node rand state key nonce packet =
      ({ state with challenges := setKey state.challenges key ⟨whoareyou, challengeData⟩ },
        [whoareyou]) := by
  cases hs : lookupKey state.sessions key with
  | none => simp [receiveMessage, hs, noChallenge, made]
  | some session => simp [receiveMessage, hs, noOpen session hs, noChallenge, made]

/-- A WHOAREYOU from an endpoint with no pending request changes nothing and gets no answer. -/
theorem receiveWhoareyou_unsolicited {node : Local} {rand : Randoms} {state : NodeState}
    {endpoint : Endpoint} {bytes : ByteArray}
    (noRequest : lookupKey state.requests endpoint = none) :
    receiveWhoareyou node rand state endpoint bytes = (state, []) := by
  simp [receiveWhoareyou, noRequest]

/-- A WHOAREYOU that mirrors another nonce than that of the pending request changes nothing. -/
theorem receiveWhoareyou_other_nonce {node : Local} {rand : Randoms} {state : NodeState}
    {endpoint : Endpoint} {bytes : ByteArray} {request : Request} {challenge : Challenge}
    (pending : lookupKey state.requests endpoint = some request)
    (read : readWhoareyou node.nodeId bytes = .ok challenge)
    (other : challenge.nonce ≠ request.nonce) :
    receiveWhoareyou node rand state endpoint bytes = (state, []) := by
  simp [receiveWhoareyou, pending, read, other]

/-- A handshake packet from a peer with no stored challenge changes nothing and gets no answer.

So a handshake packet sent again, after its challenge was used, sets up nothing. -/
theorem receiveHandshake_unchallenged {node : Local} {rand : Randoms} {state : NodeState}
    {key : SessionKey} {record bytes : ByteArray}
    (noChallenge : lookupKey state.challenges key = none) :
    receiveHandshake node rand state key record bytes = (state, []) := by
  simp [receiveHandshake, noChallenge]

/-! ## Steps -/

/-- While a challenge is pending, a message packet that no session opens gets that WHOAREYOU. -/
theorem step_resend {node : Local} {rand : Randoms} {state : NodeState} {endpoint : Endpoint}
    {bytes : ByteArray} {packet : Packet} {srcId : NodeId} {challenge : SentChallenge}
    (decoded : Packet.decode node.nodeId bytes = .ok packet)
    (message : packet.header.authdata = .message srcId)
    (noOpen : NoOpen state ⟨srcId, endpoint⟩ packet)
    (pending : lookupKey state.challenges ⟨srcId, endpoint⟩ = some challenge) :
    step node rand state endpoint bytes = (state, [challenge.packet]) := by
  simp only [step, decoded, message]
  exact receiveMessage_pending noOpen pending

/-- A message packet from an endpoint where the peer has no session gets a new WHOAREYOU.

The sessions of the peer at other endpoints play no part. -/
theorem step_endpoint {node : Local} {rand : Randoms} {state : NodeState} {endpoint : Endpoint}
    {bytes : ByteArray} {packet : Packet} {srcId : NodeId} {whoareyou challengeData : ByteArray}
    (decoded : Packet.decode node.nodeId bytes = .ok packet)
    (message : packet.header.authdata = .message srcId)
    (noSession : lookupKey state.sessions ⟨srcId, endpoint⟩ = none)
    (noChallenge : lookupKey state.challenges ⟨srcId, endpoint⟩ = none)
    (made : makeWhoareyou srcId rand.maskingIv packet.header.nonce rand.idNonce
      (node.knownSeq srcId) = .ok (whoareyou, challengeData)) :
    step node rand state endpoint bytes =
      ({ state with
          challenges := setKey state.challenges ⟨srcId, endpoint⟩ ⟨whoareyou, challengeData⟩ },
        [whoareyou]) := by
  simp only [step, decoded, message]
  refine receiveMessage_new (fun session h => ?_) noChallenge made
  simp [noSession] at h

/-- A WHOAREYOU packet from an endpoint with no pending request changes nothing. -/
theorem step_whoareyou_unsolicited {node : Local} {rand : Randoms} {state : NodeState}
    {endpoint : Endpoint} {bytes : ByteArray} {packet : Packet} {idNonce : Vector UInt8 16}
    {enrSeq : UInt64}
    (decoded : Packet.decode node.nodeId bytes = .ok packet)
    (isWhoareyou : packet.header.authdata = .whoareyou idNonce enrSeq)
    (noRequest : lookupKey state.requests endpoint = none) :
    step node rand state endpoint bytes = (state, []) := by
  simp only [step, decoded, isWhoareyou]
  exact receiveWhoareyou_unsolicited noRequest

/-! ## The handshake -/

/-- After a handshake run by both nodes, node B opens what node A seals, and the other way.

Node B sent a WHOAREYOU for the pending request of node A, and keeps its challenge.

Node A steps on it and sends a handshake packet, and node B steps on that packet.

Each node has the public key of the other. -/
theorem handshake_agree {nodeA nodeB : Local} {randA randB : Randoms}
    {stateA stateA' stateB stateB' : NodeState} {endpointA endpointB : Endpoint}
    {request : Request} {maskingIv : Vector UInt8 16} {idNonce : Vector UInt8 16} {seq : UInt64}
    {whoareyou challengeData handshake : ByteArray} {replies : List ByteArray}
    {session : Session}
    (keyOfB : nodeA.publicKeyOf nodeB.nodeId = some (Point.mul nodeB.staticKey Point.generator))
    (keyOfA : nodeB.publicKeyOf nodeA.nodeId = some (Point.mul nodeA.staticKey Point.generator))
    (pending : lookupKey stateA.requests endpointB = some request)
    (toB : request.id = nodeB.nodeId)
    (made : makeWhoareyou nodeA.nodeId maskingIv request.nonce idNonce seq =
      .ok (whoareyou, challengeData))
    (kept : lookupKey stateB.challenges ⟨nodeA.nodeId, endpointA⟩ =
      some ⟨whoareyou, challengeData⟩)
    (stepA : step nodeA randA stateA endpointB whoareyou = (stateA', [handshake]))
    (stepB : step nodeB randB stateB endpointA handshake = (stateB', replies))
    (sessionA : lookupKey stateA'.sessions ⟨nodeB.nodeId, endpointB⟩ = some session) :
    (lookupKey stateB'.sessions ⟨nodeA.nodeId, endpointA⟩).map
        (fun s => (s.incomingKey, s.outgoingKey)) =
      some (session.outgoingKey, session.incomingKey) := by
  obtain ⟨-, readA⟩ := Proofs.Discv5.Session.readWhoareyou_makeWhoareyou made
  simp only [step, decode_makeWhoareyou made] at stepA
  simp only [receiveWhoareyou, pending, readA, ite_true, toB, keyOfB] at stepA
  split at stepA
  · rename_i packet keys sealed
    simp only [Prod.mk.injEq, List.cons.injEq, and_true] at stepA
    obtain ⟨rfl, rfl⟩ := stepA
    simp only [lookupKey_setKey_self, Option.some.injEq] at sessionA
    subst sessionA
    obtain ⟨signature, ephemeral, message, decodedB⟩ := decode_sealHandshake sealed
    have opened := Proofs.Discv5.Handshake.openHandshake_sealHandshake sealed
    simp only [step, decodedB, receiveHandshake, kept, keyOfA, Option.orElse_eq_orElse,
      Option.orElse_eq_or, Option.some_or, opened] at stepB
    let keyA : SessionKey := ⟨nodeA.nodeId, endpointA⟩
    have answered := answerIn_keys nodeB randB
      { stateB with
        sessions := setKey stateB.sessions keyA ⟨keys, false, 0⟩
        challenges := eraseKey stateB.challenges keyA }
      keyA ⟨keys, false, 0⟩ request.plaintext (lookupKey_setKey_self _ _ _)
    rw [stepB] at answered
    simpa [Session.incomingKey, Session.outgoingKey] using answered
  · simp at stepA

/-! ## Nonces -/

/-- Each of the first 4 bytes of a nonce is one big-endian byte of its counter. -/
theorem counterNonce_getElem (c : UInt32) (t : Vector UInt8 8) (i : Nat) (hi : i < 4) :
    (counterNonce c t)[i].toNat = c.toNat / 256 ^ (3 - i) % 256 := by
  rw [counterNonce, Vector.getElem_append_left hi, Vector.getElem_ofFn]
  simp

/-- Two nonces with different counters differ, whatever their last 8 bytes. -/
theorem counterNonce_ne {c1 c2 : UInt32} (differ : c1 ≠ c2) (t1 t2 : Vector UInt8 8) :
    counterNonce c1 t1 ≠ counterNonce c2 t2 := by
  intro h
  apply differ
  have byte (i : Nat) (hi : i < 4) :
      c1.toNat / 256 ^ (3 - i) % 256 = c2.toNat / 256 ^ (3 - i) % 256 := by
    rw [← counterNonce_getElem c1 t1 i hi, ← counterNonce_getElem c2 t2 i hi, h]
  have h0 := byte 0 (by decide)
  have h1 := byte 1 (by decide)
  have h2 := byte 2 (by decide)
  have h3 := byte 3 (by decide)
  simp only [Nat.reduceSub, Nat.reducePow, Nat.pow_zero, Nat.div_one] at h0 h1 h2 h3
  have b1 := c1.toNat_lt
  have b2 := c2.toNat_lt
  apply UInt32.toNat_inj.mp
  omega

/-- Sealing a message raises the counter of the session by one. -/
theorem counter_sealInSession {node : Local} {rand : Randoms} {peer : NodeId}
    {session next : Session} {plaintext bytes : ByteArray}
    (h : sealInSession node rand peer session plaintext = .ok (bytes, next)) :
    next.counter = session.counter + 1 := by
  rw [sealInSession_next h]

/-- The counters of messages sealed one after another differ while fewer than `2^32` are sealed. -/
theorem counter_add_ne {c : UInt32} {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32)
    (differ : i ≠ j) : c + UInt32.ofNat i ≠ c + UInt32.ofNat j := by
  intro h
  apply differ
  have h' := congrArg UInt32.toNat ((UInt32.add_right_inj c).mp h)
  rw [UInt32.toNat_ofNat_of_lt' (by simpa using hi),
    UInt32.toNat_ofNat_of_lt' (by simpa using hj)] at h'
  omega

/-- Two packets sealed from two session states with different counters carry different nonces.

The counters of messages sealed one after another differ for `2^32` messages.

So the nonces of those messages differ too. -/
theorem seal_nonce_distinct {node : Local} {rand1 rand2 : Randoms} {peer : NodeId}
    {session1 session2 next1 next2 : Session} {plaintext1 plaintext2 bytes1 bytes2 : ByteArray}
    (sealed1 : sealInSession node rand1 peer session1 plaintext1 = .ok (bytes1, next1))
    (sealed2 : sealInSession node rand2 peer session2 plaintext2 = .ok (bytes2, next2))
    (differ : session1.counter ≠ session2.counter) :
    (Packet.decode peer bytes1).map (·.header.nonce) ≠
      (Packet.decode peer bytes2).map (·.header.nonce) := by
  obtain ⟨m1, d1⟩ := decode_sealInSession sealed1
  obtain ⟨m2, d2⟩ := decode_sealInSession sealed2
  rw [d1, d2]
  intro h
  simp only [Except.map, Except.ok.injEq] at h
  exact counterNonce_ne differ _ _ h

end EthLib.Networking.Discv5
