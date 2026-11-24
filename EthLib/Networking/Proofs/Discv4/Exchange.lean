module

public import EthLib.Networking.Discv4.Exchange
public import Mathlib.Data.List.Induction

/-!
# `Networking.Proofs.Discv4.Exchange`

Properties of the exchange rules of discv4.

Along a run, a node answers with Neighbors or an ENRResponse only after a matching Pong.
-/

@[expose] public section

namespace EthLib.Networking.Discv4

/-- A Neighbors packet carries one of the packets of a list of nodes. -/
theorem type_of_mem_neighborsPackets {expiration : Nat} :
    (nodes : List Node) → {p : Packet} → p ∈ neighborsPackets expiration nodes → p.type = 0x04
  | nodes, p, member => by
    unfold neighborsPackets at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      rfl
    · rcases List.mem_cons.mp member with rfl | rest
      · rfl
      · exact type_of_mem_neighborsPackets (nodes.drop MAX_NEIGHBORS) rest
termination_by nodes => nodes.length
decreasing_by simp_all only [List.length_drop, MAX_NEIGHBORS]; omega

/-- A node sends Neighbors or an ENRResponse only to an address that is proven at that time.

The state is any state, so this is one step of the bound along a run. -/
theorem proven_of_receive {node : Local} {now : Nat} {state : PeerState} {address : Address}
    {received : Received} {reply : Packet}
    (member : reply ∈ (receive node now state address received).2)
    (answer : reply.type = 0x04 ∨ reply.type = 0x06) : proven now state address = true := by
  unfold receive at member
  split at member
  · cases member
  · split at member
    · simp only [List.mem_singleton] at member
      subst member
      simp [Packet.type] at answer
    · split at member <;> cases member
    · split at member
      · assumption
      · cases member
    · split at member
      · assumption
      · cases member
    · cases member
    · cases member

/-- An expired packet changes nothing and gets no answer. -/
theorem receive_expired {node : Local} {now : Nat} {state : PeerState} {address : Address}
    {received : Received} (expired : received.packet.expired now = true) :
    receive node now state address received = (state, []) := by
  simp [receive, expired]

/-- A Pong without the hash of the most recent Ping changes nothing and gets no answer. -/
theorem receive_pong_unsolicited {node : Local} {now : Nat} {state : PeerState}
    {address : Address} {received : Received} {recipient : Endpoint} {hash : Vector UInt8 32}
    {expiration : Nat} {enrSeq : Option UInt64}
    (pong : received.packet = .pong recipient hash expiration enrSeq)
    (other : (state address).lastPing ≠ some hash) :
    receive node now state address received = (state, []) := by
  unfold receive
  split
  · rfl
  · rw [pong]
    simp [other]

/-- The Pong for a Ping that has not expired carries the hash of the Ping. -/
theorem receive_ping {node : Local} {now : Nat} {state : PeerState} {address : Address}
    {received : Received} {version : Nat} {sender recipient : Endpoint} {expiration : Nat}
    {enrSeq : Option UInt64}
    (ping : received.packet = .ping version sender recipient expiration enrSeq)
    (fresh : now ≤ expiration) :
    receive node now state address received = (state,
      [.pong ⟨address.ip, address.port, sender.tcpPort⟩ received.hash node.expiration
        node.enrSeq]) := by
  have : ¬ expiration < now := Nat.not_lt.mpr fresh
  simp [receive, ping, Packet.expired, Packet.expiration?, this]

/-- A Pong with the hash of the node's Ping, received in time, proves the address for 12 hours.

The proof holds at every time up to 12 hours after the Pong. -/
theorem proven_receive_pong {node : Local} {now later : Nat} {state : PeerState}
    {address : Address} {received : Received} {recipient : Endpoint} {hash : Vector UInt8 32}
    {expiration : Nat} {enrSeq : Option UInt64}
    (pong : received.packet = .pong recipient hash expiration enrSeq) (fresh : now ≤ expiration)
    (sent : (state address).lastPing = some hash) (from_ : now ≤ later)
    (within : later ≤ now + ENDPOINT_PROOF_SECONDS) :
    proven later (receive node now state address received).1 address = true := by
  have : ¬ expiration < now := Nat.not_lt.mpr fresh
  simp [receive, pong, Packet.expired, Packet.expiration?, this, sent, proven, PeerState.set,
    within, from_]

/-- A Ping, then the Pong that its receiver sends, prove the receiver's address to the sender.

The node sends a Ping with the hash of the packet, and the Pong of the receiver carries that hash.
-/
theorem proven_ping_pong {node peer : Local} {now : Nat} {state : PeerState}
    {address : Address} {ping pong : Received} {reply : Packet} {senderState : PeerState}
    {from_ : Address} {version : Nat} {sender recipient : Endpoint} {expiration : Nat}
    {enrSeq : Option UInt64}
    (isPing : ping.packet = .ping version sender recipient expiration enrSeq)
    (freshPing : now ≤ expiration)
    (answer : (receive peer now senderState from_ ping).2 = [reply])
    (delivered : pong.packet = reply) (freshPong : now ≤ peer.expiration) :
    proven now (receive node now (sendPing state address ping.hash) address pong).1 address =
      true := by
  rw [receive_ping isPing freshPing] at answer
  simp only [List.cons.injEq, and_true] at answer
  subst answer
  exact proven_receive_pong delivered freshPong (by simp [sendPing, PeerState.set])
    (Nat.le_refl _) (Nat.le_add_right _ _)

/-- Receiving a packet changes only what the node remembers of its sender. -/
theorem receive_other {node : Local} {now : Nat} {state : PeerState} {address other : Address}
    {received : Received} (differ : other ≠ address) :
    (receive node now state address received).1 other = state other := by
  unfold receive
  split
  · rfl
  · split
    · rfl
    · split
      · simp [PeerState.set, differ]
      · rfl
    all_goals rfl

/-- A proof at a time comes from a Pong with the hash of the node's Ping to that address.

Either the address was proven before, or the packet is such a Pong, received now. -/
theorem lastPong_receive {node : Local} {now time : Nat} {state : PeerState}
    {address other : Address} {received : Received}
    (h : ((receive node now state address received).1 other).lastPong = some time) :
    (state other).lastPong = some time ∨
      (other = address ∧ time = now ∧ received.packet.expired now = false ∧
        match received.packet with
        | .pong _ hash _ _ => (state address).lastPing = some hash
        | _ => False) := by
  unfold receive at h
  by_cases expired : received.packet.expired now = true
  · simp only [expired, ↓reduceIte] at h
    exact Or.inl h
  simp only [expired, Bool.false_eq_true, ↓reduceIte] at h
  have fresh : received.packet.expired now = false := by simpa using expired
  cases packet : received.packet with
  | pong recipient hash expiration enrSeq =>
    simp only [packet] at h
    split at h
    · rename_i sent
      by_cases same : other = address
      · subst same
        simp only [PeerState.set, ↓reduceIte, Option.some.injEq] at h
        exact Or.inr ⟨rfl, h.symm, by rw [← packet]; exact fresh, sent⟩
      · simp only [PeerState.set, same, ↓reduceIte] at h
        exact Or.inl h
    · exact Or.inl h
  | _ => simp only [packet] at h; exact Or.inl h

/-- An ENRResponse answers an ENRRequest exactly when it holds the request hash and a signed record.

The record must be signed by the key that signed the response. -/
theorem acceptEnrResponse_eq_true_iff {request response : Received} {expiration : Nat}
    {hash : Vector UInt8 32} {record : Serialization.Rlp.Item}
    (isRequest : request.packet = .enrRequest expiration)
    (isResponse : response.packet = .enrResponse hash record) :
    acceptEnrResponse request response = true ↔
      hash = request.hash ∧ recordSignedBy response.sender record = true := by
  simp [acceptEnrResponse, isRequest, isResponse]

/-! ## Along a run -/

/-- At an event of a run, the node received from an address, at a time, a matching Pong.

The Pong had not expired, and it carried the hash of the node's last Ping to that address then. -/
def PongAt (node : Local) (events : List Event) (address : Address) (time : Nat) : Prop :=
  ∃ before after packet, events = before ++ .received time address packet :: after ∧
    packet.packet.expired time = false ∧
    match packet.packet with
    | .pong _ hash _ _ => (run node before address).lastPing = some hash
    | _ => False

/-- The state after a run and one more event is the state after that event. -/
theorem run_append_event (node : Local) (events : List Event) (event : Event) :
    run node (events ++ [event]) = (step node (run node events) event).1 := by
  simp [run, List.foldl_append]

/-- A Pong that the node records along a run is a matching Pong of that run. -/
theorem pongAt_of_run {node : Local} {address : Address} {time : Nat} :
    (events : List Event) → (run node events address).lastPong = some time →
      PongAt node events address time := by
  intro events
  induction events using List.reverseRecOn with
  | nil => simp [run, PeerState.empty]
  | append_singleton events event ih =>
    intro h
    rw [run_append_event] at h
    -- A Pong found before the event is still in the run.
    have earlier (old : (run node events address).lastPong = some time) :
        PongAt node (events ++ [event]) address time := by
      obtain ⟨before, after, packet, split, fresh, matching⟩ := ih old
      exact ⟨before, after ++ [event], packet, by simp [split], fresh, matching⟩
    cases event with
    | sent other hash =>
      apply earlier
      by_cases same : address = other
      · subst same
        simpa [step, sendPing, PeerState.set] using h
      · simpa [step, sendPing, PeerState.set, same] using h
    | received now other packet =>
      rcases lastPong_receive h with old | ⟨rfl, rfl, fresh, matching⟩
      · exact earlier old
      · exact ⟨events, [], packet, rfl, fresh, matching⟩

/-- Along a run, Neighbors or an ENRResponse goes only to an address that sent a matching Pong.

That Pong came at most 12 hours before, and carried the hash of the node's last Ping then.

This bounds the traffic that a forged source address can draw. -/
theorem pongAt_of_step {node : Local} {events : List Event} {now : Nat} {address : Address}
    {received : Received} {reply : Packet}
    (member : reply ∈ (step node (run node events) (.received now address received)).2)
    (answer : reply.type = 0x04 ∨ reply.type = 0x06) :
    ∃ time, PongAt node events address time ∧ time ≤ now ∧
      now ≤ time + ENDPOINT_PROOF_SECONDS := by
  have proof := proven_of_receive member answer
  unfold proven at proof
  split at proof
  · rename_i time recorded
    simp only [Bool.and_eq_true, decide_eq_true_eq] at proof
    exact ⟨time, pongAt_of_run events recorded, proof.1, proof.2⟩
  · cases proof

end EthLib.Networking.Discv4
