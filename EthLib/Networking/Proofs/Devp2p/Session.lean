module

public import EthLib.Networking.Devp2p.Session
public import EthLib.Networking.Proofs.Devp2p.P2p

/-!
# Proofs: the session of an RLPx connection

Before the peer's Hello, every frame other than Hello and Disconnect is rejected.

The peer's Hello opens the session.

The session then holds the shared capabilities and the Snappy flag of both Hello messages.

Each ID that a shared capability holds routes to that capability, at its relative ID.

Two IDs never route to one place, and both peers route every ID the same way.

No ID below `0x10` routes to a capability.

In an active session, a Ping asks for exactly one Pong and leaves the session as it was.

After a Disconnect, every frame is rejected.

The reasons of Disconnect read back from their numbers.
-/

@[expose] public section

namespace EthLib.Networking.Devp2p

open EthLib.Serialization.Rlp

/-- Each reason reads back from its number. -/
theorem DisconnectReason.ofNat?_toNat (reason : DisconnectReason) :
    DisconnectReason.ofNat? reason.toNat = some reason := by
  cases reason <;> rfl

/-- A number that the table names reads back as a reason with that number. -/
theorem DisconnectReason.toNat_of_ofNat? {n : Nat} {reason : DisconnectReason}
    (h : DisconnectReason.ofNat? n = some reason) : reason.toNat = n := by
  unfold DisconnectReason.ofNat? at h
  split at h <;> cases h <;> rfl

/-- Before the peer's Hello, a frame whose ID is neither Hello nor Disconnect is rejected. -/
theorem receive_beforeHello {length : Capability → Nat} {ours : Hello} {frameData rest : ByteArray}
    {id : Nat} (split : splitFrame frameData = .ok (id, rest)) (notHello : id ≠ 0x00)
    (notDisconnect : id ≠ 0x01) :
    receive length ours .awaitHello frameData = .error (.beforeHello id) := by
  have hc : (id != 0x00 && id != 0x01) = true := by simpa using ⟨notHello, notDisconnect⟩
  simp only [receive, split, Except.mapError, bind, Except.bind, hc, ↓reduceIte]
  rfl

/-- Before the peer's Hello, the peer's Hello opens the session.

The session then holds the Snappy flag of both versions and the IDs of the shared capabilities. -/
theorem receive_hello_active {length : Capability → Nat} {ours theirs : Hello}
    {data frame : ByteArray} (encoded : encode (Message.hello theirs).toItem = .ok data)
    (framed : encodeMessage false (.hello theirs) = .ok frame) :
    receive length ours .awaitHello frame =
      .ok (.active ours theirs (snappyEnabled ours.protocolVersion theirs.protocolVersion)
        (negotiate length ours.capabilities theirs.capabilities),
        some (.p2p (.hello theirs)), []) := by
  obtain ⟨rest, hs, hb⟩ := decodeBody_encodeMessage_false encoded framed
  simp only [Message.id] at hs hb
  simp only [receive, hs, hb, Except.mapError, bind, Except.bind]
  rfl

/-- Among ID blocks that do not overlap, the search for an ID finds the block that holds it. -/
private theorem find?_of_pairwise {length : Capability → Nat} :
    ∀ {offsets : List (Capability × Nat)},
      offsets.Pairwise (fun p q => p.2 + length p.1 ≤ q.2) →
      ∀ {entry : Capability × Nat}, entry ∈ offsets → ∀ {id : Nat},
        entry.2 ≤ id → id < entry.2 + length entry.1 →
        offsets.find? (fun e => e.2 ≤ id && id < e.2 + length e.1) = some entry
  | [], _, _, member, _, _, _ => by simp at member
  | a :: offsets, disjoint, entry, member, id, low, high => by
    rw [List.pairwise_cons] at disjoint
    rcases List.mem_cons.mp member with rfl | member
    · simp [low, high]
    · have := disjoint.1 entry member
      rw [List.find?_cons_of_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
      exact find?_of_pairwise disjoint.2 member low high

/-- An ID that a shared capability holds routes to that capability, at its relative ID. -/
theorem route_negotiate {length : Capability → Nat} {ours theirs : List Capability}
    {capability : Capability} {base i : Nat}
    (member : (capability, base) ∈ negotiate length ours theirs) (within : i < length capability) :
    route length (negotiate length ours theirs) (base + i) = some (capability, i) := by
  rw [route, find?_of_pairwise (pairwise_negotiate length ours theirs) member (by simp)
    (by simpa using within)]
  simp

/-- Two IDs that route to one capability and relative ID are equal. -/
theorem route_injective {length : Capability → Nat} {ours theirs : List Capability}
    {first second : Nat} {target : Capability × Nat}
    (routedFirst : route length (negotiate length ours theirs) first = some target)
    (routedSecond : route length (negotiate length ours theirs) second = some target) :
    first = second := by
  simp only [route, Option.map_eq_some_iff] at routedFirst routedSecond
  obtain ⟨e₁, h₁, rfl⟩ := routedFirst
  obtain ⟨e₂, h₂, he⟩ := routedSecond
  have m₁ := List.mem_of_find?_eq_some h₁
  have m₂ := List.mem_of_find?_eq_some h₂
  have p₁ := List.find?_some h₁
  have p₂ := List.find?_some h₂
  simp only [Bool.and_eq_true, decide_eq_true_eq] at p₁ p₂
  simp only [Prod.mk.injEq] at he
  -- The negotiated capabilities are distinct, so one capability names one entry.
  have nodup : ((negotiate length ours theirs).map Prod.fst).Nodup := by
    rw [map_fst_negotiate]
    exact (pairwise_sharedCapabilities ours theirs).imp fun {a b} hab (e : a = b) =>
      List.lt_irrefl _ (e ▸ hab)
  have := List.inj_on_of_nodup_map nodup m₂ m₁ he.1
  subst this
  omega

/-- Both peers route every ID the same way, since both negotiate the same IDs. -/
theorem route_comm (length : Capability → Nat) (ours theirs : List Capability) :
    route length (negotiate length ours theirs) = route length (negotiate length theirs ours) := by
  rw [negotiate_comm]

/-- No ID below `0x10` routes to a shared capability. -/
theorem route_negotiate_of_lt {length : Capability → Nat} {ours theirs : List Capability} {id : Nat}
    (below : id < BASE_PROTOCOL_LENGTH) :
    route length (negotiate length ours theirs) id = none := by
  simp only [route, Option.map_eq_none_iff, List.find?_eq_none, Bool.and_eq_true,
    decide_eq_true_eq, not_and, Nat.not_lt]
  intro p hp hle
  have := base_le_of_mem_negotiate hp
  omega

/-- In an active session, a Ping yields exactly one Pong and leaves the session as it was. -/
theorem receive_ping {length : Capability → Nat} {ours mine theirs : Hello} {snappy : Bool}
    {offsets : List (Capability × Nat)} {frame : ByteArray}
    (framed : encodeMessage snappy .ping = .ok frame) :
    receive length ours (.active mine theirs snappy offsets) frame =
      .ok (.active mine theirs snappy offsets, some (.p2p .ping), [.sendPong]) := by
  obtain ⟨rest, hs, hb⟩ := decodeBody_encodeMessage (data := ⟨#[0xc0]⟩) rfl (by decide) framed
  simp only [Message.id] at hs hb
  simp only [receive, hs, hb, Except.mapError, bind, Except.bind]
  rfl

/-- After a Disconnect, every frame is rejected. -/
theorem receive_closed (length : Capability → Nat) (ours : Hello) (reason : Option Nat)
    (frameData : ByteArray) :
    receive length ours (.closed reason) frameData = .error .closed := by
  rfl

/-- Two errors with one code come from one constructor. -/
theorem SessionError.code_injective (e₁ e₂ : SessionError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- A decoding error has a code from 11 to 14, and every other error a code from 1 to 5.
  rcases e₁ with _ | _ | _ | _ | _ | (_ | _ | _ | _) <;>
    rcases e₂ with _ | _ | _ | _ | _ | (_ | _ | _ | _) <;>
    first | rfl | (simp only [SessionError.code, P2pError.code] at h; exact absurd h (by decide))

/-- Two decoding errors with one code come from one constructor of the decoding error. -/
theorem SessionError.code_message {e₁ e₂ : P2pError}
    (h : (SessionError.message e₁).code = (SessionError.message e₂).code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [SessionError.code, P2pError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Devp2p
