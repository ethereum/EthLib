module

public import EthLib.Networking.Noise.Identity
public import EthLib.Networking.Proofs.Noise
public import EthLib.Networking.Proofs.Libp2p.PeerId

/-!
# Proofs: libp2p Noise authentication

Reading message 2 or 3 accepts only a payload signed over the static key the message carries.

The state then keeps that remote, so completion only returns it with the transport ciphers.

Completion checks that the remote has the remote static key of the handshake.

In a state that the libp2p functions produce, the stored remote has that key.

Its signature verifies on that key, the key of the handshake that gives the transport ciphers.

Such a state at step 3 always holds a remote, so completion succeeds.
-/

public section

namespace EthLib.Networking.Noise

open EthLib.Cryptography.Secp256k1 (Fn)

/-- Successful authentication keeps the static key, and the fields of the decoded payload.

The signature verifies on that static key, and the public key decodes to the stored point. -/
theorem authenticatePayload_ok {staticKey : Key} {bytes : ByteArray} {remote : Remote}
    (h : authenticatePayload staticKey bytes = .ok remote) :
    remote.staticKey = staticKey ∧
      decodePayload bytes = .ok ⟨remote.publicKey, remote.signature, remote.extensions⟩ ∧
      Libp2p.verify remote.publicKey (signedStatic staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  unfold authenticatePayload at h
  cases hd : decodePayload bytes with
  | error error => simp [hd, bind, Except.bind] at h
  | ok p =>
    simp only [hd] at h
    dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h
    · rename_i hv
      split at h
      · rename_i key hk
        cases h
        have hpk : Remote.publicKey ⟨staticKey, key, p.signature, p.extensions⟩ = p.publicKey :=
          Proofs.Libp2p.PeerId.encodePublicKey_of_decodePublicKey hk
        refine ⟨rfl, ?_, ?_, ?_⟩
        · rw [hpk]
        · rw [hpk]; exact hv
        · rw [hpk]; exact hk
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Completion returns the stored remote and the transport ciphers of the same state.

The remote has the remote static key of that state's handshake. -/
theorem complete_ok {s : Libp2pState} {remote : Remote} {send receive : CipherState}
    (h : complete s = .ok (remote, send, receive)) :
    s.remote = some remote ∧ s.handshake.remoteStatic = some remote.staticKey ∧
      transport s.handshake = .ok (send, receive) := by
  unfold complete at h
  cases ht : transport s.handshake with
  | error e => simp [ht, bind, Except.bind] at h
  | ok p =>
    obtain ⟨a, b⟩ := p
    cases hr : s.remote with
    | none => simp [ht, hr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      by_cases hk : s.handshake.remoteStatic = some r.staticKey
      · simp [ht, hr, hk, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, hk, rfl⟩
      · simp [ht, hr, hk, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- Reading message 2 or 3 accepts only a payload signed over the static key the message carries.

The new state keeps the remote of that payload. -/
theorem readLibp2p_authenticates {s next : Libp2pState} {message : ByteArray}
    (h : readLibp2p s message = .ok next) (hstep : next.handshake.step ≠ 1) :
    ∃ payload remote,
      readMessage s.handshake message = .ok (next.handshake, payload) ∧
      next.remote = some remote ∧
      next.handshake.remoteStatic = some remote.staticKey ∧
      decodePayload payload = .ok ⟨remote.publicKey, remote.signature, remote.extensions⟩ ∧
      Libp2p.verify remote.publicKey (signedStatic remote.staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  unfold readLibp2p at h
  cases hr : readMessage s.handshake message with
  | error error => simp [hr, bind, Except.bind] at h
  | ok result =>
    obtain ⟨handshake, payload⟩ := result
    simp only [hr] at h
    dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h
    · rename_i hone
      cases hd : decodePayload payload with
      | error error => simp [hd] at h
      | ok first =>
        simp only [hd] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases h
          exact absurd hone hstep
    · cases hs : handshake.remoteStatic with
      | none => simp [hs, requireKey] at h
      | some staticKey =>
        simp only [hs, requireKey] at h
        cases ha : authenticatePayload staticKey payload with
        | error error => simp [ha] at h
        | ok remote =>
          simp only [ha] at h
          cases h
          obtain ⟨hkey, hdecode, hverify, hpoint⟩ := authenticatePayload_ok ha
          subst hkey
          exact ⟨payload, remote, rfl, rfl, hs, hdecode, hverify, hpoint⟩

/-- Writing a libp2p message writes an XX message and keeps the remote. -/
theorem writeLibp2p_ok {s next : Libp2pState} {identitySecret : Fn}
    {extensions : Option ByteArray} {message : ByteArray}
    (h : writeLibp2p s identitySecret extensions = .ok (next, message)) :
    ∃ payload handshake, writeMessage s.handshake payload = .ok (handshake, message) ∧
      next = { s with handshake := handshake } := by
  unfold writeLibp2p at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (rename_i hw; cases h; exact ⟨_, _, hw, rfl⟩)
    | cases h

/-- Reading a libp2p message reads an XX message, and message 1 leaves no remote. -/
theorem readLibp2p_ok {s next : Libp2pState} {message : ByteArray}
    (h : readLibp2p s message = .ok next) :
    (∃ payload, readMessage s.handshake message = .ok (next.handshake, payload)) ∧
      (next.handshake.step = 1 → next.remote = none) := by
  unfold readLibp2p at h
  cases hr : readMessage s.handshake message with
  | error error => simp [hr, bind, Except.bind] at h
  | ok result =>
    obtain ⟨handshake, payload⟩ := result
    simp only [hr] at h
    dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h
    · cases hd : decodePayload payload with
      | error error => simp [hd] at h
      | ok first =>
        simp only [hd] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases h
          exact ⟨⟨payload, rfl⟩, fun _ => rfl⟩
    · rename_i hone
      cases hs : handshake.remoteStatic with
      | none => simp [hs, requireKey] at h
      | some staticKey =>
        simp only [hs, requireKey] at h
        cases ha : authenticatePayload staticKey payload with
        | error error => simp [ha] at h
        | ok remote =>
          simp only [ha] at h
          cases h
          exact ⟨⟨payload, rfl⟩, fun hstep => absurd hstep hone⟩

/-- A state that the libp2p functions produce from an initial state. -/
inductive Produced : Libp2pState → Prop where
  /-- An initial state. -/
  | init (initiator : Bool) (staticKey ephemeralKey : Key) :
    Produced (initializeLibp2p initiator staticKey ephemeralKey)
  /-- The state after a successful write. -/
  | write {s next : Libp2pState} {identitySecret : Fn} {extensions : Option ByteArray}
    {message : ByteArray} (hs : Produced s)
    (h : writeLibp2p s identitySecret extensions = .ok (next, message)) : Produced next
  /-- The state after a successful read. -/
  | read {s next : Libp2pState} {message : ByteArray} (hs : Produced s)
    (h : readLibp2p s message = .ok next) : Produced next

/-- In a produced state, the remote has the static key of the handshake.

Its signature verifies on that key, and its public key decodes to its point. -/
theorem Produced.remote_ok {s : Libp2pState} {remote : Remote} (hs : Produced s)
    (h : s.remote = some remote) :
    s.handshake.remoteStatic = some remote.staticKey ∧
      Libp2p.verify remote.publicKey (signedStatic remote.staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  induction hs generalizing remote with
  | init => simp [initializeLibp2p] at h
  | write _ hw ih =>
    obtain ⟨payload, handshake, hwm, rfl⟩ := writeLibp2p_ok hw
    obtain ⟨-, -, hstatic, -⟩ := writeMessage_ok hwm
    obtain ⟨h1, h2, h3⟩ := ih h
    exact ⟨hstatic.trans h1, h2, h3⟩
  | @read _ next _ _ hr _ =>
    by_cases hone : next.handshake.step = 1
    · simp [(readLibp2p_ok hr).2 hone] at h
    · obtain ⟨_, r, -, hrem, hstatic, -, hverify, hpoint⟩ := readLibp2p_authenticates hr hone
      rw [hrem] at h
      cases h
      exact ⟨hstatic, hverify, hpoint⟩

/-- A produced state holds a remote once the handshake has read the remote's static key.

The initiator reads it in message 2, and the responder in message 3. -/
theorem Produced.remote_isSome {s : Libp2pState} (hs : Produced s)
    (hstep : s.handshake.initiator = true ∧ 2 ≤ s.handshake.step ∨
      s.handshake.initiator = false ∧ s.handshake.step = 3) :
    s.remote.isSome := by
  induction hs with
  | init => simp [initializeLibp2p, initializeHandshake] at hstep
  | write _ hw ih =>
    obtain ⟨payload, handshake, hwm, rfl⟩ := writeLibp2p_ok hw
    obtain ⟨hi, hst, -, hphase⟩ := writeMessage_ok hwm
    simp only [hi, hst] at hstep
    apply ih
    rcases hphase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2] at hstep ⊢
  | @read _ next _ _ hr _ =>
    have hone : next.handshake.step ≠ 1 := by omega
    obtain ⟨_, r, -, hrem, -⟩ := readLibp2p_authenticates hr hone
    simp [hrem]

/-- Completion of a produced state after message 3 succeeds. -/
theorem Produced.complete_isOk {s : Libp2pState} (hs : Produced s) (hstep : s.handshake.step = 3) :
    (complete s).isOk := by
  have hsome := hs.remote_isSome (by cases s.handshake.initiator <;> simp [hstep])
  obtain ⟨remote, hr⟩ := Option.isSome_iff_exists.mp hsome
  simp [complete, transport, hstep, hr, (hs.remote_ok hr).1, bind, Except.bind, pure, Except.pure,
    Except.isOk, Except.toBool]

/-- Completion of a produced state returns the transport ciphers of its handshake.

The returned remote has the remote static key of that handshake.

Its signature verifies on that static key. -/
theorem Produced.complete_authenticates {s : Libp2pState} {remote : Remote}
    {send receive : CipherState} (hs : Produced s)
    (h : complete s = .ok (remote, send, receive)) :
    transport s.handshake = .ok (send, receive) ∧
      s.handshake.remoteStatic = some remote.staticKey ∧
      Libp2p.verify remote.publicKey (signedStatic remote.staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  obtain ⟨hrem, -, ht⟩ := complete_ok h
  obtain ⟨h1, h2, h3⟩ := hs.remote_ok hrem
  exact ⟨ht, h1, h2, h3⟩

end EthLib.Networking.Noise
