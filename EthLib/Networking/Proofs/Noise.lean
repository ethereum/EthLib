module

public import EthLib.Networking.Noise.Identity

/-!
# Proofs: libp2p Noise authentication

Completion verifies the identity signature on a static key read from the received message.

The reported public key, signature and extensions are the fields of the decrypted payload.

The reported peer ID is derived from that public key.

Reading message 2 or 3 accepts only a payload signed over the static key the message carries.
-/

public section

namespace EthLib.Networking.Noise

/-- Successful authentication decodes the payload into the fields it reports. -/
theorem authenticatePayload_decode {staticKey : Key} {bytes : ByteArray}
    {remote : AuthenticatedRemote staticKey}
    (h : authenticatePayload staticKey bytes = .ok remote) :
    decodePayload bytes = .ok ⟨remote.publicKey, remote.signature, remote.extensions⟩ := by
  unfold authenticatePayload at h
  cases hd : decodePayload bytes with
  | error error => simp [hd, bind, Except.bind] at h
  | ok p =>
    simp only [hd] at h
    dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h
    · cases h
      rfl
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Completion reports the fields of a payload whose signature verifies on the received key.

The static key is the one that the stored message decrypts to.

The theorem says nothing about the transport keys of a state that the caller assembled. -/
theorem complete_authenticates (s : Libp2pState) (staticKey : Key)
    (publicKey peerId signature : ByteArray) (extensions : Option ByteArray)
    (h : complete s = .ok (staticKey, (publicKey, peerId, signature, extensions))) :
    s.handshake.step = 3 ∧ ∃ before message received payload,
      s.remoteMessage = some (before, message) ∧
      readMessage before message = .ok (received, payload) ∧
      decodePayload payload = .ok ⟨publicKey, signature, extensions⟩ ∧
      received.remoteStatic = some staticKey ∧
      s.handshake.remoteStatic = some staticKey ∧
      Libp2p.verify publicKey (signedStatic staticKey) signature = true ∧
      peerId = Libp2p.peerId publicKey := by
  unfold complete at h
  split at h
  · rename_i hstep
    cases hm : s.remoteMessage with
    | none => simp [hm, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some saved =>
      obtain ⟨before, message⟩ := saved
      simp only [hm] at h
      dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
      by_cases hphase : before.initiator = s.handshake.initiator ∧
          before.step = (if s.handshake.initiator then 1 else 2)
      · rw [ite_eq_left hphase] at h
        cases hr : readMessage before message with
        | error error => simp [hr] at h
        | ok result =>
          obtain ⟨received, payload⟩ := result
          simp only [hr] at h
          by_cases hreceived : received.step = (if s.handshake.initiator then 2 else 3)
          · rw [ite_eq_left hreceived] at h
            cases hs : received.remoteStatic with
            | none => simp [hs, requireKey] at h
            | some remote =>
              simp only [hs, requireKey] at h
              by_cases hstatic : s.handshake.remoteStatic = some remote
              · rw [ite_eq_left hstatic] at h
                cases ha : authenticatePayload remote payload with
                | error error => simp [ha] at h
                | ok authenticated =>
                  simp only [ha] at h
                  change Except.ok (remote, remoteInfo authenticated) = _ at h
                  cases h
                  exact ⟨hstep, before, message, received, payload, rfl, hr,
                    authenticatePayload_decode ha, hs, hstatic, authenticated.verified, rfl⟩
              · simp [hstatic, throw, throwThe, MonadExceptOf.throw] at h
          · simp [hreceived, throw, throwThe, MonadExceptOf.throw] at h
      · simp [hphase, throw, throwThe, MonadExceptOf.throw] at h
  · simp_all

/-- Reading message 2 or 3 accepts only a payload signed over the static key the message carries.

The new state keeps the message and the state that read it, for completion. -/
theorem readLibp2p_authenticates {s next : Libp2pState} {message : ByteArray}
    (h : readLibp2p s message = .ok next) (hstep : next.handshake.step ≠ 1) :
    ∃ payload staticKey publicKey signature extensions,
      readMessage s.handshake message = .ok (next.handshake, payload) ∧
      next.handshake.remoteStatic = some staticKey ∧
      next.remoteMessage = some (s.handshake, message) ∧
      decodePayload payload = .ok ⟨publicKey, signature, extensions⟩ ∧
      Libp2p.verify publicKey (signedStatic staticKey) signature = true := by
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
          exact ⟨payload, staticKey, remote.publicKey, remote.signature, remote.extensions,
            rfl, hs, rfl, authenticatePayload_decode ha, remote.verified⟩

end EthLib.Networking.Noise
