module

public import EthLib.Networking.Noise.Identity

/-!
# Proofs: libp2p Noise authentication

Completion verifies the identity signature on a static key read from the received message.

The reported peer ID is derived from that signature's public key.
-/

public section

namespace EthLib.Networking.Noise

/-- Completion reports an identity verified against a static key read from the encrypted message. -/
theorem complete_authenticates (s : Libp2pState) (staticKey : Key)
    (publicKey peerId signature : ByteArray) (extensions : Option ByteArray)
    (h : complete s = .ok (staticKey, (publicKey, peerId, signature, extensions))) :
    s.handshake.step = 3 ∧ ∃ before message received payload,
      s.remoteMessage = some (before, message) ∧
      readMessage before message = .ok (received, payload) ∧
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
                  exact ⟨hstep, before, message, received, payload,
                    rfl, hr, hs, hstatic, authenticated.verified, rfl⟩
              · simp [hstatic, throw, throwThe, MonadExceptOf.throw] at h
          · simp [hreceived, throw, throwThe, MonadExceptOf.throw] at h
      · simp [hphase, throw, throwThe, MonadExceptOf.throw] at h
  · simp_all

end EthLib.Networking.Noise
