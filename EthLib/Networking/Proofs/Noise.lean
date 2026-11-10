module

public import EthLib.Cryptography.Proofs.Hash.Hkdf
public import EthLib.Networking.Noise

/-!
# Proofs: Noise XX

[Noise revision 34, §4.3](https://noiseprotocol.org/noise_rev34.pdf) computes two outputs from HMAC.

Its note calls this function HKDF of [RFC 5869](https://www.rfc-editor.org/rfc/rfc5869#section-2).

There the chaining key is the salt, and the info is empty.

So the two outputs are the first 64 bytes of that HKDF.

Distinct kinds of handshake error have distinct codes.

Each message keeps the role, advances the step by one, and comes at the step XX gives that role.

The pattern is [Noise revision 34, §7.5](https://noiseprotocol.org/noise_rev34.pdf).
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Base
open EthLib.Cryptography.Hash

/-- The two outputs are the first 64 bytes of HKDF, with the chaining key as salt and empty info. -/
theorem hkdf_eq_hkdf2 (chainingKey : ChainingKey) (input : ByteArray) :
    Hkdf.hkdf (packBytes chainingKey.bytes) input .empty 64 =
      .ok (packBytes (hkdf2 chainingKey input).1 ++ packBytes (hkdf2 chainingKey input).2) := by
  have hprk : Hkdf.HASH_LEN ≤ (Hkdf.extract (packBytes chainingKey.bytes) input).size := by
    simp [Hkdf.extract, Hkdf.HASH_LEN]
  rw [Hkdf.hkdf, Hkdf.expand_eq hprk (by decide)]
  simp only [show (64 + Hkdf.HASH_LEN - 1) / Hkdf.HASH_LEN = 2 from rfl]
  rw [show 64 = (Hkdf.blocks (Hkdf.extract (packBytes chainingKey.bytes) input) .empty 2).size by
    rw [Hkdf.blocks_size]; rfl, ByteArray.extract_zero_size]
  -- The two blocks of RFC 5869 are the two outputs, with the empty info dropped.
  congr 1

/-- Two errors with one code are of the same kind. -/
theorem NoiseError.code_injective (e₁ e₂ : NoiseError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [NoiseError.code] at h; exact absurd h (by decide))

/-- Writing keeps the role and the remote static key, and advances the step by one.

XX writes only message 1 or 3 as initiator, and message 2 as responder, Noise §7.5. -/
theorem writeMessage_ok {s next : HandshakeState} {payload message : ByteArray}
    (h : writeMessage s payload = .ok (next, message)) :
    next.initiator = s.initiator ∧ next.step = s.step + 1 ∧
      next.remoteStatic = s.remoteStatic ∧
      (s.initiator = true ∧ s.step = 0 ∨ s.initiator = false ∧ s.step = 1 ∨
        s.initiator = true ∧ s.step = 2) := by
  dsimp only [writeMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  cases h
  refine ⟨rfl, rfl, rfl, ?_⟩
  split at hv
  next _ _ hi hs => exact .inl ⟨hi, hs⟩
  next _ _ hi hs => exact .inr (.inl ⟨hi, hs⟩)
  next _ _ hi hs => exact .inr (.inr ⟨hi, hs⟩)
  next => cases hv

/-- Reading keeps the role and advances the step by one.

XX reads only message 1 or 3 as responder, and message 2 as initiator, Noise §7.5. -/
theorem readMessage_ok {s next : HandshakeState} {message payload : ByteArray}
    (h : readMessage s message = .ok (next, payload)) :
    next.initiator = s.initiator ∧ next.step = s.step + 1 ∧
      (s.initiator = false ∧ s.step = 0 ∨ s.initiator = true ∧ s.step = 1 ∨
        s.initiator = false ∧ s.step = 2) := by
  dsimp only [readMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  cases h
  split at hv
  next _ _ hi hs => (repeat' split at hv) <;> cases hv <;> exact ⟨rfl, rfl, .inl ⟨hi, hs⟩⟩
  next _ _ hi hs => (repeat' split at hv) <;> cases hv <;> exact ⟨rfl, rfl, .inr (.inl ⟨hi, hs⟩)⟩
  next _ _ hi hs => (repeat' split at hv) <;> cases hv <;> exact ⟨rfl, rfl, .inr (.inr ⟨hi, hs⟩)⟩
  next => cases hv

end EthLib.Networking.Noise
