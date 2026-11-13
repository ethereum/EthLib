module

public import EthLib.Networking.Proofs.Noise.Handshake
public import EthLib.Networking.Proofs.Noise.Identity

/-!
# Proofs: two honest peers complete the libp2p Noise handshake

The libp2p suite of [noise-libp2p][libp2p] runs XX with an identity payload in messages 2 and 3.

Each payload holds a secp256k1 identity key and its signature over the sender's prefixed static key.

When both peers follow the specification, each read of message 2 or 3 accepts the other's payload.

Completion then returns the identity of the other peer, with swapped transport ciphers.

[libp2p]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md#the-libp2p-handshake-payload
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1 (Fn Point)

/-- A payload that is made has a nonzero secret.

It encodes the key of that secret and a signature over the prefixed static key. -/
private theorem makePayload_eq {k : Fn} {staticKey : Key} {x : Option ByteArray}
    {q : ByteArray} (h : makePayload k staticKey x = .ok q) :
    k ≠ 0 ∧ ∃ signature, Libp2p.sign k (signedStatic staticKey) = .ok signature ∧
      encodePayload ⟨Libp2p.encodePublicKey (Point.mul k .generator), signature, x⟩ = .ok q := by
  unfold makePayload Libp2p.publicKey at h
  by_cases hk : k = 0
  · simp [hk, Except.mapError, bind, Except.bind] at h
  · refine ⟨hk, ?_⟩
    cases hs : Libp2p.sign k (signedStatic staticKey) with
    | error e => simp [hk, hs, Except.mapError, bind, Except.bind] at h
    | ok sig => exact ⟨sig, rfl, by simpa [hk, hs, Except.mapError, bind, Except.bind] using h⟩

/-- A payload that a secret makes authenticates to the key of that secret, with its extensions. -/
private theorem authenticatePayload_of_makePayload {k : Fn} {staticKey : Key}
    {x : Option ByteArray} {q : ByteArray} (h : makePayload k staticKey x = .ok q) :
    ∃ signature, authenticatePayload staticKey q =
      .ok ⟨staticKey, Point.mul k .generator, signature, x⟩ := by
  obtain ⟨hk, sig, hs, he⟩ := makePayload_eq h
  refine ⟨sig, ?_⟩
  have hv := Proofs.Libp2p.PeerId.verify_sign hs
  have hd := Proofs.Libp2p.PeerId.decodePublicKey_encodePublicKey
    (Point.isOnCurve_mul k Point.isOnCurve_generator)
    (Secp256k1.Ecdsa.mul_generator_ne_infinity hk)
  simp [authenticatePayload, decodePayload_encodePayload he, hv, hd, bind, Except.bind, pure,
    Except.pure]

/-- Writing a handshake message keeps the local static key. -/
private theorem staticKey_of_writeMessage {s next : HandshakeState} {payload message : ByteArray}
    (h : writeMessage s payload = .ok (next, message)) : next.staticKey = s.staticKey := by
  dsimp only [writeMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  rfl

/-- Reading a handshake message keeps the local static key. -/
private theorem staticKey_of_readMessage {s next : HandshakeState} {message payload : ByteArray}
    (h : readMessage s message = .ok (next, payload)) : next.staticKey = s.staticKey := by
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
  split at hv <;> (repeat' split at hv) <;> cases hv <;> rfl

/-- Two honest libp2p peers complete XX, and each returns the identity of the other.

The secrets `si`, `ei` and the identity secret `ki` are those of the initiator.

The secrets `sr`, `er` and the identity secret `kr` are those of the responder.

Making each identity payload must succeed.

Each payload must fit in a message of at most 65535 bytes, with the keys and tags of its message.

Message 1 carries an empty payload, since noise-libp2p puts no identity in it.

Making a payload fails on the zero secret, so both identity secrets are nonzero.

The initiator's remote has the responder's static key, identity key and extensions.

The responder's remote has the initiator's, and the two pairs of ciphers are swapped. -/
theorem libp2p_complete (si ei sr er : Key) (ki kr : Fn)
    (x₂ x₃ : Option ByteArray) (q₂ q₃ : ByteArray)
    (hq₂ : makePayload kr (X25519.publicKey sr) x₂ = .ok q₂)
    (hq₃ : makePayload ki (X25519.publicKey si) x₃ = .ok q₃)
    (h₂ : q₂.size + 96 ≤ 65535) (h₃ : q₃.size + 64 ≤ 65535) :
    ∃ (i₁ i₂ i₃ r₁ r₂ r₃ : Libp2pState) (m₁ m₂ m₃ : ByteArray)
      (remoteR remoteI : Remote) (c₁ c₂ : CipherState),
      writeLibp2p (initializeLibp2p true si ei) ki none = .ok (i₁, m₁) ∧
      readLibp2p (initializeLibp2p false sr er) m₁ = .ok r₁ ∧
      writeLibp2p r₁ kr x₂ = .ok (r₂, m₂) ∧
      readLibp2p i₁ m₂ = .ok i₂ ∧
      writeLibp2p i₂ ki x₃ = .ok (i₃, m₃) ∧
      readLibp2p r₂ m₃ = .ok r₃ ∧
      complete i₃ = .ok (remoteR, c₁, c₂) ∧
      complete r₃ = .ok (remoteI, c₂, c₁) ∧
      remoteR.staticKey = X25519.publicKey sr ∧
      remoteR.key = Point.mul kr .generator ∧
      remoteR.extensions = x₂ ∧
      remoteI.staticKey = X25519.publicKey si ∧
      remoteI.key = Point.mul ki .generator ∧
      remoteI.extensions = x₃ := by
  obtain ⟨I₁, I₂, I₃, R₁, R₂, R₃, m₁, m₂, m₃, c₁, c₂, hw₁, hr₁, hw₂, hr₂, hw₃, hr₃, -, hsI, hsR,
    htI, htR⟩ := handshake_complete si ei sr er .empty .empty q₂ q₃ (by simp) h₂ h₃
  obtain ⟨hkr, -⟩ := makePayload_eq hq₂
  obtain ⟨hki, -⟩ := makePayload_eq hq₃
  obtain ⟨g₂, ha₂⟩ := authenticatePayload_of_makePayload hq₂
  obtain ⟨g₃, ha₃⟩ := authenticatePayload_of_makePayload hq₃
  obtain ⟨-, sI₁, -⟩ := writeMessage_ok hw₁
  obtain ⟨-, sR₁, -⟩ := readMessage_ok hr₁
  obtain ⟨-, sR₂, -⟩ := writeMessage_ok hw₂
  obtain ⟨-, sI₂, -⟩ := readMessage_ok hr₂
  obtain ⟨-, sI₃, hsI₂, -⟩ := writeMessage_ok hw₃
  obtain ⟨-, sR₃, -⟩ := readMessage_ok hr₃
  have e₁ : I₁.step = 1 := by rw [sI₁]; rfl
  have e₂ : I₂.step = 2 := by rw [sI₂, e₁]
  have f₁ : R₁.step = 1 := by rw [sR₁]; rfl
  have f₂ : R₂.step = 2 := by rw [sR₂, f₁]
  have f₃ : R₃.step = 3 := by rw [sR₃, f₂]
  have kR₁ : R₁.staticKey = sr := staticKey_of_readMessage hr₁
  have kI₂ : I₂.staticKey = si :=
    (staticKey_of_readMessage hr₂).trans (staticKey_of_writeMessage hw₁)
  have hdec : decodePayload .empty = .ok {} := rfl
  let remoteR : Remote := ⟨X25519.publicKey sr, Point.mul kr .generator, g₂, x₂⟩
  let remoteI : Remote := ⟨X25519.publicKey si, Point.mul ki .generator, g₃, x₃⟩
  refine ⟨⟨I₁, none⟩, ⟨I₂, some remoteR⟩, ⟨I₃, some remoteR⟩, ⟨R₁, none⟩, ⟨R₂, none⟩,
    ⟨R₃, some remoteI⟩, m₁, m₂, m₃, remoteR, remoteI, c₁, c₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h0 : (initializeHandshake true si ei ByteArray.empty).step = 0 := rfl
    simp only [writeLibp2p, initializeLibp2p, hki, h0, ↓reduceIte, Option.isSome_none,
      Bool.false_eq_true, bind, Except.bind, pure, Except.pure, hw₁]
  · simp [readLibp2p, initializeLibp2p, hr₁, f₁, hdec, bind, Except.bind, pure, Except.pure]
  · simp [writeLibp2p, hkr, f₁, kR₁, hq₂, hw₂, bind, Except.bind, pure, Except.pure]
  · simp [readLibp2p, hr₂, e₂, ← hsI₂, hsI, requireKey, ha₂, remoteR, bind, Except.bind, pure,
      Except.pure]
  · simp [writeLibp2p, hki, e₂, kI₂, hq₃, hw₃, bind, Except.bind, pure, Except.pure]
  · simp [readLibp2p, hr₃, f₃, hsR, requireKey, ha₃, remoteI, bind, Except.bind, pure,
      Except.pure]
  · simp [complete, htI, hsI, remoteR, bind, Except.bind, pure, Except.pure]
  · simp [complete, htR, hsR, remoteI, bind, Except.bind, pure, Except.pure]

end EthLib.Networking.Noise
