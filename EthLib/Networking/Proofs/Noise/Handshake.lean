module

public import EthLib.Networking.Proofs.Noise
public import EthLib.Cryptography.Proofs.X25519.Agreement

/-!
# Proofs: two honest peers complete a Noise XX handshake

The XX pattern of [Noise revision 34, §7.5][noise] sends three messages.

- `-> e`
- `<- e, ee, s, es`
- `-> s, se`

Each token `ee`, `es` and `se` mixes one X25519 shared secret into the chaining key.

The two peers compute it from opposite ends, and X25519 key agreement makes the two values equal.

So two peers that follow the specification complete the handshake when each payload fits.

Each read then returns the payload that the other peer wrote.

Both peers end with the same symmetric state, and each learns the static public key of the other.

The send cipher of each peer is then the receive cipher of the other.

For each message, the chaining key mixes the X25519 outputs that the token rules name.

[noise]: https://noiseprotocol.org/noise_rev34.pdf
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Base
open EthLib.Cryptography

/-- The AEAD accepts a plaintext of at most `(2 ^ 32 - 1) * 64` bytes, the reach of its counter.

It also accepts associated data below `2 ^ 64` bytes. -/
private theorem encrypt_ok (key : ChaCha20Poly1305.Key) (nonce : ChaCha20Poly1305.Nonce)
    (aad plaintext : ByteArray) (ha : aad.size < 2 ^ 64)
    (hp : plaintext.size ≤ (2 ^ 32 - 1) * 64) :
    ∃ c t, ChaCha20Poly1305.encrypt key nonce aad plaintext = .ok (c, t) := by
  unfold ChaCha20Poly1305.encrypt ChaCha20Poly1305.checkLengths ChaCha20Poly1305.crypt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by simp; omega)]
  exact ⟨_, _, rfl⟩

/-- Without a key, a payload within 65535 bytes is sent as is and hashed. -/
private theorem encryptAndHash_of_key_none {s : SymmetricState} {p : ByteArray}
    (hk : s.cipher.key = none) (hp : p.size ≤ 65535) :
    encryptAndHash s p = .ok (mixHash s p, p) := by
  unfold encryptAndHash
  rw [encryptWithAd_eq_ok_of_key_eq_none hk (by omega)]
  rfl

/-- Under a key and a nonce below the reserved one, a short plaintext encrypts to 16 more bytes. -/
private theorem encryptAndHash_of_key_some {s : SymmetricState} {p : ByteArray}
    {key : ChaCha20Poly1305.Key} (hk : s.cipher.key = some key)
    (hn : ¬s.cipher.nonce = 2 ^ 64 - 1) (hp : p.size + 16 ≤ 65535) :
    ∃ next c, c.size = p.size + 16 ∧ next.cipher = ⟨some key, s.cipher.nonce + 1⟩ ∧
      encryptAndHash s p = .ok (next, c) := by
  obtain ⟨c, t, he⟩ := encrypt_ok key (cipherNonce s.cipher.nonce) (packBytes s.hash.bytes) p
    (by simp) (by omega)
  refine ⟨mixHash { s with cipher := ⟨some key, s.cipher.nonce + 1⟩ } (c ++ packBytes t),
    c ++ packBytes t, ?_, rfl, ?_⟩
  · rw [ByteArray.size_append, size_packBytes, ChaCha20Poly1305.encrypt_size _ _ _ _ _ _ he]
  · unfold encryptAndHash
    rw [encryptWithAd_eq_ok_of_encrypt hk (by omega) hn he]
    rfl

/-- Mixing a key installs the second HKDF output as the cipher key, with nonce 0. -/
private theorem mixKey_cipher (s : SymmetricState) (input : Key) :
    (mixKey s input).cipher = ⟨some (hkdf2 s.chainingKey (packBytes input)).2, 0⟩ := rfl

/-- Nonce 0 is not the reserved greatest nonce. -/
private theorem zero_ne_max : ¬(0 : UInt64) = 2 ^ 64 - 1 := by decide +kernel

/-- The nonce after one message is not the reserved greatest nonce. -/
private theorem one_ne_max : ¬(0 + 1 : UInt64) = 2 ^ 64 - 1 := by decide +kernel

/-- A 32-byte key read back from its bytes is that key. -/
private theorem readKey_packBytes (v : Key) : readKey (packBytes v) = .ok v := by
  unfold readKey
  rw [dite_eq_left (size_packBytes v)]
  rfl

/-- The first 32 bytes of a key followed by other bytes are that key. -/
private theorem readBytes_packBytes_append (v : Key) (q : ByteArray) (h) :
    readBytes (packBytes v ++ q) 0 32 h = v := by
  apply Vector.ext
  intro i hi
  simp only [readBytes, Vector.getElem_ofFn, ByteArray.data_append]
  rw [Array.getElem_append_left (by simp [packBytes]; omega)]
  simp [packBytes]

/-- The first 32 bytes of a key followed by two other byte arrays are that key. -/
private theorem readBytes_packBytes_append_append (v : Key) (q r : ByteArray) (h) :
    readBytes (packBytes v ++ q ++ r) 0 32 h = v := by
  apply Vector.ext
  intro i hi
  simp only [readBytes, Vector.getElem_ofFn, ByteArray.data_append]
  rw [Array.getElem_append_left (by simp [packBytes]; omega),
    Array.getElem_append_left (by simp [packBytes]; omega)]
  simp [packBytes]

/-- The middle part of three appended byte arrays is cut out by its bounds. -/
private theorem extract_append_append_mid {a b c : ByteArray} {i j : Nat} (hi : i = a.size)
    (hj : j = a.size + b.size) : (a ++ b ++ c).extract i j = b := by
  have h := ByteArray.extract_append_size_add (a := a) (b := b ++ c) (i := 0) (j := b.size)
  rw [Nat.add_zero] at h
  rw [hi, hj, ByteArray.append_assoc, h, ByteArray.extract_append_eq_left rfl]

/-- Two honest peers complete XX, and each returns the payload that the other wrote.

The secrets `si`, `ei` are those of the initiator, and `sr`, `er` those of the responder.

Both peers hash the same prologue.

Each payload must fit in a message of at most 65535 bytes, with the keys and tags of its message.

Both peers end with the same symmetric state and swapped ciphers.

Each stores the static public key of the other. -/
theorem handshake_complete (si ei sr er : Key) (prologue p₁ p₂ p₃ : ByteArray)
    (h₁ : p₁.size + 32 ≤ 65535) (h₂ : p₂.size + 96 ≤ 65535) (h₃ : p₃.size + 64 ≤ 65535) :
    ∃ (i₁ i₂ i₃ r₁ r₂ r₃ : HandshakeState) (m₁ m₂ m₃ : ByteArray) (c₁ c₂ : CipherState),
      writeMessage (initializeHandshake true si ei prologue) p₁ = .ok (i₁, m₁) ∧
      readMessage (initializeHandshake false sr er prologue) m₁ = .ok (r₁, p₁) ∧
      writeMessage r₁ p₂ = .ok (r₂, m₂) ∧
      readMessage i₁ m₂ = .ok (i₂, p₂) ∧
      writeMessage i₂ p₃ = .ok (i₃, m₃) ∧
      readMessage r₂ m₃ = .ok (r₃, p₃) ∧
      i₃.symmetric = r₃.symmetric ∧
      i₃.remoteStatic = some (X25519.publicKey sr) ∧
      r₃.remoteStatic = some (X25519.publicKey si) ∧
      transport i₃ = .ok (c₁, c₂) ∧
      transport r₃ = .ok (c₂, c₁) := by
  -- Message 1 carries the ephemeral key of the initiator and the payload, unencrypted.
  have he₁ := encryptAndHash_of_key_none
    (s := mixHash (mixHash initializeSymmetric prologue) (packBytes (X25519.publicKey ei)))
    (p := p₁) rfl (by omega)
  have hw₁ : writeMessage (initializeHandshake true si ei prologue) p₁ = .ok
      (⟨true, si, ei, none, none, 1, mixHash (mixHash (mixHash initializeSymmetric prologue)
        (packBytes (X25519.publicKey ei))) p₁⟩, packBytes (X25519.publicKey ei) ++ p₁) := by
    simp only [writeMessage, initializeHandshake, show ¬(p₁.size + 32 > 65535) by omega,
      ite_false, bind, Except.bind, pure, Except.pure, he₁]
  have hr₁ : readMessage (initializeHandshake false sr er prologue)
      (packBytes (X25519.publicKey ei) ++ p₁) = .ok
      (⟨false, sr, er, none, some (X25519.publicKey ei), 1, mixHash (mixHash
        (mixHash initializeSymmetric prologue) (packBytes (X25519.publicKey ei))) p₁⟩, p₁) := by
    have hs : (packBytes (X25519.publicKey ei) ++ p₁).size = 32 + p₁.size := by
      rw [ByteArray.size_append, size_packBytes]
    have hx : (packBytes (X25519.publicKey ei) ++ p₁).extract 32 (32 + p₁.size) = p₁ :=
      ByteArray.extract_append_eq_right (size_packBytes _).symm (by rw [size_packBytes])
    simp only [readMessage, initializeHandshake, hs, show ¬(32 + p₁.size > 65535) by omega,
      show 32 ≤ 32 + p₁.size by omega, ite_false, dite_true, bind, Except.bind, pure, Except.pure,
      readBytes_packBytes_append, hx, decryptAndHash_encryptAndHash he₁]
  generalize mixHash (mixHash (mixHash initializeSymmetric prologue)
    (packBytes (X25519.publicKey ei))) p₁ = S₁ at hw₁ hr₁
  -- Message 2: both peers mix the same `ee`, then the same `es` after the encrypted static key.
  have hag₁ := X25519.x25519_agree ei er
  have hag₂ := X25519.x25519_agree ei sr
  obtain ⟨B, cs₂, hcs₂, -, hes₂⟩ := encryptAndHash_of_key_some
    (p := packBytes (X25519.publicKey sr))
    (s := mixKey (mixHash S₁ (packBytes (X25519.publicKey er))) (X25519.x25519 er
      (X25519.publicKey ei))) (by rw [mixKey_cipher]) (by rw [mixKey_cipher]; exact zero_ne_max)
    (by rw [size_packBytes]; omega)
  obtain ⟨D, cp₂, hcp₂, hD, hep₂⟩ := encryptAndHash_of_key_some (p := p₂)
    (s := mixKey B (X25519.x25519 sr (X25519.publicKey ei))) (by rw [mixKey_cipher])
    (by rw [mixKey_cipher]; exact zero_ne_max) (by omega)
  have hw₂ : writeMessage ⟨false, sr, er, none, some (X25519.publicKey ei), 1, S₁⟩ p₂ = .ok
      (⟨false, sr, er, none, some (X25519.publicKey ei), 2, D⟩,
        packBytes (X25519.publicKey er) ++ cs₂ ++ cp₂) := by
    simp only [writeMessage, show ¬(p₂.size + 96 > 65535) by omega, ite_false, requireKey,
      bind, Except.bind, pure, Except.pure, hes₂, hep₂]
  have hr₂ : readMessage ⟨true, si, ei, none, none, 1, S₁⟩
      (packBytes (X25519.publicKey er) ++ cs₂ ++ cp₂) = .ok
      (⟨true, si, ei, some (X25519.publicKey sr), some (X25519.publicKey er), 2, D⟩, p₂) := by
    have hs : (packBytes (X25519.publicKey er) ++ cs₂ ++ cp₂).size = p₂.size + 96 := by
      simp only [ByteArray.size_append, size_packBytes]
      rw [size_packBytes] at hcs₂
      omega
    have hx₁ : (packBytes (X25519.publicKey er) ++ cs₂ ++ cp₂).extract 32 80 = cs₂ :=
      extract_append_append_mid (size_packBytes _).symm
        (by rw [size_packBytes, hcs₂, size_packBytes])
    have hx₂ : (packBytes (X25519.publicKey er) ++ cs₂ ++ cp₂).extract 80
        (packBytes (X25519.publicKey er) ++ cs₂ ++ cp₂).size = cp₂ :=
      ByteArray.extract_append_eq_right
        (by rw [ByteArray.size_append, size_packBytes, hcs₂, size_packBytes])
        ByteArray.size_append
    rw [hs] at hx₂
    simp only [readMessage, show ¬(p₂.size + 96 > 65535) by omega, hs,
      show 96 ≤ p₂.size + 96 by omega, ite_false, dite_true, bind, Except.bind, pure,
      Except.pure, readBytes_packBytes_append_append, hag₁, hx₁,
      decryptAndHash_encryptAndHash hes₂, readKey_packBytes, hag₂,
      hx₂, decryptAndHash_encryptAndHash hep₂]
  -- Message 3: both peers mix the same `se` after the encrypted static key of the initiator.
  have hag₃ := X25519.x25519_agree er si
  obtain ⟨E, cs₃, hcs₃, -, hes₃⟩ := encryptAndHash_of_key_some (s := D)
    (p := packBytes (X25519.publicKey si)) (by rw [hD])
    (by rw [hD, mixKey_cipher]; exact one_ne_max) (by rw [size_packBytes]; omega)
  obtain ⟨G, cp₃, hcp₃, -, hep₃⟩ := encryptAndHash_of_key_some (p := p₃)
    (s := mixKey E (X25519.x25519 si (X25519.publicKey er))) (by rw [mixKey_cipher])
    (by rw [mixKey_cipher]; exact zero_ne_max) (by omega)
  have hw₃ : writeMessage ⟨true, si, ei, some (X25519.publicKey sr), some (X25519.publicKey er),
      2, D⟩ p₃ = .ok (⟨true, si, ei, some (X25519.publicKey sr), some (X25519.publicKey er),
        3, G⟩, cs₃ ++ cp₃) := by
    simp only [writeMessage, show ¬(p₃.size + 64 > 65535) by omega, ite_false, requireKey,
      bind, Except.bind, pure, Except.pure, hes₃, hep₃]
  have hr₃ : readMessage ⟨false, sr, er, none, some (X25519.publicKey ei), 2, D⟩
      (cs₃ ++ cp₃) = .ok
      (⟨false, sr, er, some (X25519.publicKey si), some (X25519.publicKey ei), 3, G⟩, p₃) := by
    rw [size_packBytes] at hcs₃
    have hs : (cs₃ ++ cp₃).size = p₃.size + 64 := by
      rw [ByteArray.size_append]
      omega
    have hx₁ : (cs₃ ++ cp₃).extract 0 48 = cs₃ :=
      ByteArray.extract_append_eq_left hcs₃.symm
    have hx₂ : (cs₃ ++ cp₃).extract 48 (p₃.size + 64) = cp₃ :=
      ByteArray.extract_append_eq_right hcs₃.symm (by omega)
    simp only [readMessage, show ¬(p₃.size + 64 > 65535) by omega, hs,
      show 64 ≤ p₃.size + 64 by omega, ite_false, ite_true, bind, Except.bind, pure,
      Except.pure, hx₁, decryptAndHash_encryptAndHash hes₃, readKey_packBytes, hag₃,
      hx₂, decryptAndHash_encryptAndHash hep₃]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, hw₁, hr₁, hw₂, hr₂, hw₃, hr₃, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The chaining key of each message

For each message of XX, the theorems below name the X25519 outputs that the chaining key mixes.

They give the local key of each token, and the field of the state that holds its remote key.

A token that used another local key or remote field would make the theorem of its message false.
-/

/-- Mixing a key sets the chaining key to the first HKDF output of the chaining key and that key. -/
private theorem chainingKey_mixKey (s : SymmetricState) (input : Key) :
    (mixKey s input).chainingKey = ⟨(hkdf2 s.chainingKey (packBytes input)).1⟩ := rfl

/-- Encrypting and hashing keeps the chaining key. -/
private theorem chainingKey_of_encryptAndHash {s next : SymmetricState} {p c : ByteArray}
    (h : encryptAndHash s p = .ok (next, c)) : next.chainingKey = s.chainingKey := by
  unfold encryptAndHash at h
  cases hc : encryptWithAd s.cipher (packBytes s.hash.bytes) p with
  | error e => simp [hc, bind, Except.bind] at h
  | ok r =>
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl

/-- Decrypting and hashing keeps the chaining key. -/
private theorem chainingKey_of_decryptAndHash {s next : SymmetricState} {c p : ByteArray}
    (h : decryptAndHash s c = .ok (next, p)) : next.chainingKey = s.chainingKey := by
  unfold decryptAndHash at h
  cases hc : decryptWithAd s.cipher (packBytes s.hash.bytes) c with
  | error e => simp [hc, bind, Except.bind] at h
  | ok r =>
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl

/-- Writing message 1 keeps the chaining key, since its one token `e` mixes only into the hash. -/
theorem chainingKey_writeMessage_of_step_eq_zero {s next : HandshakeState}
    {payload message : ByteArray} (h : writeMessage s payload = .ok (next, message))
    (hs : s.step = 0) : next.symmetric.chainingKey = s.symmetric.chainingKey := by
  dsimp only [writeMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  rename_i w hw
  cases h
  rw [chainingKey_of_encryptAndHash hw]
  split at hv
  · split at hv
    · cases hv
    · cases hv
      rfl
  all_goals first | omega | cases hv

/-- Reading message 1 keeps the chaining key, since its one token `e` mixes only into the hash. -/
theorem chainingKey_readMessage_of_step_eq_zero {s next : HandshakeState}
    {message payload : ByteArray} (h : readMessage s message = .ok (next, payload))
    (hs : s.step = 0) : next.symmetric.chainingKey = s.symmetric.chainingKey := by
  dsimp only [readMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  rename_i w hw
  cases h
  rw [chainingKey_of_decryptAndHash hw]
  split at hv
  · split at hv
    · cases hv
      rfl
    · cases hv
  all_goals first | omega | cases hv

/-- Writing message 2 mixes `ee`, then `es`, into the chaining key, Noise §§5.3, 7.5.

The responder computes `ee` from its ephemeral key and `es` from its static key.

Both take the remote ephemeral key, which the state must hold. -/
theorem chainingKey_writeMessage_of_step_eq_one {s next : HandshakeState}
    {payload message : ByteArray} (h : writeMessage s payload = .ok (next, message))
    (hs : s.step = 1) :
    ∃ re, s.remoteEphemeral = some re ∧ next.symmetric.chainingKey =
      ⟨(hkdf2 ⟨(hkdf2 s.symmetric.chainingKey (packBytes (X25519.x25519 s.ephemeralKey re))).1⟩
        (packBytes (X25519.x25519 s.staticKey re))).1⟩ := by
  dsimp only [writeMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  rename_i w hw
  cases h
  rw [chainingKey_of_encryptAndHash hw]
  split at hv
  · omega
  · split at hv
    · cases hv
    cases hr : s.remoteEphemeral with
    | none => simp [hr, requireKey] at hv
    | some re =>
      simp only [hr, requireKey] at hv
      split at hv
      · cases hv
      rename_i u hu
      cases hv
      refine ⟨re, rfl, ?_⟩
      rw [chainingKey_mixKey, chainingKey_of_encryptAndHash hu, chainingKey_mixKey]
      rfl
  all_goals first | omega | cases hv

/-- Reading message 2 mixes `ee`, then `es`, into the chaining key, Noise §§5.3, 7.5.

The initiator computes both from its ephemeral key.

`ee` takes the remote ephemeral key and `es` the remote static key.

The new state stores both. -/
theorem chainingKey_readMessage_of_step_eq_one {s next : HandshakeState}
    {message payload : ByteArray} (h : readMessage s message = .ok (next, payload))
    (hs : s.step = 1) :
    ∃ re rs, next.remoteEphemeral = some re ∧ next.remoteStatic = some rs ∧
      next.symmetric.chainingKey =
        ⟨(hkdf2 ⟨(hkdf2 s.symmetric.chainingKey (packBytes (X25519.x25519 s.ephemeralKey re))).1⟩
          (packBytes (X25519.x25519 s.ephemeralKey rs))).1⟩ := by
  dsimp only [readMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  rename_i w hw
  cases h
  rw [chainingKey_of_decryptAndHash hw]
  split at hv
  · omega
  · split at hv
    · split at hv
      · cases hv
      rename_i u hu
      split at hv
      · cases hv
      cases hv
      refine ⟨_, _, rfl, rfl, ?_⟩
      rw [chainingKey_mixKey, chainingKey_of_decryptAndHash hu, chainingKey_mixKey]
      rfl
    · cases hv
  all_goals first | omega | cases hv

/-- Writing message 3 mixes `se` into the chaining key, Noise §§5.3, 7.5.

The initiator computes it from its static key and the remote ephemeral key that the state holds. -/
theorem chainingKey_writeMessage_of_step_eq_two {s next : HandshakeState}
    {payload message : ByteArray} (h : writeMessage s payload = .ok (next, message))
    (hs : s.step = 2) :
    ∃ re, s.remoteEphemeral = some re ∧ next.symmetric.chainingKey =
      ⟨(hkdf2 s.symmetric.chainingKey (packBytes (X25519.x25519 s.staticKey re))).1⟩ := by
  dsimp only [writeMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  rename_i w hw
  cases h
  rw [chainingKey_of_encryptAndHash hw]
  split at hv
  · omega
  · omega
  · split at hv
    · cases hv
    cases hr : s.remoteEphemeral with
    | none => simp [hr, requireKey] at hv
    | some re =>
      simp only [hr, requireKey] at hv
      split at hv
      · cases hv
      rename_i u hu
      cases hv
      refine ⟨re, rfl, ?_⟩
      rw [chainingKey_mixKey, chainingKey_of_encryptAndHash hu]
  · cases hv

/-- Reading message 3 mixes `se` into the chaining key, Noise §§5.3, 7.5.

The responder computes it from its ephemeral key and the remote static key, which it then stores.

The stored remote ephemeral key stays as it was. -/
theorem chainingKey_readMessage_of_step_eq_two {s next : HandshakeState}
    {message payload : ByteArray} (h : readMessage s message = .ok (next, payload))
    (hs : s.step = 2) :
    next.remoteEphemeral = s.remoteEphemeral ∧ ∃ rs, next.remoteStatic = some rs ∧
      next.symmetric.chainingKey =
        ⟨(hkdf2 s.symmetric.chainingKey (packBytes (X25519.x25519 s.ephemeralKey rs))).1⟩ := by
  dsimp only [readMessage, Bind.bind, Pure.pure, Except.bind, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i v hv
  split at h
  · cases h
  rename_i w hw
  cases h
  rw [chainingKey_of_decryptAndHash hw]
  split at hv
  · omega
  · omega
  · split at hv
    · split at hv
      · cases hv
      rename_i u hu
      split at hv
      · cases hv
      cases hv
      refine ⟨rfl, _, rfl, ?_⟩
      rw [chainingKey_mixKey, chainingKey_of_decryptAndHash hu]
    · cases hv
  · cases hv

/-- After message 3, the initiator's chaining key has mixed `ee`, `es` and `se`, in that order.

The first chaining key is the one that the protocol name sets, Noise §5.2.

`ee` and `es` pair the ephemeral key of the initiator with the remote ephemeral and static keys.

`se` pairs the static key of the initiator with the remote ephemeral key.

These remote keys are the ones that the final state stores. -/
theorem chainingKey_writeMessage_readMessage_writeMessage {si ei : Key}
    {prologue p₁ p₂ p₃ m₁ m₂ m₃ : ByteArray} {i₁ i₂ i₃ : HandshakeState}
    (h₁ : writeMessage (initializeHandshake true si ei prologue) p₁ = .ok (i₁, m₁))
    (h₂ : readMessage i₁ m₂ = .ok (i₂, p₂)) (h₃ : writeMessage i₂ p₃ = .ok (i₃, m₃)) :
    ∃ re rs, i₃.remoteEphemeral = some re ∧ i₃.remoteStatic = some rs ∧
      i₃.symmetric.chainingKey =
        ⟨(hkdf2 ⟨(hkdf2 ⟨(hkdf2 initializeSymmetric.chainingKey
          (packBytes (X25519.x25519 ei re))).1⟩ (packBytes (X25519.x25519 ei rs))).1⟩
          (packBytes (X25519.x25519 si re))).1⟩ := by
  have c₁ := chainingKey_writeMessage_of_step_eq_zero h₁ rfl
  have k₁ := keys_of_writeMessage h₁
  have s₁ := (writeMessage_ok h₁).2.1
  obtain ⟨re, rs, hre, hrs, c₂⟩ := chainingKey_readMessage_of_step_eq_one h₂ s₁
  have k₂ := keys_of_readMessage h₂
  have s₂ := (readMessage_ok h₂).2.1
  obtain ⟨re', hre', c₃⟩ := chainingKey_writeMessage_of_step_eq_two h₃ (by rw [s₂, s₁]; rfl)
  rw [hre] at hre'
  cases hre'
  refine ⟨re, rs, by rw [(keys_of_writeMessage h₃).2.2, hre],
    by rw [(writeMessage_ok h₃).2.2.1, hrs], ?_⟩
  rw [c₃, c₂, c₁, k₂.1, k₁.1, k₁.2.1]
  rfl

/-- After message 3, the responder's chaining key has mixed `ee`, `es` and `se`, in that order.

The first chaining key is the one that the protocol name sets, Noise §5.2.

`ee` and `es` pair the ephemeral and static keys of the responder with the remote ephemeral key.

`se` pairs the ephemeral key of the responder with the remote static key.

These remote keys are the ones that the final state stores. -/
theorem chainingKey_readMessage_writeMessage_readMessage {sr er : Key}
    {prologue p₁ p₂ p₃ m₁ m₂ m₃ : ByteArray} {r₁ r₂ r₃ : HandshakeState}
    (h₁ : readMessage (initializeHandshake false sr er prologue) m₁ = .ok (r₁, p₁))
    (h₂ : writeMessage r₁ p₂ = .ok (r₂, m₂)) (h₃ : readMessage r₂ m₃ = .ok (r₃, p₃)) :
    ∃ re rs, r₃.remoteEphemeral = some re ∧ r₃.remoteStatic = some rs ∧
      r₃.symmetric.chainingKey =
        ⟨(hkdf2 ⟨(hkdf2 ⟨(hkdf2 initializeSymmetric.chainingKey
          (packBytes (X25519.x25519 er re))).1⟩ (packBytes (X25519.x25519 sr re))).1⟩
          (packBytes (X25519.x25519 er rs))).1⟩ := by
  have c₁ := chainingKey_readMessage_of_step_eq_zero h₁ rfl
  have k₁ := keys_of_readMessage h₁
  have s₁ := (readMessage_ok h₁).2.1
  obtain ⟨re, hre, c₂⟩ := chainingKey_writeMessage_of_step_eq_one h₂ s₁
  have k₂ := keys_of_writeMessage h₂
  have s₂ := (writeMessage_ok h₂).2.1
  obtain ⟨he₃, rs, hrs, c₃⟩ := chainingKey_readMessage_of_step_eq_two h₃ (by rw [s₂, s₁]; rfl)
  refine ⟨re, rs, by rw [he₃, k₂.2.2, hre], hrs, ?_⟩
  rw [c₃, c₂, c₁, k₂.2.1, k₁.1, k₁.2]
  rfl

end EthLib.Networking.Noise
