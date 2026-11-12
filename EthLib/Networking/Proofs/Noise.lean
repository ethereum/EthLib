module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Cryptography.Proofs.Hash.Hkdf
public import EthLib.Networking.Noise
public import EthLib.Cryptography.Proofs.ChaCha20Poly1305

/-!
# Proofs: Noise XX

[Noise revision 34, §4.3](https://noiseprotocol.org/noise_rev34.pdf) computes two outputs from HMAC.

Its note calls this function HKDF of [RFC 5869](https://www.rfc-editor.org/rfc/rfc5869#section-2).

There the chaining key is the salt, and the info is empty.

So the two outputs are the first 64 bytes of that HKDF.

Distinct kinds of handshake error have distinct codes.

Each message keeps the role, advances the step by one, and comes at the step XX gives that role.

The pattern is [Noise revision 34, §7.5](https://noiseprotocol.org/noise_rev34.pdf).

The cipher state is [Noise revision 34, §5.1](https://noiseprotocol.org/noise_rev34.pdf).

A keyed cipher state advances its nonce by one for each message it encrypts or decrypts.

Without a key, both directions return their input and leave the cipher state as it was.

Noise §5.1 reserves the greatest nonce, so both directions refuse it.

From one state, decrypting what encrypting wrote returns the plaintext and the same next state.

Both sides hash the same ciphertext, so their transcripts stay in step.
-/

@[expose] public section

namespace EthLib.Networking.Noise

open EthLib.Base
open EthLib.Cryptography
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

XX writes only message 1 or 3 as initiator, and message 2 as responder, Noise revision 34, §7.5. -/
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

XX reads only message 1 or 3 as responder, and message 2 as initiator, Noise revision 34, §7.5. -/
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

private theorem size_append_tag (c : ByteArray) (t : ChaCha20Poly1305.Tag) :
    (c ++ packBytes t).size = c.size + 16 := by
  rw [ByteArray.size_append, size_packBytes]

private theorem extract_append_tag (c : ByteArray) (t : ChaCha20Poly1305.Tag) :
    (c ++ packBytes t).extract 0 c.size = c :=
  ByteArray.extract_append_eq_left rfl

private theorem readBytes_append_tag (c : ByteArray) (t : ChaCha20Poly1305.Tag)
    (h : c.size + 16 ≤ (c ++ packBytes t).size) :
    readBytes (c ++ packBytes t) c.size 16 h = t := by
  apply Vector.ext
  intro i hi
  simp only [readBytes, Vector.getElem_ofFn, ByteArray.data_append]
  rw [Array.getElem_append_right (by simp)]
  simp [packBytes]

/-! ## The cipher state -/

/-- A key is installed with its nonce at zero. -/
theorem nonce_initializeKey (key : Option ChaCha20Poly1305.Key) :
    (initializeKey key).nonce = 0 := rfl

/-- Under no key, a plaintext within 65535 bytes comes back unchanged, with the same state. -/
theorem encryptWithAd_eq_ok_of_key_eq_none {s : CipherState} {aad plaintext : ByteArray}
    (hk : s.key = none) (hs : ¬plaintext.size > 65535) :
    encryptWithAd s aad plaintext = .ok (s, plaintext) := by
  simp [encryptWithAd, hk, hs, pure, Except.pure]

/-- Under no key, a plaintext above 65535 bytes, the limit of Noise §3, is refused. -/
theorem encryptWithAd_eq_error_of_key_eq_none_of_size {s : CipherState}
    {aad plaintext : ByteArray} (hk : s.key = none) (hs : plaintext.size > 65535) :
    encryptWithAd s aad plaintext = .error .messageTooLong := by
  simp [encryptWithAd, hk, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Under a key, a plaintext whose message with its 16-byte tag exceeds 65535 bytes is refused. -/
theorem encryptWithAd_eq_error_of_size {s : CipherState} {aad plaintext : ByteArray}
    {key : ChaCha20Poly1305.Key} (hk : s.key = some key) (hs : plaintext.size + 16 > 65535) :
    encryptWithAd s aad plaintext = .error .messageTooLong := by
  simp [encryptWithAd, hk, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- The greatest nonce never encrypts, as Noise revision 34, §5.1 reserves it for other use. -/
theorem encryptWithAd_eq_error_of_nonce_max {s : CipherState} {aad plaintext : ByteArray}
    {key : ChaCha20Poly1305.Key} (hk : s.key = some key)
    (hs : ¬plaintext.size + 16 > 65535) (hn : s.nonce = 2 ^ 64 - 1) :
    encryptWithAd s aad plaintext = .error .nonceExhausted := by
  simp [encryptWithAd, hk, hs, hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Under a key, an error of the AEAD cipher becomes the error of encrypting.

For a message within 65535 bytes, the cipher refuses only associated data of 2^64 bytes or more. -/
theorem encryptWithAd_eq_error_of_encrypt {s : CipherState} {aad plaintext : ByteArray}
    {key : ChaCha20Poly1305.Key} {error : ChaCha20Poly1305.ChaCha20Poly1305Error}
    (hk : s.key = some key) (hs : ¬plaintext.size + 16 > 65535) (hn : ¬s.nonce = 2 ^ 64 - 1)
    (he : ChaCha20Poly1305.encrypt key (cipherNonce s.nonce) aad plaintext = .error error) :
    encryptWithAd s aad plaintext = .error (.cipher error) := by
  simp [encryptWithAd, hk, hs, hn, he, Except.mapError, Functor.map, Except.map]

/-- Encrypting appends the tag to the ciphertext, keeps the key and advances the nonce by one. -/
theorem encryptWithAd_eq_ok_of_encrypt {s : CipherState} {aad plaintext ciphertext : ByteArray}
    {key : ChaCha20Poly1305.Key} {tag : ChaCha20Poly1305.Tag} (hk : s.key = some key)
    (hs : ¬plaintext.size + 16 > 65535) (hn : ¬s.nonce = 2 ^ 64 - 1)
    (he : ChaCha20Poly1305.encrypt key (cipherNonce s.nonce) aad plaintext =
      .ok (ciphertext, tag)) :
    encryptWithAd s aad plaintext =
      .ok (⟨some key, s.nonce + 1⟩, ciphertext ++ packBytes tag) := by
  simp [encryptWithAd, hk, hs, hn, he, Except.mapError, Functor.map, Except.map]

/-- A ciphertext above 65535 bytes is refused, with or without a key. -/
theorem decryptWithAd_eq_error_of_size {s : CipherState} {aad ciphertext : ByteArray}
    (hs : ciphertext.size > 65535) :
    decryptWithAd s aad ciphertext = .error .messageTooLong := by
  simp [decryptWithAd, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Under no key, a ciphertext within 65535 bytes comes back unchanged, with the same state. -/
theorem decryptWithAd_eq_ok_of_key_eq_none {s : CipherState} {aad ciphertext : ByteArray}
    (hk : s.key = none) (hs : ¬ciphertext.size > 65535) :
    decryptWithAd s aad ciphertext = .ok (s, ciphertext) := by
  simp [decryptWithAd, hk, hs, pure, Except.pure]

/-- The greatest nonce never decrypts, as Noise revision 34, §5.1 reserves it for other use. -/
theorem decryptWithAd_eq_error_of_nonce_max {s : CipherState} {aad ciphertext : ByteArray}
    {key : ChaCha20Poly1305.Key} (hk : s.key = some key) (hs : ¬ciphertext.size > 65535)
    (hn : s.nonce = 2 ^ 64 - 1) :
    decryptWithAd s aad ciphertext = .error .nonceExhausted := by
  simp [decryptWithAd, hk, hs, hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A message too short to hold a tag is refused as truncated. -/
theorem decryptWithAd_eq_error_of_lt {s : CipherState} {aad ciphertext : ByteArray}
    {key : ChaCha20Poly1305.Key} (hk : s.key = some key) (hs : ¬ciphertext.size > 65535)
    (hn : ¬s.nonce = 2 ^ 64 - 1) (h16 : ciphertext.size < 16) :
    decryptWithAd s aad ciphertext = .error .truncated := by
  simp [decryptWithAd, hk, hs, hn, Nat.not_le.mpr h16, throw, throwThe, MonadExceptOf.throw]

/-- An accepted ciphertext and tag decrypt to the plaintext, and the nonce advances by one. -/
theorem decryptWithAd_eq_ok_of_decrypt {s : CipherState} {aad ciphertext plaintext : ByteArray}
    {key : ChaCha20Poly1305.Key} {tag : ChaCha20Poly1305.Tag} (hk : s.key = some key)
    (hs : ¬(ciphertext ++ packBytes tag).size > 65535) (hn : ¬s.nonce = 2 ^ 64 - 1)
    (hd : ChaCha20Poly1305.decrypt key (cipherNonce s.nonce) aad ciphertext tag = .ok plaintext) :
    decryptWithAd s aad (ciphertext ++ packBytes tag) =
      .ok (⟨some key, s.nonce + 1⟩, plaintext) := by
  have h16 : 16 ≤ (ciphertext ++ packBytes tag).size := by rw [size_append_tag]; omega
  have hcut : (ciphertext ++ packBytes tag).size - 16 = ciphertext.size := by
    rw [size_append_tag]; omega
  simp only [decryptWithAd, hs, ↓reduceIte, hk, hn, h16, hcut, readBytes_append_tag,
    extract_append_tag, hd, Except.mapError, bind, Except.bind,
    pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  simp

/-- A ciphertext and tag that the cipher refuses are refused with its error, Noise §5.1.

The refusal returns no cipher state, so the nonce of the caller does not advance. -/
theorem decryptWithAd_eq_error_of_decrypt {s : CipherState} {aad ciphertext : ByteArray}
    {key : ChaCha20Poly1305.Key} {tag : ChaCha20Poly1305.Tag}
    {error : ChaCha20Poly1305.ChaCha20Poly1305Error} (hk : s.key = some key)
    (hs : ¬(ciphertext ++ packBytes tag).size > 65535) (hn : ¬s.nonce = 2 ^ 64 - 1)
    (hd : ChaCha20Poly1305.decrypt key (cipherNonce s.nonce) aad ciphertext tag = .error error) :
    decryptWithAd s aad (ciphertext ++ packBytes tag) = .error (.cipher error) := by
  have h16 : 16 ≤ (ciphertext ++ packBytes tag).size := by rw [size_append_tag]; omega
  have hcut : (ciphertext ++ packBytes tag).size - 16 = ciphertext.size := by
    rw [size_append_tag]; omega
  simp only [decryptWithAd, hs, ↓reduceIte, hk, hn, h16, hcut, readBytes_append_tag,
    extract_append_tag, hd, Except.mapError, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]
  simp

/-! ## Decrypting undoes encrypting -/

/-- Decrypting undoes encrypting, and reaches the cipher state that encrypting reached. -/
theorem decryptWithAd_encryptWithAd {s next : CipherState} {aad plaintext message : ByteArray}
    (h : encryptWithAd s aad plaintext = .ok (next, message)) :
    decryptWithAd s aad message = .ok (next, plaintext) := by
  cases hk : s.key with
  | none =>
    have hs : ¬plaintext.size > 65535 := by
      intro hc
      rw [encryptWithAd_eq_error_of_key_eq_none_of_size hk hc] at h
      cases h
    rw [encryptWithAd_eq_ok_of_key_eq_none hk hs] at h
    cases h
    exact decryptWithAd_eq_ok_of_key_eq_none hk hs
  | some key =>
    have hs : ¬plaintext.size + 16 > 65535 := by
      intro hc
      rw [encryptWithAd_eq_error_of_size hk hc] at h
      cases h
    have hn : ¬s.nonce = 2 ^ 64 - 1 := by
      intro hc
      rw [encryptWithAd_eq_error_of_nonce_max hk hs hc] at h
      cases h
    cases he : ChaCha20Poly1305.encrypt key (cipherNonce s.nonce) aad plaintext with
    | error e =>
      rw [encryptWithAd_eq_error_of_encrypt hk hs hn he] at h
      cases h
    | ok r =>
      obtain ⟨ciphertext, tag⟩ := r
      rw [encryptWithAd_eq_ok_of_encrypt hk hs hn he] at h
      cases h
      exact decryptWithAd_eq_ok_of_decrypt hk
        (by rw [size_append_tag, ChaCha20Poly1305.encrypt_size _ _ _ _ _ _ he]; omega) hn
        (ChaCha20Poly1305.decrypt_encrypt key (cipherNonce s.nonce) aad plaintext ciphertext tag he)

/-- Decrypting a handshake message undoes encrypting it, and reaches the same symmetric state.

Both sides hash the same ciphertext into the transcript, so their transcripts stay in step. -/
theorem decryptAndHash_encryptAndHash {s next : SymmetricState} {plaintext message : ByteArray}
    (h : encryptAndHash s plaintext = .ok (next, message)) :
    decryptAndHash s message = .ok (next, plaintext) := by
  unfold encryptAndHash at h
  unfold decryptAndHash
  cases hc : encryptWithAd s.cipher (packBytes s.hash.bytes) plaintext with
  | error e => simp [hc, bind, Except.bind] at h
  | ok r =>
    obtain ⟨cipher, ciphertext⟩ := r
    simp only [hc, bind, Except.bind, pure, Except.pure] at h
    cases h
    rw [decryptWithAd_encryptWithAd hc]
    rfl

/-! ## The transcript of the handshake

A run of transcript mixes of Noise §5.2 leaves the chaining key and the cipher, however long.

Two mixes that end at one handshake hash started at one handshake hash and mixed the same bytes.

Otherwise their two inputs to SHA-256 differ and hash alike, so that pair is a collision.
-/

/-- A run of transcript mixes leaves the chaining key, however long the run. -/
theorem chainingKey_foldl_mixHash (s : SymmetricState) (l : List ByteArray) :
    (l.foldl mixHash s).chainingKey = s.chainingKey := by
  induction l generalizing s with
  | nil => rfl
  | cons b t ih => exact ih (mixHash s b)

/-- A run of transcript mixes leaves the cipher, so it changes no key and no nonce. -/
theorem cipher_foldl_mixHash (s : SymmetricState) (l : List ByteArray) :
    (l.foldl mixHash s).cipher = s.cipher := by
  induction l generalizing s with
  | nil => rfl
  | cons b t ih => exact ih (mixHash s b)

/-- Two mixes that end at one handshake hash started at one such hash and mixed the same bytes.

Otherwise the two inputs to SHA-256, each an old hash and the bytes mixed, collide. -/
theorem eq_or_collision_of_hash_mixHash_eq {s t : SymmetricState} {a b : ByteArray}
    (h : (mixHash s a).hash = (mixHash t b).hash) :
    (s.hash = t.hash ∧ a = b) ∨
      (packBytes s.hash.bytes ++ a ≠ packBytes t.hash.bytes ++ b ∧
        Hash.Sha256.hash32 (packBytes s.hash.bytes ++ a)
          = Hash.Sha256.hash32 (packBytes t.hash.bytes ++ b)) := by
  by_cases he : packBytes s.hash.bytes ++ a = packBytes t.hash.bytes ++ b
  · -- Both transcripts are 32 bytes, so equal inputs split into equal parts.
    have hp := ByteArray.append_inj_left he (by simp)
    rw [hp, ByteArray.append_right_inj] at he
    exact .inl ⟨congrArg HandshakeHash.mk (packBytes_injective hp), he⟩
  · exact .inr ⟨he, congrArg HandshakeHash.bytes h⟩

/-! ## The frame of a transport message

The frame is the one of the noise-libp2p "Wire Format": a 16-bit big-endian length, then the body.
-/

/-- Fewer than two bytes hold no length, and are refused as truncated. -/
theorem unframe_eq_error_of_size_lt {bytes : ByteArray} (h : bytes.size < 2) :
    unframe bytes = .error .truncated := by
  simp [unframe, Nat.not_le.mpr h, throw, throwThe, MonadExceptOf.throw]

/-- Bytes whose leading two declare another length for the rest are refused. -/
theorem unframe_eq_error_of_length_ne {bytes : ByteArray} (h : 2 ≤ bytes.size)
    (hne : bytesToNat (readBytes bytes 0 2 h).toList + 2 ≠ bytes.size) :
    unframe bytes = .error .frameLength := by
  simp [unframe, h, hne, throw, throwThe, MonadExceptOf.throw]

/-- Reading back a written frame returns the message it was written from. -/
theorem unframe_frame {message bytes : ByteArray} (h : frame message = .ok bytes) :
    unframe bytes = .ok message := by
  unfold frame at h
  split at h
  · rename_i hm
    cases h
    have hlen := natToBytes_length 2 message.size
    have hs : 2 ≤ (⟨(natToBytes 2 message.size).toArray⟩ ++ message : ByteArray).size := by
      rw [ByteArray.size_append]
      show 2 ≤ (natToBytes 2 message.size).toArray.size + message.size
      simp [hlen]
    have hread : (readBytes (⟨(natToBytes 2 message.size).toArray⟩ ++ message) 0 2 hs).toList
        = natToBytes 2 message.size := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp only [readBytes, Vector.toList_ofFn, List.getElem_ofFn, Nat.zero_add,
          ByteArray.data_append]
        rw [Array.getElem_append_left (by simp [hlen]; simp at h1; omega)]
        simp
    have hval : bytesToNat (natToBytes 2 message.size) = message.size :=
      bytesToNat_natToBytes_of_lt (by omega)
    have hp : (⟨(natToBytes 2 message.size).toArray⟩ : ByteArray).size = 2 := by
      show (natToBytes 2 message.size).toArray.size = 2
      simp [hlen]
    unfold unframe
    rw [dite_eq_left_of_eq_true (eq_true hs)]
    simp only [hread, hval, ByteArray.size_append, hp]
    rw [ite_eq_left (by omega)]
    exact congrArg Except.ok (ByteArray.extract_append_eq_right hp.symm (by rw [hp]))
  · cases h

end EthLib.Networking.Noise
