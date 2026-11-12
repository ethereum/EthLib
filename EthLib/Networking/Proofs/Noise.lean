module

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

Noise §5.2 starts the chaining key and the transcript hash at the padded protocol name.

The two start equal, whichever of the two forms of §5.2 the name takes.

Each mix has one theorem for the whole state it returns.

A mix that moved bytes between the three fields would fail it.

A run of transcript mixes leaves the chaining key and the cipher, however long the run.

Two transcripts that end alike agree on the last bytes mixed, or SHA-256 repeats itself.
-/

/-- The whole state the handshake starts from, Noise §5.2.

The chaining key and the transcript start equal, and the cipher starts with no key. -/
theorem initializeSymmetric_eq :
    initializeSymmetric
      = ⟨⟨initializeSymmetric.hash.bytes⟩, initializeSymmetric.hash, initializeKey none⟩ := rfl

/-- The whole state a mix of bytes returns, Noise §5.2.

Only the transcript changes, and it becomes the hash of the old one with those bytes. -/
theorem mixHash_eq (s : SymmetricState) (bytes : ByteArray) :
    mixHash s bytes
      = ⟨s.chainingKey, ⟨Hash.Sha256.hash32 (packBytes s.hash.bytes ++ bytes)⟩, s.cipher⟩ := rfl

/-- The whole state a mix of a key returns, Noise §§4.3 and 5.2.

The transcript stays, and the chaining key takes the first output of the derivation.

The cipher takes the second output, with a fresh nonce. -/
theorem mixKey_eq (s : SymmetricState) (input : Key) :
    mixKey s input
      = ⟨⟨(hkdf2 s.chainingKey (packBytes input)).1⟩, s.hash,
          initializeKey (some (hkdf2 s.chainingKey (packBytes input)).2)⟩ := rfl

/-- A mix of a key resets the nonce, so its key is never used at a spent nonce, Noise §5.2. -/
theorem nonce_mixKey (s : SymmetricState) (input : Key) : (mixKey s input).cipher.nonce = 0 := by
  rw [mixKey_eq]
  rfl

/-! ## A run of mixes

The chaining key carries the key material, so no run of transcript mixes may reach it.
-/

/-- A run of transcript mixes leaves the chaining key, however long the run. -/
theorem chainingKey_foldl_mixHash (s : SymmetricState) (l : List ByteArray) :
    (l.foldl mixHash s).chainingKey = s.chainingKey := by
  induction l generalizing s with
  | nil => rfl
  | cons b t ih => rw [List.foldl_cons, ih, mixHash_eq]

/-- A run of transcript mixes leaves the cipher, so it reaches no key and no nonce. -/
theorem cipher_foldl_mixHash (s : SymmetricState) (l : List ByteArray) :
    (l.foldl mixHash s).cipher = s.cipher := by
  induction l generalizing s with
  | nil => rfl
  | cons b t ih => rw [List.foldl_cons, ih, mixHash_eq]

/-- Two transcripts that end alike agree on the bytes last mixed, or SHA-256 repeats itself.

So a transcript separates two handshakes unless their mixed bytes collide under SHA-256. -/
theorem hash_mixHash_inj {s t : SymmetricState} {a b : ByteArray}
    (h : (mixHash s a).hash = (mixHash t b).hash) :
    Hash.Sha256.hash32 (packBytes s.hash.bytes ++ a)
      = Hash.Sha256.hash32 (packBytes t.hash.bytes ++ b) := by
  rw [mixHash_eq, mixHash_eq] at h
  exact congrArg HandshakeHash.bytes h

/-! ## The frame of a transport message -/

/-- Fewer than two bytes carry no length, Noise §3 framing. -/
theorem unframe_eq_error_of_size_lt {bytes : ByteArray} (h : bytes.size < 2) :
    unframe bytes = .error .truncated := by
  simp [unframe, Nat.not_le.mpr h, throw, throwThe, MonadExceptOf.throw]

/-- A frame whose declared length is not its own refuses it, Noise §3 framing. -/
theorem unframe_eq_error_of_length_ne {bytes : ByteArray} (h : 2 ≤ bytes.size)
    (hne : bytesToNat (readBytes bytes 0 2 h).toList + 2 ≠ bytes.size) :
    unframe bytes = .error .frameLength := by
  simp [unframe, h, hne, throw, throwThe, MonadExceptOf.throw]

/-- An accepted frame carries the length that its two leading bytes declare. -/
theorem size_of_unframe_eq_ok {bytes body : ByteArray} (h : unframe bytes = .ok body) :
    body.size + 2 = bytes.size := by
  unfold unframe at h
  split at h
  · rename_i hs
    by_cases hsize : bytesToNat (readBytes bytes 0 2 hs).toList + 2 = bytes.size
    · simp only [hsize, reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [ByteArray.size_extract]
      omega
    · simp [hsize, throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end EthLib.Networking.Noise
