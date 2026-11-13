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

end EthLib.Networking.Noise
