module

public import EthLib.Cryptography.ChaCha20Poly1305
public import EthLib.Base.Proofs.Bytes

/-!
# Proofs: the ChaCha20-Poly1305 boundaries and round trip

Counter exhaustion is rejected, output length is preserved, and a wrong tag reveals no plaintext.

The cipher undoes itself, as [RFC 8439 §2.4][rfc] says: decryption is done in the same way.

So decryption of an honest ciphertext and tag returns the plaintext, and no other tag passes.

[rfc]: https://www.rfc-editor.org/rfc/rfc8439#section-2.4
-/

public section

namespace EthLib.Cryptography.ChaCha20Poly1305

/-- Encryption and decryption preserve the input length whenever the counter admits it. -/
theorem crypt_size (key : Key) (counter : UInt32) (nonce : Nonce) (input output : ByteArray)
    (h : crypt key counter nonce input = .ok output) : output.size = input.size := by
  unfold crypt at h
  split at h
  · contradiction
  · cases h
    exact EthLib.Base.xorByteArray_size _ _

/-- A stream that would wrap the counter is refused. -/
theorem crypt_eq_error_of_counter_exhausted (key : Key) (counter : UInt32) (nonce : Nonce)
    (input : ByteArray) (h : counter.toNat + (input.size + 63) / 64 > 2 ^ 32) :
    crypt key counter nonce input = .error .counterExhausted := by
  simp only [crypt, h, ↓reduceIte]

/-- A wrong tag is refused before the cipher is run. -/
theorem decrypt_eq_error_of_tag_ne (key : Key) (nonce : Nonce)
    (aad ciphertext : ByteArray) (tag : Tag)
    (hlengths : checkLengths aad.size ciphertext.size = .ok ())
    (htag : poly1305 (poly1305Key key nonce) (macData aad ciphertext) ≠ tag) :
    decrypt key nonce aad ciphertext tag = .error .authenticationFailed := by
  simp only [decrypt, hlengths, ite_eq_right htag]
  rfl

/-- Running the cipher on its own output gives back the input, RFC 8439 §2.4.

The output has the length of the input, so it passes the same counter check. -/
theorem crypt_crypt (key : Key) (counter : UInt32) (nonce : Nonce) (input output : ByteArray)
    (h : crypt key counter nonce input = .ok output) :
    crypt key counter nonce output = .ok input := by
  unfold crypt at h ⊢
  split at h
  · contradiction
  · rename_i hc
    cases h
    rw [EthLib.Base.xorByteArray_size, ite_eq_right hc,
      EthLib.Base.xorByteArray_xorByteArray_cancel_right]

/-- Decryption of an honest ciphertext and tag returns the plaintext, RFC 8439 §2.8. -/
theorem decrypt_encrypt (key : Key) (nonce : Nonce) (aad plaintext ciphertext : ByteArray)
    (tag : Tag) (h : encrypt key nonce aad plaintext = .ok (ciphertext, tag)) :
    decrypt key nonce aad ciphertext tag = .ok plaintext := by
  unfold encrypt at h
  cases hl : checkLengths aad.size plaintext.size with
  | error e => simp [hl, bind, Except.bind] at h
  | ok u =>
    cases hc : crypt key 1 nonce plaintext with
    | error e => simp [hl, hc, bind, Except.bind] at h
    | ok c =>
      simp only [hl, hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- The ciphertext has the length of the plaintext, so it passes the same length checks.
      have hs := crypt_size key 1 nonce plaintext c hc
      unfold decrypt
      rw [hs, hl]
      simp only [bind, Except.bind, ite_true]
      exact crypt_crypt key 1 nonce plaintext c hc

/-- An honest ciphertext decrypts under no tag other than the honest one, RFC 8439 §2.8. -/
theorem tag_eq_of_decrypt_eq_ok (key : Key) (nonce : Nonce)
    (aad plaintext ciphertext out : ByteArray) (tag tag' : Tag)
    (h : encrypt key nonce aad plaintext = .ok (ciphertext, tag))
    (h' : decrypt key nonce aad ciphertext tag' = .ok out) : tag' = tag := by
  unfold encrypt at h
  cases hl : checkLengths aad.size plaintext.size with
  | error e => simp [hl, bind, Except.bind] at h
  | ok u =>
    cases hc : crypt key 1 nonce plaintext with
    | error e => simp [hl, hc, bind, Except.bind] at h
    | ok c =>
      simp only [hl, hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs := crypt_size key 1 nonce plaintext c hc
      -- Decryption returns a plaintext only after its tag comparison succeeds.
      by_cases same : poly1305 (poly1305Key key nonce) (macData aad c) = tag'
      · exact same.symm
      · have hfail := decrypt_eq_error_of_tag_ne key nonce aad c tag' (by rw [hs, hl]) same
        rw [hfail] at h'
        exact absurd h' (by simp)

end EthLib.Cryptography.ChaCha20Poly1305
