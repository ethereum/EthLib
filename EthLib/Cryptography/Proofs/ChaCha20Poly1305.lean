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

/-- Encryption returns a ciphertext of the plaintext's length. -/
theorem encrypt_size (key : Key) (nonce : Nonce) (aad plaintext ciphertext : ByteArray)
    (tag : Tag) (h : encrypt key nonce aad plaintext = .ok (ciphertext, tag)) :
    ciphertext.size = plaintext.size := by
  unfold encrypt at h
  cases hl : checkLengths aad.size plaintext.size with
  | error e => simp [hl, bind, Except.bind] at h
  | ok u =>
    cases hc : crypt key 1 nonce plaintext with
    | error e => simp [hl, hc, bind, Except.bind] at h
    | ok c =>
      simp only [hl, hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]
      exact crypt_size _ _ _ _ _ hc

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

/-! ## The clamp of the Poly1305 key

RFC 8439 §2.5 clears the top four bits of bytes 3, 7, 11 and 15 of `r`.

It also clears the bottom two bits of bytes 4, 8 and 12.

One theorem gives every bit of `r` in those terms, so a clamp with another mask fails it.

So `r` stays below `2 ^ 124`, where a key's low half alone only stays below `2 ^ 128`.
-/

/-- The mask keeps a bit exactly when RFC 8439 §2.5 keeps it. -/
private theorem testBit_clampMask (i : Nat) :
    (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i
      = (decide (i < 128) && decide (i % 32 < 28) && (decide (i < 32) || decide (2 ≤ i % 32))) := by
  by_cases h : i < 128
  · have hall : ∀ j < 128, (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit j
        = (decide (j % 32 < 28) && (decide (j < 32) || decide (2 ≤ j % 32))) := by
      decide
    simp only [h, decide_true, Bool.true_and]
    exact hall i h
  · simp only [h, decide_false, Bool.false_and]
    apply Nat.testBit_lt_two_pow
    calc (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) < 2 ^ 128 := by decide
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)

/-- Every bit of `r`, RFC 8439 §2.5.

Bit `i` is bit `i % 8` of byte `i / 8`, so it is bit `i % 32` of word `i / 32`.

The clamp clears bits 28 to 31 of every word: the top four bits of bytes 3, 7, 11 and 15.

It clears bits 0 and 1 of every word but the first: the bottom two bits of bytes 4, 8 and 12.

Every other bit below 128 is the bit of the key's low half, and no bit from 128 up is set. -/
theorem testBit_clampR (key : Key) (i : Nat) :
    (clampR key).testBit i
      = ((Base.bytesToUint (Vector.ofFn fun j : Fin 16 => key[j.val]'(by omega))).testBit i
          && (decide (i < 128) && decide (i % 32 < 28)
            && (decide (i < 32) || decide (2 ≤ i % 32)))) := by
  rw [← testBit_clampMask]
  simp [clampR, Nat.testBit_and]

/-- The clamp keeps `r` below `2 ^ 124`. -/
theorem clampR_lt (key : Key) : clampR key < 2 ^ 124 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-! ## The accumulator -/

/-- The accumulator stays below the prime `2 ^ 130 - 5`, whatever `r` and the message.

Each step reduces modulo the prime, so this does not depend on the clamp. -/
theorem poly1305Accumulator_lt (r : Nat) (message : ByteArray) :
    poly1305Accumulator r message < 2 ^ 130 - 5 := by
  have hp : 0 < 2 ^ 130 - 5 := by decide
  exact List.foldlRecOn (motive := (· < 2 ^ 130 - 5)) _ _ hp fun _ _ _ _ => Nat.mod_lt _ hp

end EthLib.Cryptography.ChaCha20Poly1305
