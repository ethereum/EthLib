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

One theorem gives every bit of `r`.

It is the key's own bit where the mask keeps it, and clear where the mask does not.

So a clamp that cleared another bit, or kept one it should clear, would fail it.

The bits the mask clears and the bounds that follow are corollaries of that one theorem.

So `r` stays below the prime of the field, and the accumulator never reduces it.
-/

/-- Every bit of `r` is the key's bit where the mask keeps it, and clear where it does not.

This gives the clamp of RFC 8439 §2.5 in full: the facts below are corollaries of it. -/
theorem testBit_clampR (key : Key) (i : Nat) :
    (clampR key).testBit i
      = ((Base.bytesToUint (Vector.ofFn fun j : Fin 16 => key[j.val]'(by omega))).testBit i
          && (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i) := by
  simp [clampR, Nat.testBit_and]

/-- A bit that the mask clears is clear in `r`. -/
private theorem testBit_clampR_of_mask_false {i : Nat}
    (h : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i = false) (key : Key) :
    (clampR key).testBit i = false := by
  rw [testBit_clampR, h, Bool.and_false]

/-- A bit that the mask keeps is the key's own bit, so the clamp clears nothing else. -/
theorem testBit_clampR_of_mask_true {i : Nat}
    (h : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i = true) (key : Key) :
    (clampR key).testBit i
      = (Base.bytesToUint (Vector.ofFn fun j : Fin 16 => key[j.val]'(by omega))).testBit i := by
  rw [testBit_clampR, h, Bool.and_true]

/-- The mask clears the four high bits of each of its four words. -/
private theorem testBit_mask_high : ∀ w < 4, ∀ i < 32, 28 ≤ i →
    (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit (32 * w + i) = false := by decide

/-- The mask clears the two low bits of each of its words but the first. -/
private theorem testBit_mask_low : ∀ w < 4, 0 < w → ∀ i < 2,
    (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit (32 * w + i) = false := by decide

/-- The clamp clears the four high bits of every word of `r`, RFC 8439 §2.5. -/
theorem testBit_clampR_high (key : Key) {w i : Nat} (hw : w < 4) (hi : i < 32) (h : 28 ≤ i) :
    (clampR key).testBit (32 * w + i) = false :=
  testBit_clampR_of_mask_false (testBit_mask_high w hw i hi h) key

/-- The clamp clears the two low bits of every word of `r` but the first, RFC 8439 §2.5. -/
theorem testBit_clampR_low (key : Key) {w i : Nat} (hw : w < 4) (hw0 : 0 < w) (hi : i < 2) :
    (clampR key).testBit (32 * w + i) = false :=
  testBit_clampR_of_mask_false (testBit_mask_low w hw hw0 i hi) key

/-- The clamp keeps no bit that its mask clears. -/
private theorem clampR_le (key : Key) :
    clampR key ≤ 0x0ffffffc0ffffffc0ffffffc0fffffff := Nat.and_le_right

/-- The clamp keeps `r` below `2 ^ 124`, RFC 8439 §2.5. -/
theorem clampR_lt (key : Key) : clampR key < 2 ^ 124 :=
  Nat.lt_of_le_of_lt (clampR_le key) (by decide)

/-- The clamp keeps `r` below the prime `2 ^ 130 - 5`, so the accumulator never reduces it. -/
theorem clampR_lt_prime (key : Key) : clampR key < 2 ^ 130 - 5 :=
  Nat.lt_of_le_of_lt (clampR_le key) (by decide)

/-- A fold whose every step lands below a bound stays below it. -/
private theorem foldl_lt_of_step {α : Type} {p : Nat} {g : Nat → α → Nat}
    (hg : ∀ acc a, g acc a < p) : ∀ (l : List α) (acc : Nat), acc < p → l.foldl g acc < p := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons a t ih => intro acc _; exact ih _ (hg acc a)

/-- The accumulator stays below the prime, whatever `r` and the message, RFC 8439 §2.5. -/
theorem poly1305Accumulator_lt (r : Nat) (message : ByteArray) :
    poly1305Accumulator r message < 2 ^ 130 - 5 := by
  have hp : 0 < 2 ^ 130 - 5 := by decide
  exact foldl_lt_of_step (fun _ _ => Nat.mod_lt _ hp) _ 0 hp

end EthLib.Cryptography.ChaCha20Poly1305
