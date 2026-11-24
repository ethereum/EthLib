module

public import EthLib.Cryptography.ChaCha20Poly1305
public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.Word32

/-!
# Proofs: the ChaCha20-Poly1305 boundaries, round trip and bytes

Counter exhaustion is rejected, output length is preserved, and a wrong tag reveals no plaintext.

The cipher undoes itself, as [RFC 8439 §2.4][rfc] says: decryption is done in the same way.

So decryption of an honest ciphertext and tag returns the plaintext, and no other tag passes.

Each byte of the cipher's output and of the AEAD ciphertext is given by its block and counter.

The tag, the padding of the MAC input and the serialization of the state are stated too.

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
    crypt key counter nonce input = .error (.counterExhausted counter.toNat input.size) := by
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

A bit below 128 that the clamp keeps is the bit of the key's low half. -/
theorem testBit_clampR (key : Key) (i : Nat) :
    (clampR key).testBit i
      = ((Base.ByteOrder.ofLE (Vector.ofFn fun j : Fin 16 => key[j.val]'(by omega))).testBit i
          -- No bit from 128 up is set.
          --
          -- The clamp clears bits 28 to 31 of every word.
          --
          -- They are the top four bits of bytes 3, 7, 11 and 15.
          && (decide (i < 128) && decide (i % 32 < 28)
            -- It clears bits 0 and 1 of every word but the first.
            --
            -- They are the bottom two bits of bytes 4, 8 and 12.
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

/-! ## The state as bytes

RFC 8439 §2.3 serializes the sixteen words of the state little-endian, word 0 first.

Byte `i` is byte `i % 4` of word `i / 4`, its least significant byte first.

Reading 64 bytes as a state undoes that serialization, in both directions.
-/

/-- Byte `i` of the serialized state is byte `i % 4` of word `i / 4`, RFC 8439 §2.3.

So the least significant byte of each word comes first, and a big-endian serialization fails it. -/
theorem getElem_serializeState (words : State) (i : Nat) (h : i < 64) :
    (serializeState words)[i]
      = UInt8.ofNat ((words[i / 4]'(by omega)).toNat / 256 ^ (i % 4)) := by
  simp only [serializeState, Vector.getElem_ofFn, Base.uint32Byte]
  apply UInt8.toNat.inj
  have h8 : (8 * (i % 4)) % 32 = 8 * (i % 4) := Nat.mod_eq_of_lt (by omega)
  simp [UInt32.toNat_shiftRight, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    UInt32.toNat_ofNat', h8, Nat.pow_mul]

/-- Reading the serialized state gives back the state. -/
theorem stateOfBytes_serializeState (words : State) :
    stateOfBytes (serializeState words) = words := by
  ext j hj
  simp only [stateOfBytes, serializeState, Vector.getElem_ofFn]
  have h0 : (4 * j) / 4 = j := by omega
  have h1 : (4 * j + 1) / 4 = j := by omega
  have h2 : (4 * j + 2) / 4 = j := by omega
  have h3 : (4 * j + 3) / 4 = j := by omega
  simp only [h0, h1, h2, h3, Nat.mul_mod_right, Nat.mul_add_mod_self_left]
  exact Base.uint32OfBytes_uint32Byte _

/-- Serializing a state read from 64 bytes gives back the bytes.

So the read is the inverse of the serialization, and it reads each word little-endian too. -/
theorem serializeState_stateOfBytes (bytes : Vector UInt8 64) :
    serializeState (stateOfBytes bytes) = bytes := by
  ext i hi
  simp only [stateOfBytes, serializeState, Vector.getElem_ofFn]
  obtain ⟨e0, e1, e2, e3⟩ := Base.uint32Byte_uint32OfBytes bytes[4 * (i / 4)]
    bytes[4 * (i / 4) + 1] bytes[4 * (i / 4) + 2] bytes[4 * (i / 4) + 3]
  -- Byte `i` is byte `i % 4` of the word read from bytes `4 * (i / 4)` to `4 * (i / 4) + 3`.
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h
  · rw [h, e0]
    congr 1
    omega
  · rw [h, e1]
    congr 1
    omega
  · rw [h, e2]
    congr 1
    omega
  · rw [h, e3]
    congr 1
    omega

/-! ## The keystream and the cipher

One theorem gives every byte of the cipher's output by its block and counter.

Another gives every byte of the AEAD's output.
-/

/-- One more block appends the block whose counter is the initial counter plus their number. -/
private theorem keyStream_succ (key : Key) (counter : UInt32) (nonce : Nonce) (blocks : Nat) :
    keyStream key counter nonce (blocks + 1)
      = keyStream key counter nonce blocks
        ++ Base.packBytes (block key (counter + UInt32.ofNat blocks) nonce) := by
  simp only [keyStream, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The keystream has 64 bytes for each block. -/
theorem size_keyStream (key : Key) (counter : UInt32) (nonce : Nonce) (blocks : Nat) :
    (keyStream key counter nonce blocks).size = 64 * blocks := by
  induction blocks with
  | zero => rfl
  | succ n ih =>
    rw [keyStream_succ, ByteArray.size_append, ih, Base.size_packBytes]
    omega

/-- Byte `j` of the keystream is byte `j % 64` of the block at counter plus `j / 64`, RFC 8439 §2.4.

Every byte past the requested blocks reads as zero. -/
theorem byteAtOrZero_keyStream (key : Key) (counter : UInt32) (nonce : Nonce) (blocks j : Nat) :
    Base.byteAtOrZero (keyStream key counter nonce blocks) j
      = if j < 64 * blocks then
          -- RFC 8439 §2.4 encrypts byte `j` of the input with byte `j % 64` of this block.
          --
          -- Its counter is the initial one plus `j / 64`, so each input block has its own counter.
          (block key (counter + UInt32.ofNat (j / 64)) nonce)[j % 64]'(Nat.mod_lt _ (by decide))
        else 0 := by
  induction blocks with
  | zero => simp [keyStream, Base.byteAtOrZero_of_size_le]
  | succ n ih =>
    rw [keyStream_succ, Base.byteAtOrZero_append, size_keyStream, ih]
    by_cases hj : j < 64 * n
    · simp [hj, show j < 64 * (n + 1) by omega]
    · rcases (by omega : j / 64 = n ∨ 64 * (n + 1) ≤ j) with hq | hq
      · -- Byte `j` falls in the appended block, at offset `j % 64`.
        have hlt : j < 64 * (n + 1) := by omega
        have hm : j - 64 * n = j % 64 := by omega
        simp [hj, hlt, hq, Base.byteAtOrZero, hm, Base.packBytes, ByteArray.getElem_eq_getElem_data]
        exact dite_eq_left (by simp [ByteArray.size]; omega)
      · simp [hj, show ¬j < 64 * (n + 1) by omega]
        exact Base.byteAtOrZero_of_size_le (by simp; omega)

/-- The cipher accepts exactly when the counter does not wrap.

Its output then has the length of the input, and each byte is XORed with its keystream byte.

So a cipher that leaves a byte unencrypted, or reuses a counter, fails it. -/
theorem crypt_eq_ok_iff (key : Key) (counter : UInt32) (nonce : Nonce)
    (input output : ByteArray) :
    crypt key counter nonce input = .ok output ↔
      -- RFC 8439 §2.3 makes the block counter 32 bits, and §2.4 adds `j / 64` to it at byte `j`.
      counter.toNat + (input.size + 63) / 64 ≤ 2 ^ 32 ∧ output.size = input.size ∧
        -- Byte `j` of the output is byte `j` of the input XOR a byte of the keystream.
        --
        -- That byte is byte `j % 64` of block `counter + j / 64`.
        --
        -- A keystream shorter than the input would leave the bytes past its end in plaintext.
        ∀ j < input.size, Base.byteAtOrZero output j = Base.byteAtOrZero input j ^^^
        (block key (counter + UInt32.ofNat (j / 64)) nonce)[j % 64]'(Nat.mod_lt _ (by decide)) := by
  -- The keystream covers every byte of the input.
  have hks : ∀ j < input.size,
      Base.byteAtOrZero (keyStream key counter nonce ((input.size + 63) / 64)) j
        = (block key (counter + UInt32.ofNat (j / 64)) nonce)[j % 64]'(Nat.mod_lt _ (by decide)) :=
    fun j hj => by rw [byteAtOrZero_keyStream, ite_eq_left (by omega)]
  unfold crypt
  constructor
  · intro h
    split at h
    · contradiction
    · cases h
      refine ⟨by omega, Base.xorByteArray_size _ _, fun j hj => ?_⟩
      rw [Base.byteAtOrZero_xorByteArray, ite_eq_left hj, hks j hj]
  · rintro ⟨hc, hs, hb⟩
    rw [ite_eq_right (by omega)]
    congr 1
    apply Base.eq_of_byteAtOrZero (by rw [Base.xorByteArray_size, hs])
    intro j
    rw [Base.byteAtOrZero_xorByteArray]
    by_cases hj : j < input.size
    · rw [ite_eq_left hj, hb j hj, hks j hj]
    · rw [ite_eq_right hj, Base.byteAtOrZero_of_size_le (by omega)]

/-- The AEAD accepts exactly when the AAD length fits in 64 bits and the counter does not wrap.

These are the limits of RFC 8439 §2.8.

Its ciphertext then has the length of the plaintext, XOR the keystream from block 1.

Its tag is the Poly1305 tag of the padded AAD, ciphertext and lengths, RFC 8439 §2.8. -/
theorem encrypt_eq_ok_iff (key : Key) (nonce : Nonce) (aad plaintext ciphertext : ByteArray)
    (tag : Tag) :
    encrypt key nonce aad plaintext = .ok (ciphertext, tag) ↔
      -- The AAD is below `2 ^ 64` bytes, and the plaintext at most `2 ^ 32 - 1` blocks of 64 bytes.
      aad.size < 2 ^ 64 ∧ plaintext.size ≤ (2 ^ 32 - 1) * 64 ∧
        -- The ciphertext then has the length of the plaintext.
        ciphertext.size = plaintext.size ∧
        -- Byte `j` of the ciphertext is byte `j` of the plaintext XOR a byte of the keystream.
        --
        -- That byte is byte `j % 64` of block `1 + j / 64`.
        (∀ j < plaintext.size, Base.byteAtOrZero ciphertext j = Base.byteAtOrZero plaintext j ^^^
          -- RFC 8439 §2.8 starts the counter at 1, since §2.6 makes the Poly1305 key from block 0.
          (block key (1 + UInt32.ofNat (j / 64)) nonce)[j % 64]'(Nat.mod_lt _ (by decide))) ∧
        -- The tag is the Poly1305 tag of the padded AAD, ciphertext and lengths, RFC 8439 §2.8.
        --
        -- The Poly1305 key is the first 32 bytes of block 0, RFC 8439 §2.6.
        tag = poly1305 (Vector.ofFn fun i : Fin 32 => (block key 0 nonce)[i.val]'(by omega))
          (aad ++ pad16 aad ++ ciphertext ++ pad16 ciphertext ++
            -- The lengths are 8 bytes each, least significant first.
            Base.packBytes (Base.ByteOrder.toLE 8 aad.size) ++
            Base.packBytes (Base.ByteOrder.toLE 8 ciphertext.size)) := by
  unfold encrypt checkLengths
  by_cases ha : aad.size ≥ 2 ^ 64
  · simp only [ha, ite_true, bind, Except.bind, reduceCtorEq, false_iff]
    omega
  by_cases hp : plaintext.size > (2 ^ 32 - 1) * 64
  · simp only [ha, hp, ite_true, ite_false, bind, Except.bind, reduceCtorEq, false_iff]
    omega
  simp only [ha, hp, ite_false, bind, Except.bind]
  cases hc : crypt key 1 nonce plaintext with
  | error e =>
    -- A plaintext of at most `2 ^ 32 - 1` blocks leaves room for them after counter 1.
    simp only [crypt] at hc
    rw [ite_eq_right (by simp; omega)] at hc
    contradiction
  | ok c =>
    obtain ⟨_, hs, hb⟩ := (crypt_eq_ok_iff key 1 nonce plaintext c).mp hc
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      subst h1
      exact ⟨by omega, by omega, hs, hb, h2.symm⟩
    · rintro ⟨-, -, hs', hb', rfl⟩
      -- Two strings of the plaintext's length that agree on every byte are one string.
      have heq : c = ciphertext := by
        apply Base.eq_of_byteAtOrZero (by rw [hs, hs'])
        intro j
        by_cases hj : j < plaintext.size
        · rw [hb j hj, hb' j hj]
        · rw [Base.byteAtOrZero_of_size_le (by omega), Base.byteAtOrZero_of_size_le (by omega)]
      subst heq
      exact ⟨rfl, rfl⟩

/-! ## The padding of the MAC input -/

/-- The padding is `n` zero bytes exactly when `n` is below 16 and completes a multiple of 16.

So it is the fewest zero bytes that align the input, RFC 8439 §2.8.1, and none for aligned input. -/
theorem pad16_eq_iff (bytes : ByteArray) (n : Nat) :
    pad16 bytes = ⟨Array.replicate n 0⟩ ↔ n < 16 ∧ (bytes.size + n) % 16 = 0 := by
  constructor
  · intro h
    have := congrArg (fun b : ByteArray => b.data.size) h
    simp only [pad16, Array.size_replicate] at this
    omega
  · rintro ⟨h1, h2⟩
    have : (16 - bytes.size % 16) % 16 = n := by omega
    simp [pad16, this]

end EthLib.Cryptography.ChaCha20Poly1305
