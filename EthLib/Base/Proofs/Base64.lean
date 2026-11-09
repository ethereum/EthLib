module

public import EthLib.Base.Base64

/-!
# Proofs: base64 is a bijection between byte strings and accepted texts

The decoder undoes the encoder, so every byte string reads back from its text.

The encoder writes back every text that the decoder accepts, so each byte string has one text.

Both hold group by group, because each six-bit value and its character determine each other.
-/

@[expose] public section

namespace EthLib.Base.Base64

/-- Every six-bit value reads back from its character. -/
theorem decodeSextet_encodeSextet : ∀ v : Fin 64, decodeSextet (encodeSextet v) = some v.val := by
  decide

/-- The character of a value below 64 reads back as that value. -/
theorem readSextet_encodeSextet (v : Nat) (h : v < 64) : readSextet (encodeSextet v) = .ok v := by
  simp only [readSextet, decodeSextet_encodeSextet ⟨v, h⟩]

/-- A byte is the byte of its value. -/
private theorem ofNat_eq (b : UInt8) (n : Nat) (h : n = b.toNat) : UInt8.ofNat n = b := by
  rw [h, UInt8.ofNat_toNat]

/-- The decoder undoes the encoder, three bytes at a time. -/
theorem decodeList_encodeList : (bytes : List UInt8) → decodeList (encodeList bytes) = .ok bytes
  | b0 :: b1 :: b2 :: rest => by
    have h0 := b0.toNat_lt
    have h1 := b1.toNat_lt
    have h2 := b2.toNat_lt
    -- The 24 bits of the group, and its four sextets.
    generalize hn : b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 + b2.toNat = n
    simp only [encodeList, decodeList, hn, readSextet_encodeSextet (n / 2 ^ 18) (by omega),
      readSextet_encodeSextet (n / 2 ^ 12 % 64) (by omega),
      readSextet_encodeSextet (n / 2 ^ 6 % 64) (by omega),
      readSextet_encodeSextet (n % 64) (by omega), decodeList_encodeList rest,
      bind, Except.bind, pure, Except.pure]
    rw [ofNat_eq b0 _ (by omega), ofNat_eq b1 _ (by omega), ofNat_eq b2 _ (by omega)]
  | [b0, b1] => by
    have h0 := b0.toNat_lt
    have h1 := b1.toNat_lt
    -- The 16 bits of the group, then two zero bits.
    generalize hn : b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 = n
    simp only [encodeList, decodeList, hn, readSextet_encodeSextet (n / 2 ^ 18) (by omega),
      readSextet_encodeSextet (n / 2 ^ 12 % 64) (by omega),
      readSextet_encodeSextet (n / 2 ^ 6 % 64) (by omega),
      bind, Except.bind, pure, Except.pure]
    -- The two unused bits are zero.
    rw [ite_eq_left (by omega)]
    rw [ofNat_eq b0 _ (by omega), ofNat_eq b1 _ (by omega)]
  | [b0] => by
    have h0 := b0.toNat_lt
    -- The 8 bits of the byte, then four zero bits.
    generalize hn : b0.toNat * 2 ^ 16 = n
    simp only [encodeList, decodeList, hn, readSextet_encodeSextet (n / 2 ^ 18) (by omega),
      readSextet_encodeSextet (n / 2 ^ 12 % 64) (by omega),
      bind, Except.bind, pure, Except.pure]
    -- The four unused bits are zero.
    rw [ite_eq_left (by omega)]
    rw [ofNat_eq b0 _ (by omega)]
  | [] => rfl

/-- The decoder undoes the encoder: every byte string reads back from its text. -/
theorem decode_encode (bytes : ByteArray) : decode (encode bytes) = .ok bytes := by
  simp only [decode, encode, String.toList_ofList, decodeList_encodeList, bind, Except.bind,
    pure, Except.pure]

/-! ## The decoder accepts only what the encoder writes -/

/-- A character that reads as a value is the character of that value. -/
theorem encodeSextet_of_decodeSextet {c : Char} {v : Nat} (h : decodeSextet c = some v) :
    v < 64 ∧ encodeSextet v = c := by
  unfold decodeSextet at h
  have hc : Char.ofNat c.toNat = c := Char.ofNat_toNat c
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeSextet, show c.toNat - 65 < 26 by omega, ↓reduceIte]
    rw [show 65 + (c.toNat - 65) = c.toNat by omega, hc]
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeSextet, show ¬ c.toNat - 97 + 26 < 26 by omega,
      show c.toNat - 97 + 26 < 52 by omega, ↓reduceIte]
    rw [show 97 + (c.toNat - 97 + 26 - 26) = c.toNat by omega, hc]
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeSextet, show ¬ c.toNat - 48 + 52 < 26 by omega,
      show ¬ c.toNat - 48 + 52 < 52 by omega, show c.toNat - 48 + 52 < 62 by omega, ↓reduceIte]
    rw [show 48 + (c.toNat - 48 + 52 - 52) = c.toNat by omega, hc]
  split at h
  · cases h
    rename_i h
    subst h
    exact ⟨by omega, rfl⟩
  split at h
  · cases h
    rename_i h
    subst h
    exact ⟨by omega, rfl⟩
  · cases h

/-- A character that reads as a value is the character of that value. -/
theorem encodeSextet_of_readSextet {c : Char} {v : Nat} (h : readSextet c = .ok v) :
    v < 64 ∧ encodeSextet v = c := by
  unfold readSextet at h
  split at h
  · cases h
    apply encodeSextet_of_decodeSextet
    assumption
  · cases h

/-- The value of a byte written from `k`. -/
private theorem toNat_ofNat (k : Nat) : (UInt8.ofNat k).toNat = k % 256 := UInt8.toNat_ofNat'

/-- Three bytes cut from 24 bits encode as the four sextets of those bits. -/
private theorem encodeList_three (n : Nat) (hn : n < 2 ^ 24) (rest : List UInt8) :
    encodeList (UInt8.ofNat (n / 2 ^ 16) :: UInt8.ofNat (n / 2 ^ 8 % 256) :: UInt8.ofNat (n % 256)
      :: rest)
      = encodeSextet (n / 2 ^ 18) :: encodeSextet (n / 2 ^ 12 % 64) ::
        encodeSextet (n / 2 ^ 6 % 64) :: encodeSextet (n % 64) :: encodeList rest := by
  simp only [encodeList, toNat_ofNat]
  rw [show n / 2 ^ 16 % 256 * 2 ^ 16 + n / 2 ^ 8 % 256 % 256 * 2 ^ 8 + n % 256 % 256 = n
    by omega]

/-- Two bytes cut from 24 bits whose low 8 bits are zero encode as three sextets. -/
private theorem encodeList_two (n : Nat) (hn : n < 2 ^ 24) (hz : n % 2 ^ 8 = 0) :
    encodeList [UInt8.ofNat (n / 2 ^ 16), UInt8.ofNat (n / 2 ^ 8 % 256)]
      = [encodeSextet (n / 2 ^ 18), encodeSextet (n / 2 ^ 12 % 64),
        encodeSextet (n / 2 ^ 6 % 64)] := by
  simp only [encodeList, toNat_ofNat]
  rw [show n / 2 ^ 16 % 256 * 2 ^ 16 + n / 2 ^ 8 % 256 % 256 * 2 ^ 8 = n by omega]

/-- One byte cut from 24 bits whose low 16 bits are zero encodes as two sextets. -/
private theorem encodeList_one (n : Nat) (hn : n < 2 ^ 24) (hz : n % 2 ^ 16 = 0) :
    encodeList [UInt8.ofNat (n / 2 ^ 16)]
      = [encodeSextet (n / 2 ^ 18), encodeSextet (n / 2 ^ 12 % 64)] := by
  simp only [encodeList, toNat_ofNat]
  rw [show n / 2 ^ 16 % 256 * 2 ^ 16 = n by omega]

/-- The encoder writes back every list of characters that the decoder accepts. -/
theorem encodeList_decodeList :
    (text : List Char) → (bytes : List UInt8) → decodeList text = .ok bytes →
      encodeList bytes = text
  | c0 :: c1 :: c2 :: c3 :: rest, bytes, h => by
    simp only [decodeList, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i s0 h0
    split at h; · cases h
    rename_i s1 h1
    split at h; · cases h
    rename_i s2 h2
    split at h; · cases h
    rename_i s3 h3
    split at h; · cases h
    rename_i tail ht
    cases h
    obtain ⟨l0, e0⟩ := encodeSextet_of_readSextet h0
    obtain ⟨l1, e1⟩ := encodeSextet_of_readSextet h1
    obtain ⟨l2, e2⟩ := encodeSextet_of_readSextet h2
    obtain ⟨l3, e3⟩ := encodeSextet_of_readSextet h3
    rw [encodeList_three _ (by omega), encodeList_decodeList rest tail ht]
    -- Each sextet comes back from the 24 bits.
    rw [show (s0 * 2 ^ 18 + s1 * 2 ^ 12 + s2 * 2 ^ 6 + s3) / 2 ^ 18 = s0 by omega,
      show (s0 * 2 ^ 18 + s1 * 2 ^ 12 + s2 * 2 ^ 6 + s3) / 2 ^ 12 % 64 = s1 by omega,
      show (s0 * 2 ^ 18 + s1 * 2 ^ 12 + s2 * 2 ^ 6 + s3) / 2 ^ 6 % 64 = s2 by omega,
      show (s0 * 2 ^ 18 + s1 * 2 ^ 12 + s2 * 2 ^ 6 + s3) % 64 = s3 by omega, e0, e1, e2, e3]
  | [c0, c1, c2], bytes, h => by
    simp only [decodeList, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i s0 h0
    split at h; · cases h
    rename_i s1 h1
    split at h; · cases h
    rename_i s2 h2
    split at h
    · rename_i hz
      cases h
      obtain ⟨l0, e0⟩ := encodeSextet_of_readSextet h0
      obtain ⟨l1, e1⟩ := encodeSextet_of_readSextet h1
      obtain ⟨l2, e2⟩ := encodeSextet_of_readSextet h2
      rw [encodeList_two _ (by omega) hz]
      rw [show (s0 * 2 ^ 18 + s1 * 2 ^ 12 + s2 * 2 ^ 6) / 2 ^ 18 = s0 by omega,
        show (s0 * 2 ^ 18 + s1 * 2 ^ 12 + s2 * 2 ^ 6) / 2 ^ 12 % 64 = s1 by omega,
        show (s0 * 2 ^ 18 + s1 * 2 ^ 12 + s2 * 2 ^ 6) / 2 ^ 6 % 64 = s2 by omega, e0, e1, e2]
    · cases h
  | [c0, c1], bytes, h => by
    simp only [decodeList, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i s0 h0
    split at h; · cases h
    rename_i s1 h1
    split at h
    · rename_i hz
      cases h
      obtain ⟨l0, e0⟩ := encodeSextet_of_readSextet h0
      obtain ⟨l1, e1⟩ := encodeSextet_of_readSextet h1
      rw [encodeList_one _ (by omega) hz]
      rw [show (s0 * 2 ^ 18 + s1 * 2 ^ 12) / 2 ^ 18 = s0 by omega,
        show (s0 * 2 ^ 18 + s1 * 2 ^ 12) / 2 ^ 12 % 64 = s1 by omega, e0, e1]
    · cases h
  | [_], _, h => by cases h
  | [], bytes, h => by
    simp only [decodeList, pure, Except.pure] at h
    cases h
    rfl

/-- The encoder writes back every text that the decoder accepts. -/
theorem encode_decode (text : String) (bytes : ByteArray) (h : decode text = .ok bytes) :
    encode bytes = text := by
  simp only [decode, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i list hlist
  cases h
  simp only [encode, encodeList_decodeList _ _ hlist, String.ofList_toList]

end EthLib.Base.Base64
