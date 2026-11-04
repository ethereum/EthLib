module

public import EthLib.Execution.Evm.Precompiles.Blake2f

/-!
# Proofs: `Precompiles.Blake2f`

For every input:

- an input that is not 213 bytes long is rejected;
- a 213-byte input whose flag byte is neither `0` nor `1` is rejected;
- any other input returns F on its fields.

The fields are decoded as EIP-152 encodes them, for every input:

- the rounds field is big-endian;
- every word of `h`, `m`, `t0` and `t1` is little-endian;
- the output words are little-endian too, the encoding of the input.

With its gas, a 213-byte call fails exactly when the gas is below the number of rounds, and otherwise returns the precompile's result.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Blake2f

/-! ## The errors and the result -/

/-- The price of a 213-byte input is one gas per round. -/
theorem gasCost_of_size (data : ByteArray) (h : data.size = INPUT_BYTES) :
    gasCost data = GAS_PER_ROUND * (readRounds ⟨data.data, h⟩).toNat := by
  simp [gasCost, h]

/-- A call with a 213-byte input and too little gas runs out of gas, whatever its flag byte. -/
theorem call_outOfGas (data : ByteArray) (h : data.size = INPUT_BYTES) {gas : Nat}
    (hgas : gas < gasCost data) : call data gas = .error (.outOfGas (gasCost data) gas) := by
  simp [call, h, hgas]

/-- A call with a 213-byte input and enough gas returns the result of the precompile, as bytes. -/
theorem call_of_gas (data : ByteArray) (h : data.size = INPUT_BYTES) {gas : Nat}
    (hgas : gasCost data ≤ gas) : call data gas = (blake2f data).map fun out => ⟨out.toArray⟩ := by
  simp [call, h, Nat.not_lt.mpr hgas]

/-- A call with an input that is not 213 bytes long is rejected before any gas is charged. -/
theorem call_invalidLength (data : ByteArray) (h : data.size ≠ INPUT_BYTES) (gas : Nat) :
    call data gas = .error (.invalidLength data.size) := by
  simp [call, h]

/-- An input that is not 213 bytes long is rejected, whatever it holds. -/
theorem blake2f_invalidLength (data : ByteArray) (h : data.size ≠ INPUT_BYTES) :
    blake2f data = .error (.invalidLength data.size) := by
  simp [blake2f, h]

/-- A flag byte above `1` is rejected. -/
theorem readFlag_invalid (flag : UInt8) (hf : 1 < flag) : readFlag flag = .error (.invalidFlag flag) := by
  unfold readFlag
  split
  -- A flag of `0` or `1` contradicts `1 < flag`.
  · simp at hf
  · simp at hf
  -- Any other flag is the error.
  · rfl

/-- A 213-byte input whose flag byte is above `1` is rejected with that byte. -/
theorem blake2f_invalidFlag (data : ByteArray) (h : data.size = INPUT_BYTES) (hf : (1 : UInt8) < data[212]!) :
    blake2f data = .error (.invalidFlag data[212]!) := by
  -- Byte 212 is in range, so reading it with a default gives the byte itself.
  rw [getElem!_pos data 212 (by simp only [h, INPUT_BYTES]; omega), ByteArray.getElem_eq_getElem_data] at hf ⊢
  simp [blake2f, h, readFlag_invalid _ hf]

/-- A 213-byte input whose flag byte reads as `f` returns F on its fields, with that flag. -/
theorem blake2f_ok (data : ByteArray) (h : data.size = INPUT_BYTES) {f : Bool}
    (hf : readFlag data[212]! = .ok f) : blake2f data = .ok (compute ⟨data.data, h⟩ f) := by
  -- Byte 212 is in range, so reading it with a default gives the byte itself.
  rw [getElem!_pos data 212 (by simp only [h, INPUT_BYTES]; omega), ByteArray.getElem_eq_getElem_data] at hf
  simp [blake2f, h, hf]

/-- The three errors of a call, in the order the call checks them.

The length comes first, so a wrong length fails whatever the gas.

The gas comes next, so too little gas fails whatever the flag byte.

The flag byte comes last, so a bad flag fails only a call that pays its price. -/
theorem call_eq_error_iff (data : ByteArray) (gas : Nat) (e : Blake2fError) :
    call data gas = .error e ↔
      (data.size ≠ INPUT_BYTES ∧ e = .invalidLength data.size) ∨
      (data.size = INPUT_BYTES ∧ gas < gasCost data ∧ e = .outOfGas (gasCost data) gas) ∨
      (data.size = INPUT_BYTES ∧ gasCost data ≤ gas ∧ (1 : UInt8) < data[212]! ∧
        e = .invalidFlag data[212]!) := by
  by_cases hsize : data.size = INPUT_BYTES
  · by_cases hgas : gas < gasCost data
    · rw [call_outOfGas data hsize hgas]
      simp [hsize, hgas, eq_comm]
      -- Enough gas contradicts too little gas.
      intro h
      omega
    · have henough := Nat.le_of_not_lt hgas
      rw [call_of_gas data hsize henough]
      by_cases hf : (1 : UInt8) < data[212]!
      · rw [blake2f_invalidFlag data hsize hf]
        simp [hsize, hgas, henough, hf, eq_comm, Except.map]
      · -- A flag byte of `0` or `1` decodes, so the call succeeds.
        have h01 : ∀ x : UInt8, ¬(1 : UInt8) < x → x = 0 ∨ x = 1 := by
          intro x hx
          rw [UInt8.lt_iff_toNat_lt] at hx
          rcases (by simp at hx; omega : x.toNat = 0 ∨ x.toNat = 1) with h | h
          · exact .inl (UInt8.toNat_inj.mp h)
          · exact .inr (UInt8.toNat_inj.mp h)
        obtain ⟨f, hok⟩ : ∃ f, readFlag data[212]! = .ok f := by
          rcases h01 _ hf with h | h <;> rw [h] <;> exact ⟨_, rfl⟩
        rw [blake2f_ok data hsize hok]
        simp [hsize, hgas, hf, Except.map]
  · rw [call_invalidLength data hsize]
    simp [hsize, eq_comm]

/-! ## Decoding

The test vectors only sample the encoding.

These theorems fix it for every input. -/

/-- A byte or-ed below a word shifted up by 8 bits is their sum. -/
private theorem byte_or_shiftLeft_toNat (x : UInt8) (acc : UInt64) (hacc : acc.toNat < 2 ^ 56) :
    (x.toUInt64 ||| (acc <<< 8)).toNat = x.toNat + 2 ^ 8 * acc.toNat := by
  have hx := x.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  have : (8 : UInt64).toNat % 64 = 8 := by decide
  -- The shifted word has no bit below 8, so or-ing the byte adds it.
  rw [this, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

/-- Folding at most 8 bytes into a word, last byte highest, reads them in base `2^8`. -/
private theorem foldr_bytes_toNat (l : List UInt8) (hl : l.length ≤ 8) :
    (l.foldr (fun (b : UInt8) (acc : UInt64) => b.toUInt64 ||| acc <<< 8) 0).toNat =
        l.foldr (fun b acc => b.toNat + 2 ^ 8 * acc) 0 ∧
      l.foldr (fun b acc => b.toNat + 2 ^ 8 * acc) 0 < 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    obtain ⟨eq, lt⟩ := ih (by simp at hl; omega)
    have hb := b.toNat_lt
    -- The tail has at most 7 bytes, so its word fits in 56 bits.
    have : 2 ^ (8 * l.length) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by simp at hl; omega)
    simp only [List.foldr_cons, List.length_cons]
    rw [byte_or_shiftLeft_toNat _ _ (by omega), eq]
    refine ⟨rfl, ?_⟩
    rw [Nat.mul_add, Nat.pow_add]
    have := Nat.mul_le_mul_left (2 ^ 8) (Nat.succ_le_of_lt lt)
    omega

/-- Every word is read little-endian, RFC 7693 §2.4. -/
theorem readWord_toNat (input : Input) (offset : Nat) (h : offset + 8 ≤ INPUT_BYTES) :
    (readWord input offset h).toNat =
      input[offset].toNat + 2 ^ 8 * input[offset + 1].toNat + 2 ^ 16 * input[offset + 2].toNat +
      2 ^ 24 * input[offset + 3].toNat + 2 ^ 32 * input[offset + 4].toNat + 2 ^ 40 * input[offset + 5].toNat +
      2 ^ 48 * input[offset + 6].toNat + 2 ^ 56 * input[offset + 7].toNat := by
  -- The 8 bytes as a list, with plain indices.
  have key : readWord input offset h = [input[offset], input[offset + 1], input[offset + 2], input[offset + 3],
      input[offset + 4], input[offset + 5], input[offset + 6], input[offset + 7]].foldr
      (fun (b : UInt8) (acc : UInt64) => b.toUInt64 ||| acc <<< 8) 0 := rfl
  rw [key, (foldr_bytes_toNat _ (by simp)).1]
  simp only [List.foldr]
  omega

/-- A byte or-ed below a 32-bit word shifted up by 8 bits is their sum. -/
private theorem shiftLeft_or_byte_toNat (acc : UInt32) (x : UInt8) (hacc : acc.toNat < 2 ^ 24) :
    ((acc <<< 8) ||| x.toUInt32).toNat = 2 ^ 8 * acc.toNat + x.toNat := by
  have hx := x.toNat_lt
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  have : (8 : UInt32).toNat % 32 = 8 := by decide
  rw [this, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega),
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

/-- The rounds field is read big-endian, EIP-152 Specification. -/
theorem readRounds_toNat (input : Input) :
    (readRounds input).toNat =
      2 ^ 24 * input[0].toNat + 2 ^ 16 * input[1].toNat + 2 ^ 8 * input[2].toNat + input[3].toNat := by
  have key : readRounds input = [input[0], input[1], input[2], input[3]].foldl
      (fun (acc : UInt32) (b : UInt8) => (acc <<< 8) ||| b.toUInt32) 0 := rfl
  have := input[0].toNat_lt
  have := input[1].toNat_lt
  have := input[2].toNat_lt
  rw [key]
  simp only [List.foldl]
  -- Each byte read shifts the earlier ones 8 bits up.
  have r0 : ((0 : UInt32) <<< 8 ||| input[0].toUInt32).toNat = input[0].toNat := by
    rw [shiftLeft_or_byte_toNat _ _ (by decide)]
    simp
  have r1 : (((0 : UInt32) <<< 8 ||| input[0].toUInt32) <<< 8 ||| input[1].toUInt32).toNat =
      2 ^ 8 * input[0].toNat + input[1].toNat := by
    rw [shiftLeft_or_byte_toNat _ _ (by omega), r0]
  have r2 : ((((0 : UInt32) <<< 8 ||| input[0].toUInt32) <<< 8 ||| input[1].toUInt32) <<< 8 |||
      input[2].toUInt32).toNat = 2 ^ 16 * input[0].toNat + 2 ^ 8 * input[1].toNat + input[2].toNat := by
    rw [shiftLeft_or_byte_toNat _ _ (by omega), r1]
    omega
  rw [shiftLeft_or_byte_toNat _ _ (by omega), r2]
  omega

/-- Byte `k` of output word `i` is byte `k` of state word `i`, little-endian. -/
theorem writeState_byte (h : Vector UInt64 8) (i k : Fin 8) :
    ((writeState h)[8 * i.val + k.val]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ (8 * k.val) % 2 ^ 8 := by
  simp only [writeState, Vector.getElem_ofFn, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  have e2 : (8 * i.val + k.val) % 8 = k.val := by omega
  -- Output byte `8i + k` reads word `i`.
  have hi : h[(8 * i.val + k.val) / 8]'(by omega) = h[i] := by
    congr 1
    omega
  -- It shifts that word right by `8k` bits.
  have hs : (UInt64.ofNat (8 * ((8 * i.val + k.val) % 8))).toNat % 64 = 8 * k.val := by
    rw [e2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hi, hs, Nat.shiftRight_eq_div_pow]

/-- Output word `i`, read back little-endian, is state word `i`.

So the output keeps the encoding of the input, EIP-152 Specification. -/
theorem writeState_word (h : Vector UInt64 8) (i : Fin 8) :
    ((writeState h)[8 * i.val]'(by simp only [OUTPUT_BYTES]; omega)).toNat +
      2 ^ 8 * ((writeState h)[8 * i.val + 1]'(by simp only [OUTPUT_BYTES]; omega)).toNat +
      2 ^ 16 * ((writeState h)[8 * i.val + 2]'(by simp only [OUTPUT_BYTES]; omega)).toNat +
      2 ^ 24 * ((writeState h)[8 * i.val + 3]'(by simp only [OUTPUT_BYTES]; omega)).toNat +
      2 ^ 32 * ((writeState h)[8 * i.val + 4]'(by simp only [OUTPUT_BYTES]; omega)).toNat +
      2 ^ 40 * ((writeState h)[8 * i.val + 5]'(by simp only [OUTPUT_BYTES]; omega)).toNat +
      2 ^ 48 * ((writeState h)[8 * i.val + 6]'(by simp only [OUTPUT_BYTES]; omega)).toNat +
      2 ^ 56 * ((writeState h)[8 * i.val + 7]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat := by
  -- The 8 bytes of the word, one by one.
  have b0 : ((writeState h)[8 * i.val]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 0 % 2 ^ 8 := writeState_byte h i 0
  have b1 : ((writeState h)[8 * i.val + 1]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 8 % 2 ^ 8 := writeState_byte h i 1
  have b2 : ((writeState h)[8 * i.val + 2]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 16 % 2 ^ 8 := writeState_byte h i 2
  have b3 : ((writeState h)[8 * i.val + 3]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 24 % 2 ^ 8 := writeState_byte h i 3
  have b4 : ((writeState h)[8 * i.val + 4]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 32 % 2 ^ 8 := writeState_byte h i 4
  have b5 : ((writeState h)[8 * i.val + 5]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 40 % 2 ^ 8 := writeState_byte h i 5
  have b6 : ((writeState h)[8 * i.val + 6]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 48 % 2 ^ 8 := writeState_byte h i 6
  have b7 : ((writeState h)[8 * i.val + 7]'(by simp only [OUTPUT_BYTES]; omega)).toNat =
      h[i].toNat / 2 ^ 56 % 2 ^ 8 := writeState_byte h i 7
  -- The word is below `2^64`, so its 8 base-`2^8` digits add back up to it.
  have := h[i].toNat_lt
  rw [b0, b1, b2, b3, b4, b5, b6, b7]
  omega

/-- The flag byte decodes to `f` exactly when it is `1` for true or `0` for false. -/
theorem readFlag_ok_iff (flag : UInt8) (f : Bool) : readFlag flag = .ok f ↔ flag = if f then 1 else 0 := by
  constructor
  · intro h
    unfold readFlag at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    cases f <;> rfl

end EthLib.Execution.Evm.Precompiles.Blake2f
