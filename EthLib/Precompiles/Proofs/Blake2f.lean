module

public import EthLib.Precompiles.Blake2f

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

Known answers then run test vectors 0 to 7 of EIP-152 through the whole precompile.
-/

@[expose] public section

namespace EthLib.Precompiles.Blake2f

/-! ## The errors and the result -/

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

/-! ## The test vectors of EIP-152

Every nonempty vector shares the 208 bytes of `h`, `m`, `t0` and `t1`:

- `h` is the IV of BLAKE2b, with the parameter block of a 64-byte digest in its first word;
- `m` is "abc" followed by 125 zero bytes;
- `t0` is 3 and `t1` is 0.

The vectors differ in the rounds field and in the flag byte.

Bytes are written as hex numbers, digit for digit as the EIP prints them.

The kernel reads a number at once, but a string one character at a time.

`decide +kernel` has the kernel evaluate each claim, so no compiled code is trusted. -/

namespace TestVector

/-- `value` in base 256 on exactly `size` bytes, most significant first.

A value too large for its count gives the empty list.

So a claim on it fails, instead of comparing fewer bytes. -/
def bytesOf (size value : Nat) : List UInt8 :=
  if value < 256 ^ size then go size value [] else []
where
  /-- The lowest `size` digits of `value`, in front of `acc`. -/
  go : Nat → Nat → List UInt8 → List UInt8
    | 0, _, acc => acc
    | size + 1, value, acc => go size (value / 256) (UInt8.ofNat (value % 256) :: acc)

/-- `h` in every input below. -/
def initialState : List UInt8 :=
  bytesOf 32 0x48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5 ++
  bytesOf 32 0xd182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b

/-- `m`, `t0` and `t1` in the test vectors. -/
def abcFields : List UInt8 :=
  [0x61, 0x62, 0x63] ++ List.replicate 125 0 ++
  bytesOf 8 0x0300000000000000 ++
  bytesOf 8 0x0000000000000000

/-- The bytes of a test vector: its rounds field, the shared fields, then its flag. -/
def vectorBytes (rounds : List UInt8) (flag : UInt8) : List UInt8 :=
  rounds ++ initialState ++ abcFields ++ [flag]

/-- The input of a test vector. -/
def vectorInput (rounds : List UInt8) (flag : UInt8) : ByteArray :=
  ⟨(vectorBytes rounds flag).toArray⟩

/-- The error of a failed call, or `none` for a success. -/
def errorOf : Except Blake2fError (Vector UInt8 OUTPUT_BYTES) → Option Blake2fError
  | .error e => some e
  | .ok _ => none

/-- The bytes of a successful call, or `none` for a failure. -/
def outputOf (result : Except Blake2fError (Vector UInt8 OUTPUT_BYTES)) : Option (List UInt8) :=
  result.toOption.map Vector.toList

end TestVector

open TestVector

/-- Test vector 0: the empty input. -/
theorem vector0 : errorOf (blake2f ByteArray.empty) = some (.invalidLength 0) := by
  decide +kernel

/-- Test vector 1: a rounds field one byte too short (3 bytes), so 212 bytes in all. -/
theorem vector1 :
    errorOf (blake2f (vectorInput (bytesOf 3 0x00000c) 0x01)) = some (.invalidLength 212) := by
  decide +kernel

/-- Test vector 2: a rounds field one byte too long (5 bytes), so 214 bytes in all. -/
theorem vector2 :
    errorOf (blake2f (vectorInput (bytesOf 5 0x000000000c) 0x01)) = some (.invalidLength 214) := by
  decide +kernel

/-- Test vector 3: the flag `02`. -/
theorem vector3 :
    errorOf (blake2f (vectorInput (bytesOf 4 0x0000000c) 0x02)) = some (.invalidFlag 2) := by
  decide +kernel

/-- Test vector 4: no round, so F only XORs the two halves of the initial work vector into `h`. -/
theorem vector4 : outputOf (blake2f (vectorInput (bytesOf 4 0x00000000) 0x01)) = some (
    bytesOf 32 0x08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5 ++
    bytesOf 32 0xd282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b) := by
  decide +kernel

/-- Test vector 5: the 12 rounds of BLAKE2b on a last block, which give BLAKE2b-512 of "abc" (RFC 7693 Appendix A). -/
theorem vector5 : outputOf (blake2f (vectorInput (bytesOf 4 0x0000000c) 0x01)) = some (
    bytesOf 32 0xba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1 ++
    bytesOf 32 0x7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923) := by
  decide +kernel

/-- Test vector 6: as vector 5, with the flag `00`. -/
theorem vector6 : outputOf (blake2f (vectorInput (bytesOf 4 0x0000000c) 0x00)) = some (
    bytesOf 32 0x75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752 ++
    bytesOf 32 0x98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735) := by
  decide +kernel

/-- Test vector 7: one round. -/
theorem vector7 : outputOf (blake2f (vectorInput (bytesOf 4 0x00000001) 0x01)) = some (
    bytesOf 32 0xb63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb ++
    bytesOf 32 0xa551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421) := by
  decide +kernel

/-! ## What the test vectors leave out

- Test vector 8 asks for `2^32 - 1` rounds, too many for the kernel to evaluate.
  Only its rounds field is checked.
- The vectors leave words 1 to 15 of `m` at zero, so they cannot tell those words apart.
- None of them sets `t1`.

The last two answers fill these gaps. -/

/-- The rounds field of test vector 8, `ffffffff`, asks for `2^32 - 1` rounds. -/
theorem vector8_rounds :
    readRounds ⟨(vectorBytes (bytesOf 4 0xffffffff) 0x01).toArray, by decide +kernel⟩ = 4294967295 := by
  decide +kernel

/-- One full block: BLAKE2b-512 of the 128 bytes `0x00` to `0x7f`.

Every word of `m` differs. -/
theorem fullBlock : outputOf (blake2f ⟨(bytesOf 4 0x0000000c ++ initialState ++ (List.range 128).map Nat.toUInt8 ++
    bytesOf 8 0x8000000000000000 ++ bytesOf 8 0x0000000000000000 ++ [0x01]).toArray⟩) = some (
    bytesOf 32 0x2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e ++
    bytesOf 32 0x8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115) := by
  decide +kernel

/-- Test vector 5 with `t1 = 1`, the high word of the offset counter.

A hash sets `t1` only past `2^64` bytes, so no hash known answer pins it.

This one pins the high word mixed into word 13 of the work vector. -/
theorem highOffset : outputOf (blake2f ⟨(bytesOf 4 0x0000000c ++ initialState ++ [0x61, 0x62, 0x63] ++
    List.replicate 125 0 ++ bytesOf 8 0x0300000000000000 ++ bytesOf 8 0x0100000000000000 ++ [0x01]).toArray⟩) = some (
    bytesOf 32 0x5811650d30e41b4e9641ddb368e6b697ac38f34598f74e9f253db772f522fa80 ++
    bytesOf 32 0x55e373dcd96b59e0e30efa21ed0c4110eeb8dc7a33d626ec6a2930a1808a5560) := by
  decide +kernel

end EthLib.Precompiles.Blake2f
