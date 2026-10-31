import EthLib.Precompiles.Blake2f

/-!
# Proofs: `Precompiles.Blake2f`

The first theorems say how the precompile treats any input.

- An input that is not 213 bytes long is rejected.
- A 213-byte input whose flag is neither `0` nor `1` is rejected.
- Any other input returns F on its fields.

The known answers at the end run test vectors 0 to 7 of EIP-152 through the whole precompile.

Three more pin what those vectors leave out: the rounds field of vector 8, the order of the words of `m`, and `t1`.
-/

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

/-! ## The test vectors of EIP-152

Every input but the empty one has the same 208 bytes of `h`, `m`, `t0` and `t1`:

- `h` is the IV of BLAKE2b with the parameter block of a 64-byte digest XORed into `h[0]`, as 8 little-endian words.
- `m` is the block "abc" followed by 125 zero bytes.
- `t0` is 3 and `t1` is 0.

The inputs differ in the rounds field before these bytes and in the flag after them.

The bytes are written as hex numbers of at most 32 bytes, digit for digit as the EIP prints them.

Only the 125 zero bytes of `m` are written as a run of zeros instead.

The kernel reads such a number at once, where it would read a string one character at a time.

`decide +kernel` has the kernel itself evaluate each claim, so no compiled code is trusted. -/

/-- `value` in base 256 on exactly `size` bytes, most significant first.

A value too large for its count gives the empty list, so a claim on it fails instead of comparing fewer bytes.

It is the `bytesOf` of the RLP vectors, repeated so that these proofs do not import RLP. -/
private def bytesOf (size value : Nat) : List UInt8 :=
  if value < 256 ^ size then go size value [] else []
where
  /-- The lowest `size` digits of `value`, in front of `acc`. -/
  go : Nat → Nat → List UInt8 → List UInt8
    | 0, _, acc => acc
    | size + 1, value, acc => go size (value / 256) (UInt8.ofNat (value % 256) :: acc)

/-- `h` in every input below. -/
private def initialState : List UInt8 :=
  bytesOf 32 0x48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5 ++
  bytesOf 32 0xd182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b

/-- `m`, `t0` and `t1` in the test vectors. -/
private def abcFields : List UInt8 :=
  [0x61, 0x62, 0x63] ++ List.replicate 125 0 ++
  bytesOf 8 0x0300000000000000 ++
  bytesOf 8 0x0000000000000000

/-- The bytes of a test vector: its rounds field, the shared fields, then its flag. -/
private def vectorBytes (rounds : List UInt8) (flag : UInt8) : List UInt8 :=
  rounds ++ initialState ++ abcFields ++ [flag]

/-- The input of a test vector. -/
private def vectorInput (rounds : List UInt8) (flag : UInt8) : ByteArray :=
  ⟨(vectorBytes rounds flag).toArray⟩

/-- The error of a failed call, or `none` for a success. -/
private def errorOf : Except Blake2fError (Vector UInt8 OUTPUT_BYTES) → Option Blake2fError
  | .error e => some e
  | .ok _ => none

/-- The bytes of a successful call, or `none` for a failure. -/
private def outputOf (result : Except Blake2fError (Vector UInt8 OUTPUT_BYTES)) : Option (List UInt8) :=
  result.toOption.map Vector.toList

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

Test vector 8 asks for `0xffffffff` rounds, that is 4294967295 of them, where vector 5 asks for 12.

The kernel cannot evaluate that many rounds, so no theorem states the output of vector 8.

Vectors 3 to 7 have zero in the first three bytes of the rounds field.

So `vector8_rounds` at least reads the rounds field of vector 8.

The vectors also leave words 1 to 15 of `m` at zero, so they cannot tell those words apart.

And none of them sets `t1`.

`fullBlock` and `highOffset` fill these two gaps. -/

/-- The rounds field of test vector 8, `ffffffff`, asks for 4294967295 rounds. -/
theorem vector8_rounds :
    readRounds ⟨(vectorBytes (bytesOf 4 0xffffffff) 0x01).toArray, by decide +kernel⟩ = 4294967295 := by
  decide +kernel

/-- One full block: BLAKE2b-512 of the 128 bytes `0x00` to `0x7f`, the known answer `compress_fullBlock` checks for F.

Here every word of `m` differs. -/
theorem fullBlock : outputOf (blake2f ⟨(bytesOf 4 0x0000000c ++ initialState ++ (List.range 128).map Nat.toUInt8 ++
    bytesOf 8 0x8000000000000000 ++ bytesOf 8 0x0000000000000000 ++ [0x01]).toArray⟩) = some (
    bytesOf 32 0x2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e ++
    bytesOf 32 0x8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115) := by
  decide +kernel

/-- Test vector 5 with `t1 = 1`, the high word of the offset counter.

`t1` stays zero until the offset counter `t` reaches `2^64` bytes, so no known answer of a hash sets it.

This answer is the output of `blake2f` in execution-specs at `2c0c8e7` on the same input. -/
theorem highOffset : outputOf (blake2f ⟨(bytesOf 4 0x0000000c ++ initialState ++ [0x61, 0x62, 0x63] ++
    List.replicate 125 0 ++ bytesOf 8 0x0300000000000000 ++ bytesOf 8 0x0100000000000000 ++ [0x01]).toArray⟩) = some (
    bytesOf 32 0x5811650d30e41b4e9641ddb368e6b697ac38f34598f74e9f253db772f522fa80 ++
    bytesOf 32 0x55e373dcd96b59e0e30efa21ed0c4110eeb8dc7a33d626ec6a2930a1808a5560) := by
  decide +kernel

end EthLib.Precompiles.Blake2f
