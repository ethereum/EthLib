import EthLib.Cryptography.Hash.Blake2b

/-!
# `Precompiles.Blake2f`

The precompile at address `0x09`, which runs the compression function F of BLAKE2b, as specified by EIP-152.

Its input is exactly 213 bytes: the number of rounds, then the inputs `h`, `m`, `t` and `f` of F in RFC 7693 §3.2.

The offset counter `t` comes as two words, `t0` and `t1`.

```text
    [ rounds: 4 | h: 64 | m: 128 | t0: 8 | t1: 8 | f: 1 ]
      0           4       68       196     204     212
```

The second line gives the offset of each field.

- `rounds` is a 32-bit unsigned big-endian word.
- `h` is 8 words, `m` is 16 words, and `t0` and `t1` are one word each, all of them 64-bit unsigned little-endian.
- `f` is `1` for true and `0` for false, and any other value is an error.

The output is F with `rounds` rounds: the new state `h`, in the same encoding, 64 bytes.

EIP-152 also prices a call at one gas per round, which is not specified here.
-/

namespace EthLib.Precompiles.Blake2f

open EthLib.Cryptography.Hash

/-- The length of the input in bytes: 4 + 64 + 128 + 8 + 8 + 1.

EIP-152, Specification: "taking exactly 213 bytes". -/
def INPUT_BYTES : Nat := 213

/-- The length of the output in bytes: the 8 words of the new state. -/
def OUTPUT_BYTES : Nat := 64

/-- An input of the right length. -/
abbrev Input := Vector UInt8 INPUT_BYTES

/-- The two errors of EIP-152. -/
inductive Blake2fError where
  /-- The input is not exactly 213 bytes.

  EIP-152, test vectors 0 to 2: "input length for BLAKE2 F precompile should be exactly 213 bytes". -/
  | invalidLength (length : Nat)
  /-- The final block indicator flag is neither `0` nor `1`.

  EIP-152, Specification: "All other values yield an invalid encoding of `f` error". -/
  | invalidFlag (flag : UInt8)
  deriving Repr, DecidableEq

/-! ## Reading the input -/

/-- The number of rounds: bytes 0 to 3, a big-endian word. -/
def readRounds (input : Input) : UInt32 :=
  -- Horner's rule from the first byte: each later byte sits 8 bits lower.
  (List.finRange 4).foldl
    (fun acc k => (acc <<< 8) ||| (input[k.val]'(by simp only [INPUT_BYTES]; omega)).toUInt32) 0

/-- The 64-bit word that the 8 bytes from `offset` spell, the first byte least significant.

So byte `k` carries bits `8k` to `8k + 7` of the word, as in RFC 7693 §2.4. -/
def readWord (input : Input) (offset : Nat) (h : offset + 8 ≤ INPUT_BYTES) : UInt64 :=
  -- Horner's rule from the last byte: each earlier byte sits 8 bits lower.
  (List.finRange 8).foldr (fun k acc => (input[offset + k.val]'(by omega)).toUInt64 ||| (acc <<< 8)) 0

/-- The final block indicator flag, from its byte.

EIP-152, Specification: `1` is true, `0` is false, and "All other values yield an invalid encoding of `f` error". -/
def readFlag : UInt8 → Except Blake2fError Bool
  | 0 => .ok false
  | 1 => .ok true
  | flag => .error (.invalidFlag flag)

/-- The new state as 64 bytes, each word little-endian. -/
def writeState (h : Vector UInt64 8) : Vector UInt8 OUTPUT_BYTES :=
  -- Byte `k` of the output is byte `k mod 8` of word `k / 8`.
  Vector.ofFn fun k =>
    (h[k.val / 8]'(by simp only [OUTPUT_BYTES] at *; omega) >>> UInt64.ofNat (8 * (k.val % 8))).toUInt8

/-! ## The precompile -/

/-- F on the fields of an input, once its flag is read. -/
def compute (input : Input) (f : Bool) : Vector UInt8 OUTPUT_BYTES :=
  -- `h` from byte 4 and `m` from byte 68, one word every 8 bytes, then `t0` and `t1`.
  let h := Vector.ofFn fun i : Fin 8 => readWord input (4 + 8 * i.val) (by simp only [INPUT_BYTES]; omega)
  let m := Vector.ofFn fun i : Fin 16 => readWord input (68 + 8 * i.val) (by simp only [INPUT_BYTES]; omega)
  let t0 := readWord input 196 (by simp only [INPUT_BYTES]; omega)
  let t1 := readWord input 204 (by simp only [INPUT_BYTES]; omega)
  writeState (Blake2b.compress (readRounds input).toNat h m t0 t1 f)

/-- Run the precompile on its input.

Returns the 64 bytes of the new state, or the error of EIP-152 that the input raises.

The length is checked first, then the flag, as in `blake2f` of execution-specs.

That is `forks/bpo2/vm/precompiled_contracts/blake2f.py` at `2c0c8e7`.

execution-specs charges the gas between the two checks. -/
def blake2f (data : ByteArray) : Except Blake2fError (Vector UInt8 OUTPUT_BYTES) :=
  if hsize : data.size = INPUT_BYTES then
    let input : Input := ⟨data.data, hsize⟩
    -- The flag is byte 212, the last one.
    match readFlag (input[212]'(by simp only [INPUT_BYTES]; omega)) with
    | .error e => .error e
    | .ok f => .ok (compute input f)
  else .error (.invalidLength data.size)

end EthLib.Precompiles.Blake2f
