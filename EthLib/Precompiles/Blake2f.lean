module

public import EthLib.Cryptography.Hash.Blake2b

/-!
# `Precompiles.Blake2f`

The BLAKE2F precompile at address `0x09`, [EIP-152](https://eips.ethereum.org/EIPS/eip-152).

It runs the compression function F of BLAKE2b, [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) §3.2, with as many rounds as the caller asks for.

The input is exactly 213 bytes:

```text
[ rounds: 4 | h: 64 | m: 128 | t0: 8 | t1: 8 | f: 1 ]
```

- The rounds field is a 32-bit big-endian word.
- `h` is 8 words and `m` is 16 words.
- `t0` and `t1` are the low and high words of the offset counter.
- Every word is 64 bits, little-endian.
- The flag byte is `1` for true and `0` for false.

The output is the new state `h`, 64 bytes, in the same encoding.

The gas cost, one per round, is not part of this module.
-/

@[expose] public section

namespace EthLib.Precompiles.Blake2f

open EthLib.Cryptography.Hash

/-- The input length in bytes, `4 + 64 + 128 + 8 + 8 + 1`, EIP-152 Specification. -/
def INPUT_BYTES : Nat := 213

/-- The output length in bytes: the 8 words of the new state. -/
def OUTPUT_BYTES : Nat := 64

/-- An input of the right length. -/
abbrev Input := Vector UInt8 INPUT_BYTES

/-- The two errors of EIP-152. -/
inductive Blake2fError where
  /-- The input is not exactly 213 bytes, EIP-152 test vectors 0 to 2. -/
  | invalidLength (length : Nat)
  /-- The flag byte is neither `0` nor `1`, EIP-152 Specification. -/
  | invalidFlag (flag : UInt8)
  deriving Repr, DecidableEq

/-! ## Reading the input -/

/-- The number of rounds: bytes 0 to 3, a big-endian word. -/
def readRounds (input : Input) : UInt32 :=
  -- Horner's rule from the first byte: each later byte sits 8 bits lower.
  (List.finRange 4).foldl
    (fun acc k => (acc <<< 8) ||| (input[k.val]'(by simp only [INPUT_BYTES]; omega)).toUInt32) 0

/-- The little-endian word in the 8 bytes from `offset`, RFC 7693 §2.4.

Byte `k` carries bits `8k` to `8k + 7`. -/
def readWord (input : Input) (offset : Nat) (h : offset + 8 ≤ INPUT_BYTES) : UInt64 :=
  -- Horner's rule from the last byte: each earlier byte sits 8 bits lower.
  (List.finRange 8).foldr (fun k acc => (input[offset + k.val]'(by omega)).toUInt64 ||| (acc <<< 8)) 0

/-- The final block flag, from its byte, EIP-152 Specification.

`1` is true, `0` is false, and any other byte is an error. -/
def readFlag : UInt8 → Except Blake2fError Bool
  | 0 => .ok false
  | 1 => .ok true
  | flag => .error (.invalidFlag flag)

/-- The new state as 64 bytes, each word little-endian, EIP-152 Specification. -/
def writeState (h : Vector UInt64 8) : Vector UInt8 OUTPUT_BYTES :=
  -- Byte `k` of the output is byte `k mod 8` of word `k / 8`.
  Vector.ofFn fun k =>
    (h[k.val / 8]'(by simp only [OUTPUT_BYTES] at *; omega) >>> UInt64.ofNat (8 * (k.val % 8))).toUInt8

/-! ## The precompile -/

/-- F on the fields of a 213-byte input, given its decoded flag. -/
def compute (input : Input) (f : Bool) : Vector UInt8 OUTPUT_BYTES :=
  -- `h` starts at byte 4, `m` at byte 68, `t0` at 196 and `t1` at 204.
  let h := Vector.ofFn fun i : Fin 8 => readWord input (4 + 8 * i.val) (by simp only [INPUT_BYTES]; omega)
  let m := Vector.ofFn fun i : Fin 16 => readWord input (68 + 8 * i.val) (by simp only [INPUT_BYTES]; omega)
  let t0 := readWord input 196 (by simp only [INPUT_BYTES]; omega)
  let t1 := readWord input 204 (by simp only [INPUT_BYTES]; omega)
  writeState (Blake2b.compress (readRounds input).toNat h m t0 t1 f)

/-- The precompile: the 64 bytes of the new state, or the error the input raises.

The length is checked before the flag.

That order is the one of [`blake2f`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/bpo2/vm/precompiled_contracts/blake2f.py) in execution-specs.

EIP-152 does not fix it. -/
def blake2f (data : ByteArray) : Except Blake2fError (Vector UInt8 OUTPUT_BYTES) :=
  if hsize : data.size = INPUT_BYTES then
    let input : Input := ⟨data.data, hsize⟩
    -- The flag is byte 212, the last one.
    match readFlag (input[212]'(by simp only [INPUT_BYTES]; omega)) with
    | .error e => .error e
    | .ok f => .ok (compute input f)
  else .error (.invalidLength data.size)

end EthLib.Precompiles.Blake2f
