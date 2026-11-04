module

public import EthLib.Cryptography.Hash.Blake2b

/-!
# `Evm.Precompiles.Blake2f`

The BLAKE2F precompile at address `0x09`, from [EIP-152](https://eips.ethereum.org/EIPS/eip-152).

It runs F, the compression function of BLAKE2b in RFC 7693 §3.2, for the rounds asked for.

The input is exactly 213 bytes, and the output is the new 64-byte state.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Blake2f

open EthLib.Cryptography.Hash

/-- The input length in bytes, `4 + 64 + 128 + 8 + 8 + 1`, EIP-152 Specification. -/
def INPUT_BYTES : Nat := 213

/-- The output length in bytes: the 8 words of the new state. -/
def OUTPUT_BYTES : Nat := 64

/-- An input of the right length. -/
abbrev Input := Vector UInt8 INPUT_BYTES

/-- Why a BLAKE2F call fails: the two errors of EIP-152, or too little gas. -/
inductive Blake2fError where
  /-- The input is not exactly 213 bytes, EIP-152 test vectors 0 to 2. -/
  | invalidInputLength (size : Nat)
  /-- The flag byte is neither `0` nor `1`, EIP-152 Specification. -/
  | invalidFlag (flag : UInt8)
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Blake2fError.code : Blake2fError → UInt32
  | .invalidInputLength .. => 1
  | .invalidFlag .. => 2
  | .outOfGas .. => 3

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

/-- The 64 bytes of the new state, or the error of the input, before any gas is charged.

The length is checked before the flag.

EIP-152 does not fix that order, so this module fixes it. -/
def output (data : ByteArray) : Except Blake2fError (Vector UInt8 OUTPUT_BYTES) :=
  if hsize : data.size = INPUT_BYTES then
    let input : Input := ⟨data.data, hsize⟩
    -- The flag is byte 212, the last one.
    match readFlag (input[212]'(by simp only [INPUT_BYTES]; omega)) with
    | .error e => .error e
    | .ok f => .ok (compute input f)
  else .error (.invalidInputLength data.size)

/-! ## The price -/

/-- The price of each round, from EIP-152. -/
def GAS_PER_ROUND : Nat := 1

/-- The gas a call is charged: one gas per round, for a 213-byte input.

Any other input fails before the charge, so its price is 0. -/
def gasCost (data : ByteArray) : Nat :=
  if hsize : data.size = INPUT_BYTES then GAS_PER_ROUND * (readRounds ⟨data.data, hsize⟩).toNat
  else 0

/-- The call: the length is checked, then the gas is charged, then the flag is read.

EIP-152 does not order the two checks of the call data, so this module orders them. -/
def blake2f (data : ByteArray) (gas : Nat) : Except Blake2fError ByteArray :=
  if data.size ≠ INPUT_BYTES then .error (.invalidInputLength data.size)
  else if gas < gasCost data then .error (.outOfGas (gasCost data) gas)
  else (output data).map fun out => ⟨out.toArray⟩

end EthLib.Execution.Evm.Precompiles.Blake2f
