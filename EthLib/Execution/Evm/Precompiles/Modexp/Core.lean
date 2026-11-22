module

public import EthLib.Execution.Evm.Precompiles.Modexp.Encoding
public import EthLib.Execution.Evm.Precompiles.Modexp.Gas
public import EthLib.Execution.Evm.Precompiles.Modexp.Errors

/-!
# `Evm.Precompiles.Modexp.Core`

The MODEXP precompile at address `0x05`, from EIP-198: `BASE ^ EXPONENT mod MODULUS`.

From Fusaka, EIP-7823 bounds the three lengths before any gas is charged.

The precompile's body marks each of its four steps.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base
open EthLib.Execution.Evm (bufferRead)

/-- The three length headers of an input, in bytes. -/
structure Lengths where
  base : Nat
  exponent : Nat
  modulus : Nat

/-- Read the three length headers.

EIP-198, Specification. -/
def parseLengths (data : ByteArray) : Lengths where
  -- EIP-198: the input is `<length_of_BASE> <length_of_EXPONENT> <length_of_MODULUS> ...`.
  --
  -- EIP-198: every length is a 32-byte left-padded integer, so each is a 32-byte big-endian read.
  base := readNat data 0 LENGTH_HEADER_BYTES
  exponent := readNat data LENGTH_HEADER_BYTES LENGTH_HEADER_BYTES
  modulus := readNat data (2 * LENGTH_HEADER_BYTES) LENGTH_HEADER_BYTES

/-- Reject a length above 1024 bytes.

EIP-7823, Specification. -/
def checkLengths (l : Lengths) : Except ModexpError Unit :=
  -- EIP-7823: each length is at most 8192 bits, 1024 bytes.
  --
  -- Otherwise the call stops, returns an error and consumes all the gas.
  --
  -- EIP-7823 names no order; checking base, exponent, modulus reports the first oversized one.
  if l.base > MAX_LENGTH_BYTES then .error (.lengthTooLarge .base l.base)
  else if l.exponent > MAX_LENGTH_BYTES then .error (.lengthTooLarge .exponent l.exponent)
  else if l.modulus > MAX_LENGTH_BYTES then .error (.lengthTooLarge .modulus l.modulus)
  else .ok ()

/-- Where `EXPONENT` starts: right after `BASE`. -/
def Lengths.exponentStart (l : Lengths) : Nat :=
  -- EIP-198: `... <BASE> <EXPONENT> <MODULUS>`, each taking the bytes its length gives.
  BASE_OFFSET + l.base

/-- Where `MODULUS` starts: right after `EXPONENT`. -/
def Lengths.modulusStart (l : Lengths) : Nat :=
  l.exponentStart + l.exponent

/-- The first 32 bytes of `EXPONENT` as an integer, or all of it when shorter.

EIP-198 reads the highest bit of the exponent from these bytes. -/
def exponentHead (data : ByteArray) (l : Lengths) : Nat :=
  readNat data l.exponentStart (min EXPONENT_HEAD_BYTES l.exponent)

/-- The gas the call is charged, read from the input. -/
def requiredGas (fork : Fork) (data : ByteArray) (l : Lengths) : Nat :=
  gasCost fork l.base l.modulus l.exponent (exponentHead data l)

/-- The bound of EIP-7823 on the lengths, which holds from Fusaka. -/
def checkLengthsAt (fork : Fork) (l : Lengths) : Except ModexpError Unit :=
  if fork ≥ .fusaka then checkLengths l else .ok ()

/-- The operation of the precompile: the output bytes, once the gas is paid.

- The power is computed by square-and-multiply, one step per bit of the exponent.
- A zero modulus gives `length_of_MODULUS` zero bytes, since the Yellow Paper takes `x mod 0 = 0`.
- An empty base and modulus give an empty output. -/
def compute (data : ByteArray) (l : Lengths) : ByteArray :=
  -- EIP-198: `<BASE> <EXPONENT> <MODULUS>`, and any data after them is ignored.
  let base := readNat data BASE_OFFSET l.base
  let exponent := readNat data l.exponentStart l.exponent
  let modulus := readNat data l.modulusStart l.modulus
  -- EIP-198: the output is `BASE^EXPONENT mod MODULUS`.
  --
  -- EIP-198 leaves the modulus 0 open; the Yellow Paper, Appendix E, takes `x mod 0` to be zero.
  let result := if modulus = 0 then 0 else Nat.powMod base exponent modulus
  -- EIP-198: the output is a byte array with the same length as the modulus.
  --
  -- The result is below the modulus, so it fits in `length_of_MODULUS` bytes.
  ByteArray.mk (natToBytes l.modulus result).toArray

/-- The gas a call is charged, or the reason it fails before gas is charged. -/
def chargedGas (fork : Fork) (data : ByteArray) : Except ModexpError Nat :=
  let l := parseLengths data
  match checkLengthsAt fork l with
  | .error e => .error e
  | .ok () => .ok (requiredGas fork data l)

/-- Run the precompile on `data` with `gas` available.

Returns the output, or the error that consumes all the gas. -/
def modexp (fork : Fork) (data : ByteArray) (gas : Nat) : Except ModexpError ByteArray :=
  -- Step 1: read the three lengths.
  let l := parseLengths data
  -- Step 2, from Fusaka: EIP-7823 bounds the lengths first, before any gas is charged.
  match checkLengthsAt fork l with
  | .error e => .error e
  | .ok () =>
    -- Step 3: charge the gas, which reads the lengths and the first 32 bytes of `EXPONENT`.
    --
    -- The base, the full exponent and the modulus are read only once the gas is paid.
    let cost := requiredGas fork data l
    -- Step 4: EIP-198 returns the output if the gas suffices; else the call fails.
    if gas < cost then .error (.outOfGas cost gas) else .ok (compute data l)

end EthLib.Execution.Evm.Precompiles.Modexp
