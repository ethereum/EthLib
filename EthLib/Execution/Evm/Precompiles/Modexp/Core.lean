module

public import EthLib.Execution.Evm.Precompiles.Modexp.Encoding
public import EthLib.Execution.Evm.Precompiles.Modexp.Gas
public import EthLib.Execution.Evm.Precompiles.Modexp.Errors
public import EthLib.Execution.Evm.PowMod

/-!
# `Evm.Precompiles.Modexp.Core`

The MODEXP precompile at address `0x05`, from EIP-198: `BASE ^ EXPONENT mod MODULUS`.

The steps run in this order:

1. Read the three lengths.
2. From Fusaka, reject any length above 1024, before any gas is charged (EIP-7823).
3. Charge the gas, and end the call when it runs out.
4. Read `BASE`, `EXPONENT` and `MODULUS`, and compute the output.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base
open EthLib.Execution.Evm (byteAt bufferRead powMod)

/-- The three length headers of an input, in bytes. -/
structure Lengths where
  base : Nat
  exponent : Nat
  modulus : Nat

/-- Read the three length headers.

EIP-198, Specification. -/
def parseLengths (data : ByteArray) : Lengths where
  base := readNat data 0 LENGTH_HEADER_BYTES
  exponent := readNat data LENGTH_HEADER_BYTES LENGTH_HEADER_BYTES
  modulus := readNat data (2 * LENGTH_HEADER_BYTES) LENGTH_HEADER_BYTES

/-- Reject a length above 1024 bytes.

EIP-7823, Specification.

The checks run in the order base, exponent, modulus, so the first oversized field is reported. -/
def checkLengths (l : Lengths) : Except ModexpError Unit :=
  if l.base > MAX_LENGTH_BYTES then .error (.lengthTooLarge .base l.base)
  else if l.exponent > MAX_LENGTH_BYTES then .error (.lengthTooLarge .exponent l.exponent)
  else if l.modulus > MAX_LENGTH_BYTES then .error (.lengthTooLarge .modulus l.modulus)
  else .ok ()

/-- Where `EXPONENT` starts: right after `BASE`. -/
def Lengths.exponentStart (l : Lengths) : Nat :=
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
- A zero modulus gives `len_mod` zero bytes, since the Yellow Paper takes `x mod 0 = 0`.
- An empty base and modulus give an empty output. -/
def compute (data : ByteArray) (l : Lengths) : ByteArray :=
  let base := readNat data BASE_OFFSET l.base
  let exponent := readNat data l.exponentStart l.exponent
  let modulus := readNat data l.modulusStart l.modulus
  -- The result is below the modulus, so it fits in `len_mod` bytes.
  let result := if modulus = 0 then 0 else powMod base exponent modulus
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
  let l := parseLengths data
  -- EIP-7823: bounds first, before any gas is charged.
  match checkLengthsAt fork l with
  | .error e => .error e
  | .ok () =>
    -- Gas is charged before the base, exponent and modulus are read.
    let cost := requiredGas fork data l
    if gas < cost then .error (.outOfGas cost gas) else .ok (compute data l)

end EthLib.Execution.Evm.Precompiles.Modexp
