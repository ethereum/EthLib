module

public import EthLib.Precompiles.Modexp.Bytes
public import EthLib.Precompiles.Modexp.Gas
public import EthLib.Precompiles.Modexp.Errors

/-!
# `Modexp.Core`

The MODEXP precompile at address `0x05`, as of the BPO2 fork.

The input has this layout, from EIP-198:

```text
    [ len_base: 32 | len_exp: 32 | len_mod: 32 | BASE | EXPONENT | MODULUS ]
```

- Each length is a 32-byte big-endian integer, counted in bytes.
- The call data reads as if followed by infinitely many zero bytes.
- So a short input is padded, and data past the last field is ignored.
- Each length must be at most 1024 (EIP-7823).

The output is `BASE ^ EXPONENT mod MODULUS`, as exactly `len_mod` big-endian bytes.

It is `len_mod` zero bytes when `MODULUS` is 0.

The steps run in the order of `modexp` in `forks/bpo2/vm/precompiled_contracts/modexp.py`.
That module is in execution-specs at `2c0c8e7`.

```text
    read the three lengths
      -> reject any length above 1024     (no gas charged)
      -> charge the gas                   (out of gas ends the call)
      -> read BASE, EXPONENT, MODULUS and compute the output
```
-/

@[expose] public section

namespace EthLib.Precompiles.Modexp

open EthLib.Precompiles.Modexp.Constants

/-- The three length headers of an input, in bytes. -/
structure Lengths where
  base : Nat
  exponent : Nat
  modulus : Nat

/-- Read the three length headers.

EIP-198, Specification.

The first lines of `modexp` in execution-specs. -/
def parseLengths (data : ByteArray) : Lengths where
  base := readNat data 0 LENGTH_HEADER_BYTES
  exponent := readNat data LENGTH_HEADER_BYTES LENGTH_HEADER_BYTES
  modulus := readNat data (2 * LENGTH_HEADER_BYTES) LENGTH_HEADER_BYTES

/-- Reject a length above 1024 bytes.

EIP-7823, Specification.

These are the three `ExceptionalHalt` checks of `modexp` in execution-specs.

They run in the order base, exponent, modulus, so the first oversized field is reported. -/
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

`exp_head` in `modexp` in execution-specs. -/
def exponentHead (data : ByteArray) (l : Lengths) : Nat :=
  readNat data l.exponentStart (min EXPONENT_HEAD_BYTES l.exponent)

/-- The gas the call is charged, read from the input.

`gas_cost(base_length, modulus_length, exp_length, exp_head)` in `modexp` in execution-specs. -/
def requiredGas (data : ByteArray) (l : Lengths) : Nat :=
  gasCost l.base l.modulus l.exponent (exponentHead data l)

/-- `b ^ e mod m` by square-and-multiply.

It takes one step per bit of `e`, at most 8192 for a 1024-byte exponent.

The direct `b ^ e % m` would first build `b ^ e`, a number of up to about `2 ^ 8205` bits.

Here `f(b, e)` stands for the result modulo 7:

```text
    f(3, 5)   e odd    = f(2, 2) * 3 mod 7     (3 * 3 mod 7 = 2)
    f(2, 2)   e even   = f(4, 1)               (2 * 2 mod 7 = 4)
    f(4, 1)   e odd    = f(2, 0) * 4 mod 7     (4 * 4 mod 7 = 2)
    f(2, 0)   e = 0    = 1

    unwinding:  1 * 4 mod 7 = 4,  then 4,  then 4 * 3 mod 7 = 5
    check:      3 ^ 5 = 243 = 34 * 7 + 5
```

A proof in the proofs library shows it equals `b ^ e % m` for every `m`. -/
def powMod (b e m : Nat) : Nat :=
  if h : e = 0 then 1 % m
  else
    -- The result for the exponent `e / 2` and the squared base.
    let half := powMod (b * b % m) (e / 2) m
    -- An odd exponent leaves one factor of `b` over.
    if e % 2 = 1 then half * b % m else half
termination_by e
decreasing_by omega

/-- The operation of the precompile: the output bytes, once the gas is paid.

The `# OPERATION` part of `modexp` in execution-specs.

- Python's `pow(base, exp, modulus)` is the square-and-multiply loop above.
- A zero modulus gives `len_mod` zero bytes.
- An empty base and modulus give an empty output, the early return of execution-specs. -/
def compute (data : ByteArray) (l : Lengths) : ByteArray :=
  let base := readNat data BASE_OFFSET l.base
  let exponent := readNat data l.exponentStart l.exponent
  let modulus := readNat data l.modulusStart l.modulus
  -- The result is below the modulus, so it fits in `len_mod` bytes.
  let result := if modulus = 0 then 0 else powMod base exponent modulus
  ByteArray.mk (natToBytes l.modulus result).toArray

/-- The gas a call is charged, or the reason it fails before gas is charged. -/
def chargedGas (data : ByteArray) : Except ModexpError Nat :=
  let l := parseLengths data
  match checkLengths l with
  | .error e => .error e
  | .ok () => .ok (requiredGas data l)

/-- Run the precompile on `data` with `gas` available.

Returns the output, or the error that consumes all the gas.

`modexp` in execution-specs. -/
def modexp (data : ByteArray) (gas : Nat) : Except ModexpError ByteArray :=
  let l := parseLengths data
  -- EIP-7823: bounds first, before any gas is charged.
  match checkLengths l with
  | .error e => .error e
  | .ok () =>
    -- Gas is charged before the base, exponent and modulus are read.
    let cost := requiredGas data l
    if gas < cost then .error (.outOfGas cost gas) else .ok (compute data l)

end EthLib.Precompiles.Modexp
