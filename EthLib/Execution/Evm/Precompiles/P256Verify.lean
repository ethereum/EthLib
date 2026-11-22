module

public import EthLib.Execution.ErrorFormat
public import EthLib.Base.BigEndian
public import EthLib.Cryptography.Secp256r1.Curve

/-!
# `Evm.Precompiles.P256Verify`

The P256VERIFY precompile at address `0x100`, from EIP-7951.

It checks an ECDSA signature over secp256r1, the curve of passkeys and secure enclaves.

An invalid input gives empty output, and the call fails only when the gas is below its price.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.P256Verify

open EthLib.Base (bytesToNat)
open EthLib.Cryptography.Secp256r1

/-- The size of the call data: the hash, the signature and the public key, 32 bytes each. -/
def INPUT_BYTES : Nat := 160

/-- The price of every call, from EIP-7951, Gas Schedule. -/
def GAS_P256VERIFY : Nat := 6900

/-- Why a P256VERIFY call fails. -/
inductive P256VerifyError where
  /-- The gas given was below the price. -/
  | outOfGas (cost gas : Nat)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def p256VerifyErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat
    ("EthLib.Execution.Evm.Precompiles.P256Verify.P256VerifyError." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named. -/
def P256VerifyError.reprPrec : P256VerifyError → Nat → Std.Format
  | .outOfGas cost gas, p =>
    p256VerifyErrorFormat "outOfGas" [namedArg "cost" cost, namedArg "gas" gas] p

instance : Repr P256VerifyError := ⟨P256VerifyError.reprPrec⟩

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def P256VerifyError.code : P256VerifyError → UInt32
  | .outOfGas .. => 1

/-- The output for a valid signature: 1 as a 32-byte word. -/
def VALID : ByteArray := ⟨(List.replicate 31 (0 : UInt8) ++ [1]).toArray⟩

/-- Whether the call data holds a valid signature, by the checks and the algorithm of EIP-7951. -/
def isValid (bytes : List UInt8) : Bool :=
  -- The input: `h`, `r`, `s`, `qx` and `qy`, 32 bytes each.
  let e := bytesToNat (bytes.take 32)
  let r := bytesToNat ((bytes.drop 32).take 32)
  let s := bytesToNat ((bytes.drop 64).take 32)
  let qx := bytesToNat ((bytes.drop 96).take 32)
  let qy := bytesToNat (bytes.drop 128)
  -- Check 3: `0 <= qx < p` and `0 <= qy < p`.
  if hx : qx < Fp.modulus then
    if hy : qy < Fp.modulus then
      -- Check 5: `(qx, qy) != (0, 0)`, the encoding of the point at infinity.
      --
      -- The verification runs check 2 on `r` and `s`, then check 4 on the curve equation.
      --
      -- Then `s1 = s^(-1) (mod n)`, `R' = (h * s1) * G + (r * s1) * (qx, qy)`.
      --
      -- It fails if `R'` is the point at infinity; else it succeeds just when `R'.x = r (mod n)`.
      !(qx = 0 ∧ qy = 0) && verify (.affine ⟨qx, hx⟩ ⟨qy, hy⟩) e r s
    else false
  else false

/-- The call: the gas is charged first, then the call data is checked. -/
def p256Verify (data : ByteArray) (gas : Nat) : Except P256VerifyError ByteArray :=
  -- Gas Schedule: `6900` gas, the same on every input.
  if gas < GAS_P256VERIFY then .error (.outOfGas GAS_P256VERIFY gas)
  -- Check 1: the input must be exactly `160` bytes, else the output is empty.
  else if data.size ≠ INPUT_BYTES then .ok .empty
  -- A valid signature returns `1` as a 32-byte word, and anything else the empty output.
  else if isValid data.data.toList then .ok VALID
  else .ok .empty

end EthLib.Execution.Evm.Precompiles.P256Verify
