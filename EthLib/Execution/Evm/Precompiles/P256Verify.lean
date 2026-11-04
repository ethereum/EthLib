module

public import EthLib.Base.BigEndian
public import EthLib.Cryptography.Secp256r1.Curve

/-!
# `Evm.Precompiles.P256Verify`

The P256VERIFY precompile at address `0x100`, from EIP-7951: an ECDSA signature check over secp256r1, the curve of passkeys and secure enclaves.

```text
input:   [ hash: 32 | r: 32 | s: 32 | qx: 32 | qy: 32 ]
gas:     6900
output:  1 as a 32-byte word for a valid signature, and no bytes otherwise
```

Source: EIP-7951, at <https://eips.ethereum.org/EIPS/eip-7951>.

The check follows the verification algorithm of EIP-7951, which is SEC 1 v2 §4.1.4.

Every later fork computes the same result with the same price.

The call fails only when it runs out of gas.

Every invalid input gives empty output: a wrong length, a value out of range, an invalid key or an invalid signature.

The call still pays its gas.
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
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def P256VerifyError.code : P256VerifyError → UInt32
  | .outOfGas .. => 1

/-- The output for a valid signature: 1 as a 32-byte word. -/
def VALID : ByteArray := ⟨(List.replicate 31 (0 : UInt8) ++ [1]).toArray⟩

/-- Whether the call data holds a valid signature, by the input validation and the algorithm of EIP-7951.

- `r` and `s` lie in `(0, n)`.
- `qx` and `qy` lie in `[0, p)`, are not both 0, and satisfy the curve equation.
- The signature verifies under that key. -/
def isValid (bytes : List UInt8) : Bool :=
  let e := bytesToNat (bytes.take 32)
  let r := bytesToNat ((bytes.drop 32).take 32)
  let s := bytesToNat ((bytes.drop 64).take 32)
  let qx := bytesToNat ((bytes.drop 96).take 32)
  let qy := bytesToNat (bytes.drop 128)
  if hx : qx < Fp.modulus then
    if hy : qy < Fp.modulus then
      -- `(0, 0)` encodes the point at infinity, which is not a public key.
      !(qx = 0 ∧ qy = 0) && verify (.affine ⟨qx, hx⟩ ⟨qy, hy⟩) e r s
    else false
  else false

/-- `p256verify`: the gas is charged first, then the call data is checked. -/
def p256Verify (data : ByteArray) (gas : Nat) : Except P256VerifyError ByteArray :=
  if gas < GAS_P256VERIFY then .error (.outOfGas GAS_P256VERIFY gas)
  else if data.size ≠ INPUT_BYTES then .ok .empty
  else if isValid data.data.toList then .ok VALID
  else .ok .empty

end EthLib.Execution.Evm.Precompiles.P256Verify
