module

public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Execution.Evm.Memory

/-!
# `Evm.Precompiles.Ecrecover`

The ECRECOVER precompile at address `0x01`, from Appendix E of the Yellow Paper.

It returns the address that signed a 32-byte hash, so contracts can check signatures.

A rejected signature gives empty output, and the call still succeeds.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ecrecover

open EthLib.Cryptography.Secp256k1
open EthLib.Base (byteAt)

/-- Why an ECRECOVER call fails: only a lack of gas, which consumes all the gas given. -/
inductive EcrecoverError where
  /-- The gas given was below the price. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EcrecoverError.code : EcrecoverError → UInt32
  | .outOfGas .. => 1

/-- The gas of a call, from Appendix E of the Yellow Paper. -/
def GAS_ECRECOVER : Nat := 3000

/-- 32 bytes of the call data from `start`, zero-padded on the right. -/
def word (data : ByteArray) (start : Nat) : Vector UInt8 32 :=
  Vector.ofFn fun i => byteAt data (start + i.val)

/-- The output for a hash and the integers `v`, `r` and `s`. -/
def output (hash : Vector UInt8 32) (v r s : Nat) : ByteArray :=
  -- `v` is 27 or 28, the recovery id plus 27.
  if hv : v = 27 ∨ v = 28 then
    -- The recovery rejects `r` and `s` outside `[1, n - 1]`, as the Yellow Paper does first.
    match Ecdsa.recover hash r s ⟨v - 27, by omega⟩ with
    | .ok (.affine x y) => ⟨(List.replicate 12 0 ++ (address x y).toList).toArray⟩
    | _ => ByteArray.empty
  else ByteArray.empty

/-- The operation of the precompile: read the four words, then compute the output. -/
def compute (data : ByteArray) : ByteArray :=
  output (word data 0) (ofBytesBE (word data 32).toList) (ofBytesBE (word data 64).toList)
    (ofBytesBE (word data 96).toList)

/-- Run the precompile on `data` with `gas` available.

Returns the output, or the lack of gas that ends the call and consumes it all.

The gas is charged first, then the operation runs. -/
def ecrecover (data : ByteArray) (gas : Nat) : Except EcrecoverError ByteArray :=
  if gas < GAS_ECRECOVER then .error (.outOfGas GAS_ECRECOVER gas) else .ok (compute data)

end EthLib.Execution.Evm.Precompiles.Ecrecover
