module

public import EthLib.Execution.ErrorFormat
public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Execution.Evm.Machine.Memory

/-!
# `Evm.Precompiles.Ecrecover`

The ECRECOVER precompile at address `0x01`, from Appendix E of the Yellow Paper, Shanghai version.

The source is `Paper.tex` at `efc5f9a`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>

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
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def ecrecoverErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Evm.Precompiles.Ecrecover.EcrecoverError." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named. -/
def EcrecoverError.reprPrec : EcrecoverError → Nat → Std.Format
  | .outOfGas cost gas, p =>
    ecrecoverErrorFormat "outOfGas" [namedArg "cost" cost, namedArg "gas" gas] p

instance : Repr EcrecoverError := ⟨EcrecoverError.reprPrec⟩

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EcrecoverError.code : EcrecoverError → UInt32
  | .outOfGas .. => 1

/-- The gas of a call, from Appendix E of the Yellow Paper. -/
def GAS_ECRECOVER : Nat := 3000

/-- 32 bytes of the call data from `start`, zero-padded on the right. -/
def word (data : ByteArray) (start : Nat) : Vector UInt8 32 :=
  -- `d[0..(||I_d|| - 1)] = I_d` and `d[||I_d||..] = (0, 0, ...)`.
  Vector.ofFn fun i => byteAt data (start + i.val)

/-- The output for a hash and the integers `v`, `r` and `s`. -/
def output (hash : Vector UInt8 32) (v r s : Nat) : ByteArray :=
  -- `||o|| = 0` if `v` is not in `{27, 28}`.
  if hv : v = 27 ∨ v = 28 then
    -- `||o|| = 0` unless `0 < r < secp256k1n` and `0 < s < secp256k1n`.
    --
    -- The recovery makes that check, before it solves for the key.
    --
    -- `||o|| = 0` if `ECDSARECOVER(h, v - 27, r, s)` is empty.
    match Ecdsa.recover hash r s ⟨v - 27, by omega⟩ with
    -- `o[0..11] = 0` and `o[12..31] = KEC(ECDSARECOVER(h, v - 27, r, s))[12..31]`.
    | .ok (.affine x y) => ⟨(List.replicate 12 0 ++ (address x y).toList).toArray⟩
    | _ => ByteArray.empty
  else ByteArray.empty

/-- The operation of the precompile: read the four words, then compute the output. -/
def compute (data : ByteArray) : ByteArray :=
  -- `h = d[0..31]`, `v = d[32..63]`, `r = d[64..95]` and `s = d[96..127]`.
  output (word data 0) (Base.bytesToNat (word data 32).toList)
    (Base.bytesToNat (word data 64).toList) (Base.bytesToNat (word data 96).toList)

/-- Run the precompile on `data` with `gas` available.

Returns the output, or the lack of gas that ends the call and consumes it all.

The gas is charged first, then the operation runs. -/
def ecrecover (data : ByteArray) (gas : Nat) : Except EcrecoverError ByteArray :=
  -- `Xi_PRE`: the call fails if `g < g_r`, with `g_r = 3000`; else it returns `o`.
  if gas < GAS_ECRECOVER then .error (.outOfGas GAS_ECRECOVER gas) else .ok (compute data)

end EthLib.Execution.Evm.Precompiles.Ecrecover
