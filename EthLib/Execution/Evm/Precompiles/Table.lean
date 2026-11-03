module

public import EthLib.Execution.Evm.Precompiles.AltBn128
public import EthLib.Execution.Evm.Precompiles.Blake2f
public import EthLib.Execution.Evm.Precompiles.Bls12381
public import EthLib.Execution.Evm.Precompiles.Ecrecover
public import EthLib.Execution.Evm.Precompiles.Identity
public import EthLib.Execution.Evm.Precompiles.Modexp
public import EthLib.Execution.Evm.Precompiles.P256Verify
public import EthLib.Execution.Evm.Precompiles.PointEvaluation
public import EthLib.Execution.Evm.Precompiles.Ripemd160
public import EthLib.Execution.Evm.Precompiles.Sha256

/-!
# `Precompiles.Table`

The 18 precompiled contracts of Bogota, by address.

The source is `PRE_COMPILED_CONTRACTS` in [`forks/bogota/vm/precompiled_contracts/mapping.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/bogota/vm/precompiled_contracts/mapping.py#L59).

Every precompile takes the call data and the gas, and returns the output or an error.

An error halts the call, which then consumes all its gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles

/-- Why a precompile call fails: the error of the precompile at the address called. -/
inductive PrecompileError where
  /-- ECRECOVER failed. -/
  | ecrecover (e : Ecrecover.EcrecoverError)
  /-- SHA-256 failed. -/
  | sha256 (e : Sha256.Sha256Error)
  /-- RIPEMD-160 failed. -/
  | ripemd160 (e : Ripemd160.Ripemd160Error)
  /-- IDENTITY failed. -/
  | identity (e : Identity.IdentityError)
  /-- MODEXP failed. -/
  | modexp (e : Modexp.ModexpError)
  /-- An alt_bn128 precompile failed. -/
  | altBn128 (e : AltBn128.AltBn128Error)
  /-- BLAKE2F failed. -/
  | blake2f (e : Blake2f.Blake2fError)
  /-- The point evaluation failed. -/
  | pointEvaluation (e : PointEvaluation.PointEvaluationError)
  /-- A BLS12-381 precompile failed. -/
  | bls12381 (e : Bls12381.Bls12381Error)
  /-- P256VERIFY failed. -/
  | p256Verify (e : P256Verify.P256VerifyError)
  deriving Repr, DecidableEq

/-- The addresses of the 18 precompiles, in increasing order. -/
def ADDRESSES : List Nat :=
  [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x100]

/-- The call of the precompile at `address` on the call data with the gas given.

It is `none` when no precompile has that address. -/
def run (address : Nat) (data : ByteArray) (gas : Nat) : Option (Except PrecompileError ByteArray) :=
  match address with
  | 0x01 => some ((Ecrecover.ecrecover data gas).mapError .ecrecover)
  | 0x02 => some ((Sha256.sha256 data gas).mapError .sha256)
  | 0x03 => some ((Ripemd160.call data gas).mapError .ripemd160)
  | 0x04 => some ((Identity.identity data gas).mapError .identity)
  | 0x05 => some ((Modexp.modexp data gas).mapError .modexp)
  | 0x06 => some ((AltBn128.ecadd data gas).mapError .altBn128)
  | 0x07 => some ((AltBn128.ecmul data gas).mapError .altBn128)
  | 0x08 => some ((AltBn128.ecpairing data gas).mapError .altBn128)
  | 0x09 => some ((Blake2f.call data gas).mapError .blake2f)
  | 0x0a => some ((PointEvaluation.pointEvaluation data gas).mapError .pointEvaluation)
  | 0x0b => some ((Bls12381.bls12G1Add data gas).mapError .bls12381)
  | 0x0c => some ((Bls12381.bls12G1Msm data gas).mapError .bls12381)
  | 0x0d => some ((Bls12381.bls12G2Add data gas).mapError .bls12381)
  | 0x0e => some ((Bls12381.bls12G2Msm data gas).mapError .bls12381)
  | 0x0f => some ((Bls12381.bls12Pairing data gas).mapError .bls12381)
  | 0x10 => some ((Bls12381.bls12MapFpToG1 data gas).mapError .bls12381)
  | 0x11 => some ((Bls12381.bls12MapFp2ToG2 data gas).mapError .bls12381)
  | 0x100 => some ((P256Verify.p256Verify data gas).mapError .p256Verify)
  | _ => none

end EthLib.Execution.Evm.Precompiles
