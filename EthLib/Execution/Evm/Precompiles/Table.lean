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

The precompiled contracts of every fork, by address.

A fork adds precompiles, so a call runs a precompile only from the fork that adds it.

The EIP that adds each precompile names it, next to its fork.

Every precompile takes the call data and the gas, and returns the output or an error.

An error halts the call, which then consumes all its gas.

A call that succeeds uses exactly its price.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles

open EthLib.Base (Fork)

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

/-- The stable code of an error: one per precompile, for the C exports.

The code names the precompile that failed, and the message carries its error.

No code is 0, so a caller can keep 0 for an address with no precompile.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PrecompileError.code : PrecompileError → UInt32
  | .ecrecover _ => 1
  | .sha256 _ => 2
  | .ripemd160 _ => 3
  | .identity _ => 4
  | .modexp _ => 5
  | .altBn128 _ => 6
  | .blake2f _ => 7
  | .pointEvaluation _ => 8
  | .bls12381 _ => 9
  | .p256Verify _ => 10

/-- The addresses of the 18 precompiles of all forks, in increasing order. -/
def ADDRESSES : List Nat :=
  [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
    0x11, 0x100]

/-- The fork that adds the precompile at `address`, or none when no fork adds one. -/
def addedAt (address : Nat) : Option Fork :=
  match address with
  -- ECRECOVER, SHA-256, RIPEMD-160 and IDENTITY
  | 0x01 | 0x02 | 0x03 | 0x04 => some .frontier
  -- MODEXP (EIP-198), and the alt_bn128 precompiles (EIP-196 and EIP-197)
  | 0x05 | 0x06 | 0x07 | 0x08 => some .byzantium
  -- BLAKE2F (EIP-152)
  | 0x09 => some .istanbul
  -- The point evaluation (EIP-4844)
  | 0x0a => some .dencun
  -- The BLS12-381 precompiles (EIP-2537)
  | 0x0b | 0x0c | 0x0d | 0x0e | 0x0f | 0x10 | 0x11 => some .pectra
  -- P256VERIFY (EIP-7951)
  | 0x100 => some .fusaka
  | _ => none

/-- Whether a fork has a precompile at `address`. -/
def isPrecompile (fork : Fork) (address : Nat) : Bool :=
  match addedAt address with
  | some added => added ≤ fork
  | none => false

/-- The call of the precompile at `address` on the call data with the gas given.

It is `none` when the fork has no precompile at that address. -/
def run (fork : Fork) (address : Nat) (data : ByteArray) (gas : Nat) :
    Option (Except PrecompileError ByteArray) :=
  if !isPrecompile fork address then none else
  match address with
  | 0x01 => some ((Ecrecover.ecrecover data gas).mapError .ecrecover)
  | 0x02 => some ((Sha256.sha256 data gas).mapError .sha256)
  | 0x03 => some ((Ripemd160.ripemd160 data gas).mapError .ripemd160)
  | 0x04 => some ((Identity.identity data gas).mapError .identity)
  | 0x05 => some ((Modexp.modexp fork data gas).mapError .modexp)
  | 0x06 => some ((AltBn128.ecadd fork data gas).mapError .altBn128)
  | 0x07 => some ((AltBn128.ecmul fork data gas).mapError .altBn128)
  | 0x08 => some ((AltBn128.ecpairing fork data gas).mapError .altBn128)
  | 0x09 => some ((Blake2f.blake2f data gas).mapError .blake2f)
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

/-- The gas that the precompile at `address` charges for the call data.

It is `none` when the fork has no precompile at that address.

Some precompiles check the call data before the charge, and such a check can fail with any gas. -/
def price (fork : Fork) (address : Nat) (data : ByteArray) : Option Nat :=
  if !isPrecompile fork address then none else
  match address with
  | 0x01 => some Ecrecover.GAS_ECRECOVER
  | 0x02 => some (Sha256.gasCost data.size)
  | 0x03 => some (Ripemd160.gasCost data.size)
  | 0x04 => some (Identity.gasCost data.size)
  | 0x05 => some (Modexp.requiredGas fork data (Modexp.parseLengths data))
  | 0x06 => some (AltBn128.ecaddGas fork)
  | 0x07 => some (AltBn128.ecmulGas fork)
  | 0x08 => some (AltBn128.ecpairingGas fork data.size)
  | 0x09 => some (Blake2f.gasCost data)
  | 0x0a => some PointEvaluation.GAS_POINT_EVALUATION
  | 0x0b => some Bls12381.GAS_G1ADD
  | 0x0c => some (Bls12381.msmGasG1 (data.size / Bls12381.LENGTH_PER_PAIR_G1))
  | 0x0d => some Bls12381.GAS_G2ADD
  | 0x0e => some (Bls12381.msmGasG2 (data.size / Bls12381.LENGTH_PER_PAIR_G2))
  | 0x0f => some (Bls12381.pairingGas (data.size / Bls12381.LENGTH_PER_PAIRING_PAIR))
  | 0x10 => some Bls12381.GAS_G1MAP
  | 0x11 => some Bls12381.GAS_G2MAP
  | 0x100 => some P256Verify.GAS_P256VERIFY
  | _ => none

end EthLib.Execution.Evm.Precompiles
