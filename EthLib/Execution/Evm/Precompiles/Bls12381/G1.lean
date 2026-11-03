module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding

/-!
# `Evm.Precompiles.Bls12381.G1`

The BLS12-381 G1 precompiles of EIP-2537.

- G1ADD at `0x0b` adds two G1 points.

Source: [`forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py) of execution-specs at `2c0c8e7`.

Prague introduced them, and every later fork there accepts the same inputs with the same prices, up to Bogota.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Cryptography.Bls (G1)

/-- The price of G1ADD, `GasCosts.PRECOMPILE_BLS_G1ADD` in [`forks/amsterdam/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/gas.py#L117). -/
def GAS_G1ADD : Nat := 375

/-- `bls12_g1_add`: the sum of two G1 points, given as two encoded points.

The points need not be in the subgroup, only on the curve. -/
def bls12G1Add (data : ByteArray) (gas : Nat) : Except Bls12381Error ByteArray := do
  -- The length is checked before the gas is charged.
  if data.size ≠ 256 then
    throw (.invalidInputLength data.size)
  let bytes := data.data.toList
  if gas < GAS_G1ADD then
    throw (.outOfGas GAS_G1ADD gas)
  -- Both paddings are checked before either point is decoded.
  let first ← unpadG1 (bytes.take 128)
  let second ← unpadG1 (bytes.drop 128)
  let sum := G1.add (← bytesToG1 first false) (← bytesToG1 second false)
  return ⟨(padG1 (g1ToBytes sum)).toArray⟩

end EthLib.Execution.Evm.Precompiles.Bls12381
