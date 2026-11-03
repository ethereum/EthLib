module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding

/-!
# `Evm.Precompiles.Bls12381.G2`

The BLS12-381 G2 precompiles of EIP-2537.

- G2ADD at `0x0d` adds two G2 points.

Source: [`forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py) of execution-specs at `2c0c8e7`.

Prague introduced them, and every later fork there accepts the same inputs with the same prices, up to Bogota.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Cryptography.Bls (G2)

/-- The price of G2ADD, `GasCosts.PRECOMPILE_BLS_G2ADD` in [`forks/amsterdam/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/gas.py#L120). -/
def GAS_G2ADD : Nat := 600

/-- `bls12_g2_add`: the sum of two G2 points, given as two encoded points.

The points need not be in the subgroup, only on the curve. -/
def bls12G2Add (data : ByteArray) (gas : Nat) : Except Bls12381Error ByteArray := do
  -- The length is checked before the gas is charged.
  if data.size ≠ 512 then
    throw (.invalidInputLength data.size)
  let bytes := data.data.toList
  if gas < GAS_G2ADD then
    throw (.outOfGas GAS_G2ADD gas)
  -- Both paddings are checked before either point is decoded.
  let first ← unpadG2 (bytes.take 256)
  let second ← unpadG2 (bytes.drop 256)
  let sum := G2.add (← bytesToG2 first false) (← bytesToG2 second false)
  return ⟨(padG2 (g2ToBytes sum)).toArray⟩

end EthLib.Execution.Evm.Precompiles.Bls12381
