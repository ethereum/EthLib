module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding
public import EthLib.Cryptography.Bls.Pairing

/-!
# `Evm.Precompiles.Bls12381.Pairing`

The BLS12-381 pairing check of EIP-2537, at address `0x0f`.

The call data lists `k` pairs of a G1 point and a G2 point:

```text
pair:    [ G1 point: 128 | G2 point: 256 ]
gas:     32600 * k + 37700
output:  1 as a 32-byte word when the product of the pairings is 1, and 0 otherwise
```

Source: [`forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_pairing.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_pairing.py#L25-L67), and `pairing_check` in [`crypto/bls12_381.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/crypto/bls12_381.py#L245-L266), of execution-specs at `2c0c8e7`.

Prague introduced it, and every later fork there accepts the same inputs with the same price, up to Bogota.

The product is checked with the pairing check of the BLS12-381 module.

The source raises each Miller loop to the final exponent, and this check raises their product once.

Both orders give the same result, because `(a * b)^e = a^e * b^e`.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Cryptography.Bls (G1 G2 pairingCheck)

/-- The size of one pair: an encoded G1 point, then an encoded G2 point. -/
def LENGTH_PER_PAIRING_PAIR : Nat := 384

/-- The price of each pair, written in the source. -/
def GAS_PAIRING_PER_PAIR : Nat := 32600

/-- The price of every call, written in the source. -/
def GAS_PAIRING_BASE : Nat := 37700

/-- The price of a pairing check on `k` pairs. -/
def pairingGas (k : Nat) : Nat := GAS_PAIRING_PER_PAIR * k + GAS_PAIRING_BASE

/-- The 32-byte word of a boolean: 1 for true, 0 for false. -/
def boolWord (result : Bool) : List UInt8 :=
  List.replicate 31 0 ++ [if result then 1 else 0]

/-- `bls12_pairing`: whether the product of the pairings of the pairs in the call data is 1.

Every point must be on its curve and in the subgroup of prime order. -/
def bls12Pairing (data : ByteArray) (gas : Nat) : Except Bls12381Error ByteArray := do
  -- The length is checked before the gas is charged.
  if data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0 then
    throw (.invalidInputLength data.size)
  let k := data.size / LENGTH_PER_PAIRING_PAIR
  if gas < pairingGas k then
    throw (.outOfGas (pairingGas k) gas)
  -- Every padding is checked before any point is decoded.
  let rawPairs ← (chunks LENGTH_PER_PAIRING_PAIR k data.data.toList).mapM fun pair => do
    return (← unpadG1 (pair.take 128), ← unpadG2 (pair.drop 128))
  -- Each pair is decoded in order, its G1 point first.
  let pairs ← rawPairs.mapM fun (rawG1, rawG2) => do
    return (← bytesToG1 rawG1 true, ← bytesToG2 rawG2 true)
  return ⟨(boolWord (pairingCheck pairs.toArray)).toArray⟩

end EthLib.Execution.Evm.Precompiles.Bls12381
