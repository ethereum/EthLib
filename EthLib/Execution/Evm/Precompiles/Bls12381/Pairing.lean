module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding
public import EthLib.Cryptography.Bls.Pairing

/-!
# `Evm.Precompiles.Bls12381.Pairing`

The BLS12-381 pairing check of EIP-2537, at address `0x0f`.

The source raises each Miller loop to the final exponent, and this check raises their product once.

Both orders give the same result, because `(a * b)^e = a^e * b^e`.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Cryptography.Bls (G1 G2 pairingCheck)

/-- The size of one pair: an encoded G1 point, then an encoded G2 point. -/
def LENGTH_PER_PAIRING_PAIR : Nat := 384

/-- The price of each pair, from EIP-2537, Gas schedule. -/
def GAS_PAIRING_PER_PAIR : Nat := 32600

/-- The price of every call, from EIP-2537, Gas schedule. -/
def GAS_PAIRING_BASE : Nat := 37700

/-- The price of a pairing check on `k` pairs. -/
def bls12PairingGas (k : Nat) : Nat :=
  -- `gas_cost = 32600*k + 37700`.
  GAS_PAIRING_PER_PAIR * k + GAS_PAIRING_BASE

/-- The 32-byte word of a boolean: 1 for true, 0 for false. -/
def boolWord (result : Bool) : List UInt8 :=
  -- `32` bytes: `31` bytes `0x00`, then `0x00` (false) or `0x01` (true).
  List.replicate 31 0 ++ [if result then 1 else 0]

/-- Whether the product of the pairings of the pairs in the call data is 1.

Every point must be on its curve and in the subgroup of prime order. -/
def bls12Pairing (data : ByteArray) (gas : Nat) : Except Bls12381Error ByteArray := do
  -- Pairing check expects `384*k` bytes, `k` being a positive integer.
  --
  -- The length is checked before the gas is charged; either error burns all the gas.
  if data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0 then
    throw (.invalidInputLength data.size)
  -- `k = floor(len(input) / LEN_PER_PAIR)`, exact here.
  let k := data.size / LENGTH_PER_PAIRING_PAIR
  if gas < bls12PairingGas k then
    throw (.outOfGas (bls12PairingGas k) gas)
  -- Every padding is checked before any point is decoded.
  let rawPairs ← (chunks LENGTH_PER_PAIRING_PAIR k data.data.toList).mapM fun pair => do
    return (← unpadG1 (pair.take 128), ← unpadG2 (pair.drop 128))
  -- Each pair is decoded in order, its G1 point first.
  --
  -- Each point is expected to be in the subgroup of order `q`.
  let pairs ← rawPairs.mapM fun (rawG1, rawG2) => do
    return (← bytesToG1 rawG1 true, ← bytesToG2 rawG2 true)
  -- `e(P1, Q1) * e(P2, Q2) * ... * e(Pk, Qk) == 1`.
  return ⟨(boolWord (pairingCheck pairs.toArray)).toArray⟩

end EthLib.Execution.Evm.Precompiles.Bls12381
