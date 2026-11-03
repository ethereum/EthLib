module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding

/-!
# `Evm.Precompiles.Bls12381.G2`

The BLS12-381 G2 precompiles of EIP-2537.

- G2ADD at `0x0d` adds two G2 points.
- G2MSM at `0x0e` sums the products of G2 points by 32-byte scalars, priced with a discount that grows with the number of pairs.

Source: [`forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py) of execution-specs at `2c0c8e7`.

Prague introduced them, and every later fork there accepts the same inputs with the same prices, up to Bogota.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bytesToNat)
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

/-- `LENGTH_PER_PAIR`: an encoded G2 point, then a 32-byte scalar. -/
def LENGTH_PER_PAIR_G2 : Nat := 288

/-- The price of one product, `GasCosts.PRECOMPILE_BLS_G2MUL` in [`forks/amsterdam/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/gas.py#L121). -/
def GAS_G2MUL : Nat := 22500

/-- `G2_K_DISCOUNT`: the discount for `k` pairs, entry `k - 1`, in thousandths.

Source: [`bls12_381/__init__.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py#L274). -/
def G2_K_DISCOUNT : Vector Nat 128 := #v[
  1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717, 711, 704, 699, 693, 688,
  683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646, 643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618,
  615, 613, 611, 609, 607, 606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582, 580,
  579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562, 561, 560, 559, 558, 557, 556, 555,
  554, 553, 552, 552, 551, 550, 549, 548, 547, 546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537,
  536, 535, 535, 534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524]

/-- `G2_MAX_DISCOUNT`: the discount for more than 128 pairs. -/
def G2_MAX_DISCOUNT : Nat := 524

/-- The discount for `k` pairs. -/
def discountG2 (k : Nat) : Nat :=
  if h : 0 < k ∧ k ≤ 128 then G2_K_DISCOUNT[k - 1] else G2_MAX_DISCOUNT

/-- The price of G2MSM on `k` pairs: `k * 22500 * discount / 1000`, rounded down. -/
def msmGasG2 (k : Nat) : Nat := k * GAS_G2MUL * discountG2 k / MULTIPLIER

/-- `g2_msm`: the sum of `[m]P` over the pairs, each point checked to be in the subgroup.

The scalar `m` is the full 32-byte integer, not reduced. -/
def g2Msm (pairs : List (List UInt8 × List UInt8)) : Except Bls12381Error G2 :=
  pairs.foldlM (init := G2.zero) fun sum (raw, scalar) => do
    let point ← bytesToG2 raw true
    return G2.add sum (G2.mulNat point (bytesToNat scalar))

/-- `bls12_g2_msm`: the multi-scalar multiplication of the pairs in the call data. -/
def bls12G2Msm (data : ByteArray) (gas : Nat) : Except Bls12381Error ByteArray := do
  -- The length is checked before the gas is charged.
  if data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G2 ≠ 0 then
    throw (.invalidInputLength data.size)
  let k := data.size / LENGTH_PER_PAIR_G2
  if gas < msmGasG2 k then
    throw (.outOfGas (msmGasG2 k) gas)
  -- Every padding is checked before any point is decoded.
  let pairs ← (chunks LENGTH_PER_PAIR_G2 k data.data.toList).mapM fun pair => do
    return (← unpadG2 (pair.take 256), pair.drop 256)
  return ⟨(padG2 (g2ToBytes (← g2Msm pairs))).toArray⟩

end EthLib.Execution.Evm.Precompiles.Bls12381
