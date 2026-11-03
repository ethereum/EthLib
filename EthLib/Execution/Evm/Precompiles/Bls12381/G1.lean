module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding

/-!
# `Evm.Precompiles.Bls12381.G1`

The BLS12-381 G1 precompiles of EIP-2537.

- G1ADD at `0x0b` adds two G1 points.
- G1MSM at `0x0c` sums the products of G1 points by 32-byte scalars, priced with a discount that grows with the number of pairs.

Source: [`forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py) of execution-specs at `2c0c8e7`.

Prague introduced them, and every later fork there accepts the same inputs with the same prices, up to Bogota.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bytesToNat)
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

/-- `LENGTH_PER_PAIR`: an encoded G1 point, then a 32-byte scalar. -/
def LENGTH_PER_PAIR_G1 : Nat := 160

/-- The price of one product, `GasCosts.PRECOMPILE_BLS_G1MUL` in [`forks/amsterdam/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/gas.py#L118). -/
def GAS_G1MUL : Nat := 12000

/-- `G1_K_DISCOUNT`: the discount for `k` pairs, entry `k - 1`, in thousandths.

Source: [`bls12_381/__init__.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py#L143). -/
def G1_K_DISCOUNT : Vector Nat 128 := #v[
  1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677, 673, 669, 665, 661, 658, 654,
  651, 648, 645, 642, 640, 637, 635, 632, 630, 627, 625, 623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604,
  603, 601, 599, 598, 596, 595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576, 575, 574,
  573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 551,
  550, 549, 548, 547, 547, 546, 545, 544, 543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532,
  532, 531, 530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519]

/-- `G1_MAX_DISCOUNT`: the discount for more than 128 pairs. -/
def G1_MAX_DISCOUNT : Nat := 519

/-- The discount for `k` pairs. -/
def discountG1 (k : Nat) : Nat :=
  if h : 0 < k ∧ k ≤ 128 then G1_K_DISCOUNT[k - 1] else G1_MAX_DISCOUNT

/-- The price of G1MSM on `k` pairs: `k * 12000 * discount / 1000`, rounded down. -/
def msmGasG1 (k : Nat) : Nat := k * GAS_G1MUL * discountG1 k / MULTIPLIER

/-- `g1_msm`: the sum of `[m]P` over the pairs, each point checked to be in the subgroup.

The scalar `m` is the full 32-byte integer, not reduced. -/
def g1Msm (pairs : List (List UInt8 × List UInt8)) : Except Bls12381Error G1 :=
  pairs.foldlM (init := G1.zero) fun sum (raw, scalar) => do
    let point ← bytesToG1 raw true
    return G1.add sum (G1.mulNat point (bytesToNat scalar))

/-- `bls12_g1_msm`: the multi-scalar multiplication of the pairs in the call data. -/
def bls12G1Msm (data : ByteArray) (gas : Nat) : Except Bls12381Error ByteArray := do
  -- The length is checked before the gas is charged.
  if data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G1 ≠ 0 then
    throw (.invalidInputLength data.size)
  let k := data.size / LENGTH_PER_PAIR_G1
  if gas < msmGasG1 k then
    throw (.outOfGas (msmGasG1 k) gas)
  -- Every padding is checked before any point is decoded.
  let pairs ← (chunks LENGTH_PER_PAIR_G1 k data.data.toList).mapM fun pair => do
    return (← unpadG1 (pair.take 128), pair.drop 128)
  return ⟨(padG1 (g1ToBytes (← g1Msm pairs))).toArray⟩

end EthLib.Execution.Evm.Precompiles.Bls12381
