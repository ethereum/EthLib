module

public import EthLib.Execution.Evm.Step
public import EthLib.Execution.Proofs.Evm.Gas.Memory
public import Mathlib.Data.Nat.Sqrt

/-!
# Proofs: a frame cannot grow memory past a bound set by its gas

A frame pays the price of its memory out of its gas.

So a range that ends past a bound set by that gas halts the frame out of gas.

The gas is what the frame holds plus the price of its memory.

For at most `2^24` gas, the cap of [EIP-7825][eip7825], the bound is 2,941,344 bytes.

That the gas of a frame stays within the cap of its transaction is left to a later theorem.

[eip7825]: https://eips.ethereum.org/EIPS/eip-7825#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

/-! ## The size that a gas budget pays for -/

/-- A budget of `g` gas pays for at most `32 * ⌊√(512 * g)⌋` bytes of memory. -/
theorem size_le_of_memoryGasCost_le {size gas : Nat} (h : memoryGasCost size ≤ gas) :
    size ≤ 32 * Nat.sqrt (512 * gas) := by
  -- The words `w` of the size have `w * w ≤ 512 * g`, so `w ≤ ⌊√(512 * g)⌋`.
  have hw : wordCount size ≤ Nat.sqrt (512 * gas) :=
    Nat.le_sqrt.mpr (wordCount_mul_self_le h)
  exact Nat.le_trans (le_wordCount size) (Nat.mul_le_mul_left 32 hw)

/-- A budget of `2^24` gas pays for at most 2,941,344 bytes of memory, which is 91,917 words. -/
theorem size_le_of_memoryGasCost_le_txMax {size : Nat} (h : memoryGasCost size ≤ TX_MAX_GAS_LIMIT) :
    size ≤ 2941344 := by
  -- One more byte makes 91,918 words, which cost 16,777,548 gas, above `2^24`.
  refine Nat.le_of_not_lt fun above => ?_
  have more : memoryGasCost 2941345 ≤ memoryGasCost size := memoryGasCost_mono above
  have cost : TX_MAX_GAS_LIMIT < memoryGasCost 2941345 := by decide
  omega

/-! ## The growth of memory in a frame -/

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- A range that is not empty halts the frame out of gas when its end costs too much.

The end must cost more than the gas that the frame holds plus the price of its memory. -/
theorem chargeGasAndMemory_eq_error {evm : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} {r : U256 × U256} (hr : r ∈ ranges) (hne : r.2 ≠ 0)
    (above : GasMeter.gasHeld evm.gas + memoryGasCost evm.memory.size <
      memoryGasCost (r.1.toNat + r.2.toNat)) :
    chargeGasAndMemory evm cost ranges = .error .outOfGas := by
  unfold chargeGasAndMemory chargeGas
  cases hc : GasMeter.charge evm.gas (cost + (extendMemory evm.memory.size ranges).cost) with
  | error e =>
    rw [LawfulGasMeter.charge_error hc] at hc
    simp only [hc, bind, Except.bind]
  | ok after =>
    -- A charge that succeeds is at most the gas held.
    have paid := LawfulGasMeter.gasHeld_charge hc
    -- The growth reaches the end of the range, so it costs at least the price of that end.
    have reach := le_ceil32_add_expandBy evm.memory.size ranges r hr hne
    have grown := memoryGasCost_mono reach
    have price := extendMemory_cost evm.memory.size ranges
    have older := memoryGasCost_ceil32 evm.memory.size
    have hle := memoryGasCost_mono (le_ceil32 evm.memory.size)
    omega

/-- A range that is not empty halts the frame out of gas when it ends past a bound.

The bound is `32 * ⌊√(512 * g)⌋`, where `g` is the gas the frame holds plus the price of its memory.

It leaves out the linear part of the price, so at `2^24` gas it is 2,965,792 bytes, not the least.
-/
theorem chargeGasAndMemory_eq_error_of_lt {evm : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} {r : U256 × U256} (hr : r ∈ ranges) (hne : r.2 ≠ 0)
    (past : 32 * Nat.sqrt (512 * (GasMeter.gasHeld evm.gas + memoryGasCost evm.memory.size)) <
      r.1.toNat + r.2.toNat) :
    chargeGasAndMemory evm cost ranges = .error .outOfGas :=
  chargeGasAndMemory_eq_error hr hne
    (Nat.lt_of_not_le fun h => Nat.not_le_of_lt past (size_le_of_memoryGasCost_le h))

/-- With at most `2^24` gas, a range that is not empty and ends past 2,941,344 bytes halts.

The gas counts what the frame holds plus the price of its memory.

It halts out of gas. -/
theorem chargeGasAndMemory_eq_error_of_txMax {evm : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} {r : U256 × U256} (hr : r ∈ ranges) (hne : r.2 ≠ 0)
    (gas : GasMeter.gasHeld evm.gas + memoryGasCost evm.memory.size ≤ TX_MAX_GAS_LIMIT)
    (past : 2941344 < r.1.toNat + r.2.toNat) :
    chargeGasAndMemory evm cost ranges = .error .outOfGas :=
  chargeGasAndMemory_eq_error hr hne (Nat.lt_of_not_le fun h =>
    Nat.not_le_of_lt past (size_le_of_memoryGasCost_le_txMax (Nat.le_trans h gas)))

end EthLib.Execution.Evm
