module

public import EthLib.Execution.Evm.Gas.Prices
public import EthLib.Execution.Evm.Words

/-!
# `Evm.Gas.Memory`

The price of memory, and the growth of memory that an instruction pays for.

Memory costs 3 gas per 32-byte word plus the square of the words over 512.

So a large memory costs quadratic gas.

An instruction that grows memory pays the price of the new size minus the price of the old size.

Appendix H.1 of the Yellow Paper, Shanghai version, defines the price and the growth of memory.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256)
open GasCosts

/-- The price of a memory of `sizeInBytes` bytes.

The size rounds up to whole words.

Each word costs 3, and the square of the words over 512 is added.

Source: the memory cost `C_mem` of Appendix H.1 of the Yellow Paper. -/
def memoryGasCost (sizeInBytes : Nat) : Nat :=
  let sizeInWords := wordCount sizeInBytes
  let linearCost := sizeInWords * MEMORY_PER_WORD
  let quadraticCost := sizeInWords ^ 2 / 512
  linearCost + quadraticCost

/-- What an instruction pays to grow memory, and the number of bytes it grows by. -/
structure ExtendMemory where
  /-- The gas to pay for the growth. -/
  cost : Nat
  /-- The number of bytes that memory grows by. -/
  expandBy : Nat
  deriving DecidableEq, Repr

/-- The growth of a memory of `currentSize` bytes for a list of ranges.

Each range is a start and a size, read in order.

A range of size 0 never grows memory.

A range that ends past the rounded memory grows it to the rounded end of the range.

It pays the price of the new size minus the price of the old size.

Source: the memory growth `M` of Appendix H.1 of the Yellow Paper. -/
def extendMemory (currentSize : Nat) : List (U256 × U256) → ExtendMemory
  | [] => ⟨0, 0⟩
  | (startPosition, size) :: extensions =>
    if size = 0 then
      extendMemory currentSize extensions
    else
      let beforeSize := ceil32 currentSize
      let afterSize := ceil32 (startPosition.toNat + size.toNat)
      if afterSize ≤ beforeSize then
        extendMemory currentSize extensions
      else
        let rest := extendMemory afterSize extensions
        ⟨memoryGasCost afterSize - memoryGasCost beforeSize + rest.cost,
          afterSize - beforeSize + rest.expandBy⟩

end EthLib.Execution.Evm
