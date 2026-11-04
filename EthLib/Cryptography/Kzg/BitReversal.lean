module

/-!
# `BitReversal`

The bit reversal of an index, and the bit-reversal permutation of an array.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.BitReversal

/-- Reverse the lower `bits` bits of `x` onto the accumulator `r`.

The accumulator starts at `0`. -/
def reverseBitsAux (x r : Nat) : Nat → Nat
  | 0 => r
  | bits + 1 => reverseBitsAux (x >>> 1) ((r <<< 1) ||| (x &&& 1)) bits

/-- Reverse the bit order of `n` over `log2 order` bits.

`order` must be a positive power of two. -/
def reverseBits (n order : Nat) : Nat :=
  reverseBitsAux n 0 order.log2

/-- The bit-reversal permutation: entry `i` of the output is entry `rev(i)` of the input.

Here `rev` reverses the bits of an index below the size.

The permutation is an involution. -/
def bitReversalPermutation {α : Type _} [Inhabited α]
    (seq : Array α) : Array α :=
  Array.ofFn (n := seq.size) fun i =>
    seq[reverseBits i.val seq.size]!

end EthLib.Cryptography.Kzg.BitReversal
