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

/-- With `r` on top of `bits` reversed bits, the result stays below `(r + 1) * 2^bits`. -/
theorem reverseBitsAux_lt (x r : Nat) : (bits : Nat) → reverseBitsAux x r bits < (r + 1) * 2 ^ bits
  | 0 => by simp [reverseBitsAux]
  | bits + 1 => by
    have hlow : x &&& 1 < 2 ^ 1 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hacc : (r <<< 1) ||| (x &&& 1) = 2 * r + (x &&& 1) := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
    have := reverseBitsAux_lt (x >>> 1) ((r <<< 1) ||| (x &&& 1)) bits
    rw [hacc] at this
    have hbit : x &&& 1 ≤ 1 := Nat.and_le_right
    have hpow : (2 * r + (x &&& 1) + 1) * 2 ^ bits ≤ (r + 1) * 2 ^ (bits + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ bits) 2, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    rw [reverseBitsAux, hacc]
    exact Nat.lt_of_lt_of_le this hpow

/-- A reversed index stays below a positive `order`: it has `log2 order` bits. -/
theorem reverseBits_lt (n : Nat) {order : Nat} (h : 0 < order) : reverseBits n order < order :=
  Nat.lt_of_lt_of_le (by simpa [reverseBits] using reverseBitsAux_lt n 0 order.log2)
    (Nat.log2_self_le (Nat.ne_of_gt h))

/-- The bit-reversal permutation: entry `i` of the output is entry `rev(i)` of the input.

Here `rev` reverses the bits of an index below the size.

The permutation is an involution when the size is a power of two. -/
def bitReversalPermutation {α : Type _} (seq : Array α) : Array α :=
  Array.ofFn (n := seq.size) fun i =>
    seq[reverseBits i.val seq.size]'(reverseBits_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt))

end EthLib.Cryptography.Kzg.BitReversal
