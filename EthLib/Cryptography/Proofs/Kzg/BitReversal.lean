import EthLib.Cryptography.Kzg.BitReversal

/-!
# Proofs: `BitReversal`

Correctness properties of `reverseBitsAux`, `reverseBits`, and
`bitReversalPermutation`.

The output bits of `reverseBitsAux` are characterized via `Nat.testBit`
(`testBit_reverseBitsAux`); everything else follows from that
characterization.
-/

namespace EthLib.Cryptography.Kzg.BitReversal

/-- Bit `i` of `reverseBitsAux x r bits`: below `bits` it is the mirrored
bit of `x`; at and above `bits` it comes from the accumulator `r`. -/
theorem testBit_reverseBitsAux (bits x r i : Nat) :
    (reverseBitsAux x r bits).testBit i =
      if i < bits then x.testBit (bits - 1 - i) else r.testBit (i - bits) := by
  induction bits generalizing x r i with
  | zero => simp [reverseBitsAux]
  | succ b ih =>
    rw [reverseBitsAux, ih]
    rcases Nat.lt_trichotomy i b with h | h | h
    · rw [if_pos h, if_pos (by omega), Nat.testBit_shiftRight]
      exact congrArg x.testBit (by omega)
    · subst h
      rw [if_neg (Nat.lt_irrefl i), if_pos (Nat.lt_succ_self i),
        Nat.sub_self, show i + 1 - 1 - i = 0 by omega]
      simp
    · rw [if_neg (by omega), if_neg (by omega),
        show i - b = (i - (b + 1)) + 1 by omega]
      have hand : x &&& 1 < 2 ^ (i - (b + 1) + 1) :=
        Nat.lt_of_le_of_lt Nat.and_le_right
          (Nat.one_lt_two_pow (Nat.succ_ne_zero _))
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.testBit_lt_two_pow hand]
      simp [Nat.le_add_left]

/-- Bit `i` of `reverseBits n (2 ^ k)` is bit `k - 1 - i` of `n`
(and `false` at or above `k`). -/
theorem testBit_reverseBits (n k i : Nat) :
    (reverseBits n (2 ^ k)).testBit i =
      if i < k then n.testBit (k - 1 - i) else false := by
  rw [reverseBits, Nat.log2_two_pow, testBit_reverseBitsAux]
  simp

/-- `reverseBits _ order` stays below `order` for power-of-two `order`. -/
theorem reverseBits_lt_two_pow (n k : Nat) :
    reverseBits n (2 ^ k) < 2 ^ k := by
  rcases Nat.lt_or_ge (reverseBits n (2 ^ k)) (2 ^ k) with h | h
  · exact h
  · obtain ⟨i, hi, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow h
    rw [testBit_reverseBits, if_neg (by omega)] at hbit
    exact absurd hbit Bool.false_ne_true

/-- `reverseBits _ order` is an involution on `[0, order)` for
power-of-two `order`. -/
theorem reverseBits_reverseBits {n k : Nat} (h : n < 2 ^ k) :
    reverseBits (reverseBits n (2 ^ k)) (2 ^ k) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_reverseBits]
  by_cases hi : i < k
  · rw [if_pos hi, testBit_reverseBits, if_pos (by omega)]
    exact congrArg n.testBit (by omega)
  · rw [if_neg hi]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))).symm

/-- `bitReversalPermutation` preserves size. -/
theorem size_bitReversalPermutation {α : Type _} [Inhabited α]
    (seq : Array α) :
    (bitReversalPermutation seq).size = seq.size := by
  simp [bitReversalPermutation]

/-- Element `i` of `bitReversalPermutation seq` is element
`reverseBits i seq.size` of `seq`. -/
theorem getElem_bitReversalPermutation {α : Type _} [Inhabited α]
    (seq : Array α) (i : Nat) (h : i < (bitReversalPermutation seq).size) :
    (bitReversalPermutation seq)[i] = seq[reverseBits i seq.size]! := by
  simp [bitReversalPermutation]

/-- `bitReversalPermutation` is an involution on arrays whose size is a
power of two, as claimed in its docstring. -/
theorem bitReversalPermutation_bitReversalPermutation {α : Type _}
    [Inhabited α] (seq : Array α) {k : Nat} (hsize : seq.size = 2 ^ k) :
    bitReversalPermutation (bitReversalPermutation seq) = seq := by
  apply Array.ext
  · rw [size_bitReversalPermutation, size_bitReversalPermutation]
  · intro i h1 h2
    have hrev : reverseBits i seq.size < seq.size := by
      rw [hsize]; exact reverseBits_lt_two_pow i k
    have hback : reverseBits (reverseBits i seq.size) seq.size = i := by
      rw [hsize]; exact reverseBits_reverseBits (hsize ▸ h2)
    rw [getElem_bitReversalPermutation _ i h1, size_bitReversalPermutation,
      getElem!_pos (bitReversalPermutation seq) (reverseBits i seq.size)
        (by rwa [size_bitReversalPermutation]),
      getElem_bitReversalPermutation seq (reverseBits i seq.size)
        (by rwa [size_bitReversalPermutation]),
      hback, getElem!_pos seq i h2]

end EthLib.Cryptography.Kzg.BitReversal
