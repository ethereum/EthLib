module

public import EthLib.Execution.Evm.Gas.Memory
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Evm.Gas.Memory`

The price of memory is `3 * w + w * w / 512` for `w` words, and it grows with the size.

The growth of memory pays the price of the new size minus the price of the old size.

A range of size 0 never grows memory, and nothing is paid when no range grows it.

The rounded size and the growth cover every range that is not empty.

Memory grows to the largest of its rounded size and the rounded ends of the ranges not empty.

A gas budget `g` bounds the words of memory by `w * w ≤ 512 * g`.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

/-- The price of memory in closed form, for `w` words. -/
theorem memoryGasCost_eq (sizeInBytes : Nat) :
    memoryGasCost sizeInBytes =
      3 * wordCount sizeInBytes + wordCount sizeInBytes * wordCount sizeInBytes / 512 := by
  simp [memoryGasCost, MEMORY_PER_WORD, Nat.pow_two, Nat.mul_comm]

/-- The price of memory grows with its size. -/
theorem memoryGasCost_mono {a b : Nat} (h : a ≤ b) : memoryGasCost a ≤ memoryGasCost b := by
  have hw := wordCount_mono h
  have := Nat.div_le_div_right (c := 512) (Nat.mul_le_mul hw hw)
  rw [memoryGasCost_eq, memoryGasCost_eq]
  omega

/-- Rounding up to whole words does not change the price. -/
theorem memoryGasCost_ceil32 (size : Nat) : memoryGasCost (ceil32 size) = memoryGasCost size := by
  simp only [memoryGasCost, wordCount_ceil32]

/-- A range of size 0 never grows memory. -/
theorem extendMemory_cons_zero (currentSize : Nat) (start : U256)
    (extensions : List (U256 × U256)) :
    extendMemory currentSize ((start, 0) :: extensions) = extendMemory currentSize extensions := by
  simp [extendMemory]

/-- Nothing grows and nothing is paid when every range has size 0 or ends in the rounded memory. -/
theorem extendMemory_eq_zero (currentSize : Nat) (extensions : List (U256 × U256))
    (h : ∀ p ∈ extensions, p.2 = 0 ∨ ceil32 (p.1.toNat + p.2.toNat) ≤ ceil32 currentSize) :
    extendMemory currentSize extensions = ⟨0, 0⟩ := by
  induction extensions with
  | nil => rfl
  | cons p extensions ih =>
    obtain ⟨start, size⟩ := p
    have hp := h (start, size) List.mem_cons_self
    have ih := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only at hp
    unfold extendMemory
    split
    · exact ih
    · simp [hp.resolve_left ‹_›, ih]

/-- The growth pays the price of the new size minus the price of the old size.

The new size is the rounded old size plus the growth. -/
theorem extendMemory_cost (currentSize : Nat) (extensions : List (U256 × U256)) :
    (extendMemory currentSize extensions).cost =
      memoryGasCost (ceil32 currentSize + (extendMemory currentSize extensions).expandBy) -
        memoryGasCost currentSize := by
  induction extensions generalizing currentSize with
  | nil => simp [extendMemory, memoryGasCost_ceil32]
  | cons p extensions ih =>
    obtain ⟨start, size⟩ := p
    unfold extendMemory
    split
    · exact ih currentSize
    · simp only
      split
      · exact ih currentSize
      · rename_i grows
        simp only at ⊢ ih
        -- The rest starts from the rounded end of the range, which is already rounded.
        rw [ih, ceil32_of_mod (ceil32_mod _)]
        have old := memoryGasCost_ceil32 currentSize
        generalize ceil32 (start.toNat + size.toNat) = after at grows ⊢
        generalize (extendMemory after extensions).expandBy = rest
        have up := memoryGasCost_mono (Nat.le_of_lt (Nat.lt_of_not_le grows))
        have further := memoryGasCost_mono (Nat.le_add_right after rest)
        rw [show ceil32 currentSize + (after - ceil32 currentSize + rest) = after + rest by omega]
        omega

/-- The rounded size and the growth for a list of ranges cover every range that is not empty. -/
theorem le_ceil32_add_expandBy (currentSize : Nat) (ranges : List (U256 × U256)) :
    ∀ r ∈ ranges, r.2 ≠ 0 →
      r.1.toNat + r.2.toNat ≤ ceil32 currentSize + (extendMemory currentSize ranges).expandBy := by
  induction ranges generalizing currentSize with
  | nil => simp
  | cons p ranges ih =>
    obtain ⟨start, size⟩ := p
    intro r hr hnz
    have hle := le_ceil32 (start.toNat + size.toNat)
    have hfix := ceil32_of_mod (ceil32_mod (start.toNat + size.toNat))
    unfold extendMemory
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [hnz, ↓reduceIte]
      split <;> (try dsimp only) <;> omega
    · have h1 := ih currentSize r hr hnz
      have h2 := ih (ceil32 (start.toNat + size.toNat)) r hr hnz
      split
      · exact h1
      · dsimp only
        split <;> (try dsimp only) <;> omega

/-- A gas budget bounds the words of memory: `w * w ≤ 512 * g`. -/
theorem wordCount_mul_self_le {sizeInBytes gas : Nat} (h : memoryGasCost sizeInBytes ≤ gas) :
    wordCount sizeInBytes * wordCount sizeInBytes ≤ 512 * gas := by
  rw [memoryGasCost_eq] at h
  -- The remainder of the square over 512 is below 512, and 3 gas per word pays for it.
  have zero : wordCount sizeInBytes = 0 → wordCount sizeInBytes * wordCount sizeInBytes = 0 :=
    fun hw => by simp [hw]
  generalize wordCount sizeInBytes * wordCount sizeInBytes = square at h zero ⊢
  omega

/-- The size after growing memory for each range in turn: the largest rounded end so far.

A range of size 0 leaves the size. -/
def grownSize (size : Nat) (ranges : List (U256 × U256)) : Nat :=
  ranges.foldl (fun size range =>
    if range.2 = 0 then size else max size (ceil32 (range.1.toNat + range.2.toNat))) size

/-- Memory grows to the largest of its rounded size and the rounded ends of the ranges.

Only the ranges that are not empty count. -/
theorem ceil32_add_expandBy (currentSize : Nat) (ranges : List (U256 × U256)) :
    ceil32 currentSize + (extendMemory currentSize ranges).expandBy =
      grownSize (ceil32 currentSize) ranges := by
  induction ranges generalizing currentSize with
  | nil => simp [extendMemory, grownSize]
  | cons p ranges ih =>
    obtain ⟨start, size⟩ := p
    unfold extendMemory
    simp only [grownSize, List.foldl_cons] at ih ⊢
    split
    · exact ih currentSize
    · split
      · rename_i stays
        rw [Nat.max_eq_left stays]
        exact ih currentSize
      · rename_i grows
        -- The rest grows from the rounded end of the range, which is already rounded.
        have hfix := ceil32_of_mod (ceil32_mod (start.toNat + size.toNat))
        have hrest := ih (ceil32 (start.toNat + size.toNat))
        rw [hfix] at hrest
        rw [Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_le grows)), ← hrest]
        dsimp only
        omega

/-- The grown size is at least the size, and at least the rounded end of each range not empty. -/
private theorem le_grownSize (size : Nat) (ranges : List (U256 × U256)) :
    size ≤ grownSize size ranges ∧
      ∀ r ∈ ranges, r.2 ≠ 0 → ceil32 (r.1.toNat + r.2.toNat) ≤ grownSize size ranges := by
  induction ranges generalizing size with
  | nil => simp [grownSize]
  | cons p ranges ih =>
    simp only [grownSize, List.foldl_cons] at ih ⊢
    -- The size after the first range is at least the size, and covers that range.
    have hs : size ≤ if p.2 = 0 then size else max size (ceil32 (p.1.toNat + p.2.toNat)) := by
      split <;> omega
    have hp : p.2 ≠ 0 →
        ceil32 (p.1.toNat + p.2.toNat) ≤
          if p.2 = 0 then size else max size (ceil32 (p.1.toNat + p.2.toNat)) := by
      intro hne
      simp only [hne, ↓reduceIte]
      omega
    obtain ⟨h1, h2⟩ := ih (if p.2 = 0 then size else max size (ceil32 (p.1.toNat + p.2.toNat)))
    generalize (if p.2 = 0 then size else max size (ceil32 (p.1.toNat + p.2.toNat))) = start
      at hs hp h1 h2 ⊢
    refine ⟨Nat.le_trans hs h1, fun r hr hne => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Nat.le_trans (hp hne) h1
    · exact h2 r hr hne

/-- The grown size is at most a bound on the size and on the rounded ends of the ranges. -/
private theorem grownSize_le {size bound : Nat} {ranges : List (U256 × U256)} (hsize : size ≤ bound)
    (hranges : ∀ r ∈ ranges, r.2 ≠ 0 → ceil32 (r.1.toNat + r.2.toNat) ≤ bound) :
    grownSize size ranges ≤ bound := by
  induction ranges generalizing size with
  | nil => simpa [grownSize] using hsize
  | cons p ranges ih =>
    simp only [grownSize, List.foldl_cons] at ih ⊢
    refine ih ?_ fun r hr hne => hranges r (List.mem_cons_of_mem _ hr) hne
    split
    · exact hsize
    · exact Nat.max_le.mpr ⟨hsize, hranges p List.mem_cons_self ‹_›⟩

/-- Growing memory for several ranges is growing it for the range with the largest end.

That range must not be empty, and its end must be the largest among the ranges not empty. -/
theorem extendMemory_eq_largest {currentSize : Nat} {ranges : List (U256 × U256)}
    {r : U256 × U256} (hr : r ∈ ranges) (hne : r.2 ≠ 0)
    (largest : ∀ q ∈ ranges, q.2 ≠ 0 → q.1.toNat + q.2.toNat ≤ r.1.toNat + r.2.toNat) :
    extendMemory currentSize ranges = extendMemory currentSize [r] := by
  -- Both lists grow memory to the larger of its rounded size and the rounded end of the range.
  have hall := ceil32_add_expandBy currentSize ranges
  have hone := ceil32_add_expandBy currentSize [r]
  have heq : grownSize (ceil32 currentSize) ranges = grownSize (ceil32 currentSize) [r] := by
    obtain ⟨a1, a2⟩ := le_grownSize (ceil32 currentSize) ranges
    obtain ⟨b1, b2⟩ := le_grownSize (ceil32 currentSize) [r]
    refine Nat.le_antisymm (grownSize_le b1 fun q hq hqne => ?_)
      (grownSize_le a1 fun q hq hqne => ?_)
    · exact Nat.le_trans (ceil32_mono (largest q hq hqne)) (b2 r List.mem_cons_self hne)
    · rw [List.mem_singleton.mp hq]
      exact a2 r hr hne
  have hexp : (extendMemory currentSize ranges).expandBy =
      (extendMemory currentSize [r]).expandBy := by
    omega
  -- The price follows from the growth.
  have hcost := extendMemory_cost currentSize ranges
  rw [hexp, ← extendMemory_cost] at hcost
  cases h1 : extendMemory currentSize ranges
  cases h2 : extendMemory currentSize [r]
  rw [h1, h2] at hexp
  rw [h1, h2] at hcost
  simp_all

end EthLib.Execution.Evm
