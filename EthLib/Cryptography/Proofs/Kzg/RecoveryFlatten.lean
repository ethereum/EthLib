import EthLib.Cryptography.Proofs.Kzg.RecoveryDomain

/-!
# Proofs: flattening cells into one evaluation array

Recovery writes each provided cell into a zero-filled array of 8192 entries.

```text
    cell ci, entry j   ->   position ci * 64 + j
```

The loop invariant: a position holds its cell's value if that cell was provided, and zero otherwise.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal

private theorem size_write_prefix (acc cell : Array Fr) (start n : Nat) :
    ((List.range n).foldl (fun a j => a.set! (start + j) cell[j]!) acc).size = acc.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    exact Array.size_setIfInBounds.trans ih

private theorem getElem!_set! (acc : Array Fr) (pos m : Nat) (v : Fr)
    (hm : m < acc.size) :
    (acc.set! pos v)[m]! = if pos = m then v else acc[m]! := by
  rw [getElem!_pos (acc.set! pos v) m (by simpa using hm),
    getElem!_pos acc m hm]
  exact Array.getElem_setIfInBounds _

/-- Lookup after a prefix of a cell's executable writes. -/
private theorem getElem!_write_prefix (acc cell : Array Fr) (start n m : Nat)
    (hm : m < acc.size) :
    ((List.range n).foldl (fun a j => a.set! (start + j) cell[j]!) acc)[m]! =
      if start ≤ m ∧ m < start + n then cell[m - start]! else acc[m]! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [getElem!_set! _ _ _ _ (by rw [size_write_prefix]; exact hm), ih]
    by_cases he : start + n = m
    · rw [ite_eq_left he, ite_eq_left (by omega)]
      congr 1
      omega
    · rw [ite_eq_right he]
      by_cases hin : start ≤ m ∧ m < start + n
      · rw [ite_eq_left hin, ite_eq_left (by omega)]
      · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-- One exact cell write in the recovery flattening loop. -/
def writeRecoveryCell (acc : Array Fr) (ci : CellIndex) (cell : CosetEvals) : Array Fr :=
  (Array.range FIELD_ELEMENTS_PER_CELL).foldl
    (fun a j => a.set! (ci * FIELD_ELEMENTS_PER_CELL + j) cell[j]!) acc

@[simp] theorem size_writeRecoveryCell (acc : Array Fr) (ci : CellIndex) (cell : CosetEvals) :
    (writeRecoveryCell acc ci cell).size = acc.size := by
  unfold writeRecoveryCell
  rw [← Array.foldl_toList, Array.toList_range, size_write_prefix]

/-- The exact flattening write selects its cell's entry, leaving all other positions unchanged. -/
theorem getElem!_writeRecoveryCell (acc : Array Fr) (ci : CellIndex) (cell : CosetEvals)
    (m : Nat) (hm : m < acc.size) :
    (writeRecoveryCell acc ci cell)[m]! =
      if m / FIELD_ELEMENTS_PER_CELL = ci then cell[m % FIELD_ELEMENTS_PER_CELL]! else acc[m]! := by
  unfold writeRecoveryCell
  rw [← Array.foldl_toList, Array.toList_range, getElem!_write_prefix _ _ _ _ _ hm]
  have hc : FIELD_ELEMENTS_PER_CELL = 64 := rfl
  rw [hc]
  by_cases he : m / 64 = ci
  · rw [ite_eq_left he, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right he, ite_eq_right (by omega)]

private theorem size_flatten_prefix (indices : Array CellIndex) (cells : Array CosetEvals)
    (init : Array Fr) (n : Nat) :
    ((List.range n).foldl (fun a k => writeRecoveryCell a indices[k]! cells[k]!) init).size = init.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, size_writeRecoveryCell, ih]

/-- Lookup invariant for the actual outer recovery flattening loop. Consistent repeated
indices are harmless: every write to a location writes the same specified value. -/
theorem getElem!_flatten_prefix (indices : Array CellIndex) (cells : Array CosetEvals)
    (init : Array Fr) (f : Nat → Fr)
    (hvals : ∀ k < indices.size, ∀ j < FIELD_ELEMENTS_PER_CELL,
      (cells[k]!)[j]! = f (indices[k]! * FIELD_ELEMENTS_PER_CELL + j))
    (n : Nat) (hn : n ≤ indices.size) (m : Nat) (hm : m < init.size) :
    ((List.range n).foldl (fun a k => writeRecoveryCell a indices[k]! cells[k]!) init)[m]! =
      if ∃ k < n, indices[k]! = m / FIELD_ELEMENTS_PER_CELL then f m else init[m]! := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [getElem!_writeRecoveryCell _ _ _ m (by rw [size_flatten_prefix]; exact hm), ih (by omega)]
    by_cases he : m / FIELD_ELEMENTS_PER_CELL = indices[n]!
    · rw [ite_eq_left he, ite_eq_left ⟨n, by omega, he.symm⟩,
        hvals n (by omega) (m % FIELD_ELEMENTS_PER_CELL) (Nat.mod_lt _ (by decide)), ← he]
      congr 1
      rw [Nat.mul_comm]
      exact Nat.div_add_mod m FIELD_ELEMENTS_PER_CELL
    · rw [ite_eq_right he]
      have hex : (∃ k < n + 1, indices[k]! = m / FIELD_ELEMENTS_PER_CELL) ↔
          ∃ k < n, indices[k]! = m / FIELD_ELEMENTS_PER_CELL := by
        constructor
        · rintro ⟨k, hk, hv⟩
          refine ⟨k, ?_, hv⟩
          by_contra hk'
          have hkn : k = n := by omega
          subst hkn
          exact he hv.symm
        · rintro ⟨k, hk, hv⟩
          exact ⟨k, by omega, hv⟩
      by_cases hE : ∃ k < n, indices[k]! = m / FIELD_ELEMENTS_PER_CELL
      · rw [ite_eq_left hE, ite_eq_left (hex.mpr hE)]
      · rw [ite_eq_right hE, ite_eq_right (fun h => hE (hex.mp h))]

end EthLib.Cryptography.Kzg
