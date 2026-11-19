module

public import EthLib.Cryptography.Multilinear.Hypercube

/-!
# Proofs: the hypercube index order

The index of a point and the point of an index are inverse, for every dimension `k`.

The index of `u ++ v` is the index of `u` plus `2^j` times the index of `v`, for `u` of length `j`.

A point of one coordinate has the index `1` when the coordinate is true, and `0` otherwise.
-/

@[expose] public section

namespace EthLib.Cryptography.Multilinear

/-- The integer of a list of bits, the first bit the low bit. -/
private def bitsValue : List Bool → Nat
  | [] => 0
  | b :: l => b.toNat + 2 * bitsValue l

private theorem bitsValue_append (l1 l2 : List Bool) :
    bitsValue (l1 ++ l2) = bitsValue l1 + 2 ^ l1.length * bitsValue l2 := by
  induction l1 with
  | nil => simp [bitsValue]
  | cons b l ih =>
    simp only [List.cons_append, bitsValue, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ l.length), Nat.add_assoc]

private theorem toList_eq_cons {k : Nat} (u : Vector Bool (k + 1)) :
    u.toList = u[0] :: u.tail.toList := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    cases n with
    | zero => simp
    | succ n => simp [Nat.add_comm 1 n]

private theorem pointIndex_val_eq_bitsValue {k : Nat} (u : Vector Bool k) :
    (pointIndex u).val = bitsValue u.toList := by
  induction k with
  | zero =>
    rw [List.eq_nil_of_length_eq_zero (by simp : u.toList.length = 0)]
    rfl
  | succ k ih =>
    rw [toList_eq_cons, bitsValue, ← ih]
    rfl

private theorem pointIndex_zero_val (u : Vector Bool 0) : (pointIndex u).val = 0 := rfl

private theorem pointIndex_succ_val {k : Nat} (u : Vector Bool (k + 1)) :
    (pointIndex u).val = u[0].toNat + 2 * (pointIndex (k := k) u.tail).val := rfl

/-- The index of a point of one coordinate is `1` when the coordinate is true, and `0` otherwise. -/
theorem pointIndex_singleton (b : Bool) : (pointIndex #v[b]).val = b.toNat := by
  rw [pointIndex_succ_val, pointIndex_zero_val]
  simp

/-- The index of `u ++ v` is the index of `u` plus `2^j` times the index of `v`.

It holds for any lengths `j` of `u` and `m` of `v`. -/
theorem pointIndex_append {j m : Nat} (u : Vector Bool j) (v : Vector Bool m) :
    (pointIndex (u ++ v)).val = (pointIndex u).val + 2 ^ j * (pointIndex v).val := by
  simp only [pointIndex_val_eq_bitsValue, Vector.toList_append, bitsValue_append,
    Vector.length_toList]

/-- The point of the index of a point is that point. -/
theorem indexPoint_pointIndex {k : Nat} (u : Vector Bool k) : indexPoint (pointIndex u) = u := by
  induction k with
  | zero => exact Vector.ext fun i h => absurd h (Nat.not_lt_zero i)
  | succ k ih =>
    apply Vector.ext
    intro i hi
    simp only [indexPoint, Vector.getElem_ofFn, pointIndex_succ_val]
    have hb := Bool.toNat_le u[0]
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      cases u[0] <;> simp
    | succ i =>
      rw [Nat.testBit_succ]
      have hdiv : (u[0].toNat + 2 * (pointIndex (k := k) u.tail).val) / 2
          = (pointIndex (k := k) u.tail).val := by omega
      rw [hdiv]
      have := congrArg (fun w => w[i]'(by omega)) (ih u.tail)
      simpa [indexPoint, Vector.getElem_ofFn, Nat.add_comm 1 i] using this

/-- The index of the point of an index is that index. -/
theorem pointIndex_indexPoint {k : Nat} (i : Fin (2 ^ k)) : pointIndex (indexPoint i) = i := by
  induction k with
  | zero =>
    have hi : i.val < 1 := i.isLt
    exact Fin.ext (by rw [pointIndex_zero_val]; omega)
  | succ k ih =>
    apply Fin.ext
    have hhalf : i.val / 2 < 2 ^ k := by
      have hi := i.isLt
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      omega
    have htail : (indexPoint i).tail = indexPoint (k := k) ⟨i.val / 2, hhalf⟩ := by
      apply Vector.ext
      intro j hj
      simp [indexPoint, Vector.getElem_ofFn, Nat.add_comm 1 j, Nat.testBit_succ]
    rw [pointIndex_succ_val, htail, ih]
    simp only [indexPoint, Vector.getElem_ofFn, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h <;> simp [h] <;> omega

end EthLib.Cryptography.Multilinear
