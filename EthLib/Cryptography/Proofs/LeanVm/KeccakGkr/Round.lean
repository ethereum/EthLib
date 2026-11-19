module

public import EthLib.Cryptography.LeanVm.KeccakGkr.Round

/-!
# Proofs: the round trips of the Keccak bit view

The source is [FIPS 202](https://doi.org/10.6028/NIST.FIPS.202), §3.1.2.

A state and its 25 lanes convert into each other without loss.

A state and its 1600 bits convert into each other without loss.

A shift by `k` columns along a row, then by `5 - k` more, is a full turn of the row.
-/

@[expose] public section

namespace EthLib.Cryptography.LeanVm.KeccakGkr

open EthLib.Cryptography.Hash

/-- Reading the lanes of a state and building a state from them gives the same state. -/
theorem stateOfLanes_stateLanes (A : Keccak.State) : stateOfLanes (stateLanes A) = A := by
  cases A
  rfl

/-- Building a state from 25 lanes and reading its lanes gives the same lanes. -/
theorem stateLanes_stateOfLanes (v : Vector UInt64 25) : stateLanes (stateOfLanes v) = v := by
  apply Vector.ext
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | _ + 25, h => exact absurd h (by omega)

/-- One step of the fold that builds a lane sets bit `z` when `p z` holds, and keeps the rest. -/
private theorem getLsbD_step (p : Fin 64 → Bool) (lane : UInt64) (z : Fin 64) (i : Nat) :
    (if p z then lane ||| (1 <<< z.val.toUInt64) else lane).toBitVec.getLsbD i =
      (lane.toBitVec.getLsbD i || (decide (z.val = i) && p z)) := by
  have hz := z.isLt
  by_cases hp : p z
  · simp only [hp, ↓reduceIte, Bool.and_true, UInt64.toBitVec_or, BitVec.getLsbD_or,
      UInt64.toBitVec_shiftLeft, Nat.toUInt64, UInt64.toBitVec_ofNat]
    by_cases hi : z.val = i
    · subst hi
      simp [Nat.mod_eq_of_lt hz, BitVec.toNat_ofNat]
    · simp only [hi, decide_false, Bool.or_false]
      cases lane.toBitVec.getLsbD i <;> simp <;> omega
  · simp [hp]

/-- The fold over a list of slices ORs in the set bits of exactly those slices. -/
private theorem getLsbD_foldl (p : Fin 64 → Bool) (l : List (Fin 64)) (lane : UInt64) (i : Nat) :
    (l.foldl (fun lane z => if p z then lane ||| (1 <<< z.val.toUInt64) else lane)
        lane).toBitVec.getLsbD i =
      (lane.toBitVec.getLsbD i || l.any fun z => decide (z.val = i) && p z) := by
  induction l generalizing lane with
  | nil => simp
  | cons z l ih => rw [List.foldl_cons, ih, getLsbD_step, List.any_cons, Bool.or_assoc]

/-- The lane that the fold of `ofBits` builds holds bit `p z` at slice `z`. -/
private theorem getLsbD_lane (p : Fin 64 → Bool) (z : Fin 64) :
    (Fin.foldl 64 (fun lane z => if p z then lane ||| (1 <<< z.val.toUInt64) else lane)
        0).toBitVec.getLsbD z.val = p z := by
  rw [Fin.foldl_eq_finRange_foldl, getLsbD_foldl]
  simp only [UInt64.toBitVec_zero, BitVec.getLsbD_zero, Bool.false_or]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, hp⟩
    rwa [Fin.ext hw] at hp
  · intro hp
    exact ⟨z, rfl, hp⟩

/-- Building a state from 1600 bits and reading its bits gives the same bits. -/
theorem bitsOf_ofBits (a : Pos → Bool) : bitsOf (ofBits a) = a := by
  funext j
  have hj := j.isLt
  simp only [bitsOf, ofBits, stateLanes_stateOfLanes, Vector.getElem_ofFn]
  have key := getLsbD_lane (fun z : Fin 64 => a ⟨z.val + 64 * (j.val / 64), by omega⟩)
    ⟨j.val % 64, by omega⟩
  refine key.trans (congrArg a (Fin.ext ?_))
  simp only
  omega

/-- Reading the bits of a state and building a state from them gives the same state. -/
theorem ofBits_bitsOf (A : Keccak.State) : ofBits (bitsOf A) = A := by
  have lanes : stateLanes (ofBits (bitsOf A)) = stateLanes A := by
    apply Vector.ext
    intro i hi
    simp only [ofBits, stateLanes_stateOfLanes, Vector.getElem_ofFn]
    apply UInt64.toBitVec_inj.1
    apply BitVec.eq_of_getLsbD_eq
    intro z hz
    rw [getLsbD_lane (fun z : Fin 64 => bitsOf A ⟨z.val + 64 * i, by omega⟩) ⟨z, hz⟩]
    simp only [bitsOf]
    have hdiv : (z + 64 * i) / 64 = i := by omega
    have hmod : (z + 64 * i) % 64 = z := by omega
    simp only [hdiv, hmod]
  rw [← stateOfLanes_stateLanes (ofBits (bitsOf A)), lanes, stateOfLanes_stateLanes]

/-- Shifting `k` columns along a row and then `5 - k` columns returns to the start.

`5 - k` is the subtraction of `Fin 5`. -/
theorem along_along_sub (j : Pos) (k : Fin 5) : along (along j k) (5 - k) = j := by
  have hj := j.isLt
  have hk := k.isLt
  have five : (5 : Fin 5).val = 0 := rfl
  have sub : (5 - k).val = (5 - k.val) % 5 := by
    rw [Fin.val_sub, five, Nat.add_zero]
  apply Fin.ext
  simp only [along, sub]
  omega

end EthLib.Cryptography.LeanVm.KeccakGkr
