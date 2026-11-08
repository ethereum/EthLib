module

/-!
# `Base.Proofs.BitVec`

Facts about rotations of a bit vector that Lean core does not prove and that several hashes use.

A rotation by `n`, then by the width minus `n`, gives the vector back.
-/

@[expose] public section

namespace EthLib.Base

/-- Rotating left by `n`, then by `w - n`, gives the vector back, for `n < w`. -/
theorem rotateLeft_rotateLeft_sub {w n : Nat} (x : BitVec w) (hw : n < w) :
    (x.rotateLeft n).rotateLeft (w - n) = x := by
  -- A rotation by 0 and then by `w` moves no bit.
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
    simp [Nat.mod_self, hi]
  refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
  simp only [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt (by omega : w - n < w),
    Nat.mod_eq_of_lt hw, hi, decide_true, Bool.true_and]
  rw [show w - (w - n) = n by omega]
  by_cases hlt : i < w - n
  · have hlt2 : n + i < w := by omega
    have hge2 : ¬ (n + i < n) := by omega
    simp [hlt, hlt2, hge2, show n + i - n = i by omega]
  · have hlt3 : i - (w - n) < n := by omega
    simp [hlt, hlt3, show w - n + (i - (w - n)) = i by omega]

/-- Rotating right by `n`, then by `w - n`, gives the vector back, for `n < w`. -/
theorem rotateRight_rotateRight_sub {w n : Nat} (x : BitVec w) (hw : n < w) :
    (x.rotateRight n).rotateRight (w - n) = x := by
  -- A rotation by 0 and then by `w` moves no bit.
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
    simp [Nat.mod_self, hi]
  refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
  simp only [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt (by omega : w - n < w),
    Nat.mod_eq_of_lt hw, hi, decide_true, Bool.true_and]
  rw [show w - (w - n) = n by omega]
  by_cases hlt : i < n
  · have hlt2 : w - n + i < w := by omega
    have hge2 : ¬ (w - n + i < w - n) := by omega
    simp [hlt, hlt2, hge2, show w - n + i - (w - n) = i by omega]
  · have hlt3 : i - n < w - n := by omega
    simp [hlt, hlt3, show n + (i - n) = i by omega]

end EthLib.Base
