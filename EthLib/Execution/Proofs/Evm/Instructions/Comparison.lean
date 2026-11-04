module

public import EthLib.Execution.Evm.Instructions.Comparison
public import EthLib.Base.Proofs.U256

/-!
# Proofs: `Evm.Instructions.Comparison`

The signed comparisons agree with the signed order on bit vectors of Lean.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base

/-- SLT is the signed order on bit vectors. -/
theorem signedLessThan_eq (left right : U256) :
    signedLessThan left right = if left.slt right then 1 else 0 := by
  simp only [signedLessThan, U256.toSigned_eq_toInt, BitVec.slt_iff_toInt_lt]

/-- SGT is the signed order on bit vectors, with the operands swapped. -/
theorem signedGreaterThan_eq (left right : U256) :
    signedGreaterThan left right = if right.slt left then 1 else 0 := by
  simp only [signedGreaterThan, U256.toSigned_eq_toInt, BitVec.slt_iff_toInt_lt, gt_iff_lt]

/-! ## Known answers -/

/-- -1 is below 0 as a signed word. -/
example : signedLessThan (BitVec.allOnes 256) 0 = 1 := by decide

/-- 2^256 - 1 is above 0 as an unsigned word. -/
example : lessThan (BitVec.allOnes 256) 0 = 0 := by decide

/-- -2^255 is the smallest signed word. -/
example : signedGreaterThan (BitVec.intMin 256) (BitVec.allOnes 256) = 0 := by decide

end EthLib.Execution.Evm.Instructions
