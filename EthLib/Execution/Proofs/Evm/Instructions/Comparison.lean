module

public import EthLib.Execution.Evm.Instructions.Comparison
public import EthLib.Base.Proofs.U256

/-!
# Proofs: `Evm.Instructions.Comparison`

The comparisons agree with the orders on bit vectors of Lean.

- LT and GT push 1 exactly when the unsigned order holds.
- EQ and ISZERO push 1 exactly when their test holds.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- LT is the unsigned order on bit vectors. -/
theorem lessThan_eq (left right : U256) :
    lessThan left right = if left.ult right then 1 else 0 := by
  simp only [lessThan, BitVec.ult, decide_eq_true_eq]

/-- GT is the unsigned order on bit vectors, with the operands swapped. -/
theorem greaterThan_eq (left right : U256) :
    greaterThan left right = if right.ult left then 1 else 0 := by
  simp only [greaterThan, BitVec.ult, gt_iff_lt, decide_eq_true_eq]

/-- EQ pushes 1 exactly when the operands are equal. -/
theorem equal_eq_one_iff (left right : U256) : equal left right = 1 ↔ left = right := by
  unfold equal
  split <;> simp_all

/-- ISZERO pushes 1 exactly when the operand is 0. -/
theorem isZero_eq_one_iff (x : U256) : isZero x = 1 ↔ x = 0 := by
  unfold isZero
  split <;> simp_all

/-- SLT is the signed order on bit vectors. -/
theorem signedLessThan_eq (left right : U256) :
    signedLessThan left right = if left.slt right then 1 else 0 := by
  simp only [signedLessThan, U256.toSigned_eq_toInt, BitVec.slt_iff_toInt_lt]

/-- SGT is the signed order on bit vectors, with the operands swapped. -/
theorem signedGreaterThan_eq (left right : U256) :
    signedGreaterThan left right = if right.slt left then 1 else 0 := by
  simp only [signedGreaterThan, U256.toSigned_eq_toInt, BitVec.slt_iff_toInt_lt, gt_iff_lt]

end EthLib.Execution.Evm
