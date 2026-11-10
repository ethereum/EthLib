module

public import EthLib.Execution.Proofs.Blocks.WithdrawalCodec
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: withdrawals

After the withdrawals of a block, each account holds its balance plus the wei withdrawn to it.

Its nonce and its code stay the same.

The withdrawals of a block succeed exactly when no balance would reach `2^256`.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State

/-- The wei that a list of withdrawals gives an address: the sum of its amounts, times `10^9`. -/
def withdrawnTo (withdrawals : List Withdrawal) (address : Address) : Nat :=
  ((withdrawals.filter (·.address = address)).map (·.amount.toNat)).sum * GWEI_TO_WEI

/-- The amount of a withdrawal in wei is below `2^256`, since its amount in Gwei is below `2^64`. -/
theorem toNat_withdrawalWei (amount : UInt64) :
    (BitVec.ofNat 256 (amount.toNat * GWEI_TO_WEI)).toNat = amount.toNat * GWEI_TO_WEI := by
  have hlt : amount.toNat * GWEI_TO_WEI < 2 ^ 64 * GWEI_TO_WEI :=
    Nat.mul_lt_mul_of_pos_right amount.toNat_lt (by decide)
  have hle : 2 ^ 64 * GWEI_TO_WEI ≤ 2 ^ 256 := by decide
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hle)]

/-- The wei of a list with one more withdrawal in front. -/
theorem withdrawnTo_cons (w : Withdrawal) (rest : List Withdrawal) (address : Address) :
    withdrawnTo (w :: rest) address =
      (if w.address = address then w.amount.toNat * GWEI_TO_WEI else 0) +
        withdrawnTo rest address := by
  by_cases hsame : w.address = address <;>
    simp [withdrawnTo, hsame, Nat.add_mul]

/-- The wei that the withdrawals give an address is the sum of the wei of each withdrawal. -/
private theorem withdrawnTo_eq_sum (withdrawals : List Withdrawal) (address : Address) :
    withdrawnTo withdrawals address =
      ((withdrawals.filter (·.address = address)).map
        fun w => (BitVec.ofNat 256 (w.amount.toNat * GWEI_TO_WEI)).toNat).sum := by
  induction withdrawals with
  | nil => simp [withdrawnTo]
  | cons w rest ih =>
    rw [withdrawnTo_cons, ih]
    by_cases hsame : w.address = address
    · simp only [hsame, ↓reduceIte, List.filter_cons, decide_true, List.map_cons, List.sum_cons,
        toNat_withdrawalWei]
    · simp [hsame]

/-- After the withdrawals of a block, each account holds its balance plus its withdrawn wei.

Its nonce and its code hash stay the same, and an address with no withdrawal keeps its balance. -/
theorem getAccount_processWithdrawals {fork : Fork} {block block' : BlockState}
    {withdrawals : List Withdrawal} (h : processWithdrawals fork block withdrawals = .ok block')
    (address : Address) :
    ((TransactionState.ofBlock block').getAccount address).balance.toNat =
        ((TransactionState.ofBlock block).getAccount address).balance.toNat +
          withdrawnTo withdrawals address ∧
      ((TransactionState.ofBlock block').getAccount address).nonce =
        ((TransactionState.ofBlock block).getAccount address).nonce ∧
      ((TransactionState.ofBlock block').getAccount address).codeHash =
        ((TransactionState.ofBlock block).getAccount address).codeHash := by
  simp only [processWithdrawals, withdrawalState, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i tx htx
    cases h
    -- The block after the withdrawals reads its accounts as the last step does.
    have hread : (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getAccount address =
        tx.getAccount address := by
      unfold TransactionState.getAccount
      rw [← TransactionState.getAccountOptional_incorporateTxIntoBlock tx address]
      rfl
    rw [hread, withdrawnTo_eq_sum]
    exact TransactionState.getAccount_foldlM_createEther _ _ withdrawals htx address

/-- The withdrawals of a block succeed exactly when each balance stays below `2^256`.

The balance of an address counts every wei that the withdrawals give it. -/
theorem processWithdrawals_isOk_iff {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} :
    (∃ block', processWithdrawals fork block withdrawals = .ok block') ↔
      ∀ address, ((TransactionState.ofBlock block).getAccount address).balance.toNat +
        withdrawnTo withdrawals address < 2 ^ 256 := by
  simp only [withdrawnTo_eq_sum]
  rw [← TransactionState.foldlM_createEther_isOk_iff (fork := fork) (·.address)
    (fun w => BitVec.ofNat 256 (w.amount.toNat * GWEI_TO_WEI)) withdrawals]
  simp only [processWithdrawals, withdrawalState, bind, Except.bind, pure, Except.pure]
  split <;> simp_all

end EthLib.Execution.Blocks
