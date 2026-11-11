module

public import EthLib.Execution.Proofs.Blocks.AccessListFollow
public import EthLib.Execution.Proofs.Blocks.WithdrawalCodec
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: withdrawals

After the withdrawals of a block, each account holds its balance plus the wei withdrawn to it.

Its nonce and its code stay the same.

The withdrawals of a block succeed exactly when no balance would reach `2^256`.

`RebuildInvariant` requires returned code to match its hash.

It requires empty or missing accounts to hold only zero storage.

Withdrawals preserve it and give `Followable`, the access-list builder's conditions on one call.
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
    rw [TransactionState.getAccount_ofBlock_incorporateTxIntoBlock, withdrawnTo_eq_sum]
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

/-! ## Following the withdrawals in an access list -/

/-- Returned code matches its hash, and an empty or missing account has only zero storage.

An account with only a nonzero balance may hold storage. -/
structure RebuildInvariant (tx : TransactionState) : Prop where
  /-- Each returned code has the hash under which it is read. -/
  code : ∀ hash code, tx.getCode hash = .ok code →
    Cryptography.Hash.Keccak.keccak256 code = hash
  /-- Empty and missing accounts hold no nonzero storage word. -/
  storage : ∀ address, tx.getAccount address = EMPTY_ACCOUNT →
    ∀ key, tx.getStorage address key = 0

/-- Adding ether cannot make a nonempty account empty. -/
private theorem getAccount_eq_empty_of_createEther {fork : Fork} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (h : tx.createEther fork target amount = .ok tx')
    (address : Address) (empty : tx'.getAccount address = EMPTY_ACCOUNT) :
    tx.getAccount address = EMPTY_ACCOUNT := by
  obtain ⟨balance, nonce, code⟩ := TransactionState.getAccount_createEther h address
  cases old : tx.getAccount address with
  | mk n b c =>
    simp only [old, empty, EMPTY_ACCOUNT] at balance nonce code ⊢
    change 0 = b.toNat + _ at balance
    have zero : b = 0 := by
      apply BitVec.eq_of_toNat_eq
      change b.toNat = 0
      omega
    subst n
    subst c
    subst b
    rfl

/-- Adding ether preserves every storage word when empty accounts have no storage. -/
private theorem getStorage_createEther {fork : Fork} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (h : tx.createEther fork target amount = .ok tx')
    (valid : RebuildInvariant tx) (address : Address) (key : Bytes32) :
    tx'.getStorage address key = tx.getStorage address key := by
  rw [TransactionState.getStorage_modifyState h]
  split
  · rename_i deleted
    have empty : tx'.getAccount address = EMPTY_ACCOUNT := by
      simp only [TransactionState.getAccount, deleted.1, deleted.2, Option.getD_none]
    exact (valid.storage address (getAccount_eq_empty_of_createEther h address empty) key).symm
  · rfl

/-- Adding ether preserves the conditions for rebuilding from an access list. -/
private theorem RebuildInvariant.createEther {fork : Fork} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (valid : RebuildInvariant tx)
    (h : tx.createEther fork target amount = .ok tx') : RebuildInvariant tx' := by
  refine ⟨?_, ?_⟩
  · intro hash code read
    rw [TransactionState.getCode_modifyState h] at read
    exact valid.code hash code read
  · intro address empty key
    rw [getStorage_createEther h valid]
    exact valid.storage address (getAccount_eq_empty_of_createEther h address empty) key

/-- Incorporating a transaction preserves the conditions for rebuilding from its reads. -/
private theorem RebuildInvariant.incorporate {tx : TransactionState} (valid : RebuildInvariant tx) :
    RebuildInvariant (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent) := by
  refine ⟨?_, ?_⟩
  · intro hash code read
    change tx.incorporateTxIntoBlock.getCode hash = .ok code at read
    rw [TransactionState.getCode_incorporateTxIntoBlock] at read
    exact valid.code hash code read
  · intro address empty key
    rw [TransactionState.getAccount_ofBlock_incorporateTxIntoBlock] at empty
    change tx.incorporateTxIntoBlock.getStorage address key = 0
    rw [TransactionState.getStorage_incorporateTxIntoBlock]
    exact valid.storage address empty key

/-- Withdrawals are followed by the access-list builder and preserve the rebuilding conditions.

This includes zero withdrawals that delete an empty account: its storage was already zero. -/
theorem withdrawalState_followable {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} {tx : TransactionState}
    (valid : RebuildInvariant (TransactionState.ofBlock block))
    (h : withdrawalState fork block withdrawals = .ok tx) :
    Followable block tx ∧
      RebuildInvariant (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent) := by
  have invariant : tx.parent = block ∧ RebuildInvariant tx ∧
      ∀ address key, tx.getStorage address key =
        (TransactionState.ofBlock block).getStorage address key := by
    apply foldlM_ok_invariant
      (fun tx => tx.parent = block ∧ RebuildInvariant tx ∧
        ∀ address key, tx.getStorage address key =
          (TransactionState.ofBlock block).getStorage address key) ?_
      ⟨rfl, valid, fun _ _ => rfl⟩ h
    intro before w after previous step
    have parent : after.parent = before.parent := by
      obtain ⟨_, _, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp step
      split <;> rfl
    exact ⟨parent.trans previous.1, previous.2.1.createEther step,
      fun address key => (getStorage_createEther step previous.2.1 address key).trans
        (previous.2.2 address key)⟩
  refine ⟨⟨invariant.1, fun address key _ => invariant.2.2 address key, ?_⟩,
    invariant.2.1.incorporate⟩
  intro address written code _ read
  exact invariant.2.1.code _ code read

end EthLib.Execution.Blocks
