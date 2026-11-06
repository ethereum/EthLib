module

public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: a move of ether from an account to itself

A move of ether from an account that holds code to itself changes no account and no storage.

The account is not empty, so no step of the move deletes it.

CALLCODE moves ether in this way, from the account that runs to itself.
-/

@[expose] public section

namespace EthLib.Execution.State.TransactionState

open EthLib.Base

/-- The account at an address that holds code is not empty, so no change of it deletes it. -/
theorem accountExistsAndIsEmpty_setAccount_of_code {tx : TransactionState} {address : Address}
    {account : Account} (hcode : account.codeHash ≠ EMPTY_CODE_HASH) :
    (tx.setAccount address (some account)).accountExistsAndIsEmpty address = false := by
  simp [accountExistsAndIsEmpty, getAccountOptional_setAccount_self, hcode]

/-- A change that keeps the code of an account that holds code only sets the account. -/
theorem modifyState_eq_of_code {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      account.codeHash ≠ EMPTY_CODE_HASH) :
    ∃ account, f (tx.getAccount address) = .ok account ∧
      tx' = (tx.recordAccountRead address).setAccount address (some account) := by
  obtain ⟨account, hf, rfl⟩ := modifyState_eq_ok_iff.mp h
  refine ⟨account, hf, ?_⟩
  split
  · rename_i hc
    simp [accountExistsAndIsEmpty_setAccount_of_code (keeps account hf)] at hc
  · rfl

/-- A move of ether from an account that holds code to itself changes nothing. -/
theorem sameOutside_moveEther_self {fork : Fork}
    {tx tx' : TransactionState} {address : Address} {amount : U256}
    (hcode : (tx.getAccount address).codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.moveEther fork address address amount = .ok tx') : SameOutside [] tx tx' := by
  unfold moveEther at h
  cases h1 : tx.modifyState fork address (Account.debit address amount) with
  | error e => simp [h1, bind, Except.bind] at h
  | ok mid =>
    rw [h1] at h
    have debit : ∀ account, Account.debit address amount (tx.getAccount address) = .ok account →
        account.codeHash ≠ EMPTY_CODE_HASH := by
      intro account hf
      simp only [Account.debit] at hf
      split at hf
      · cases hf
      · cases hf; exact hcode
    obtain ⟨acc1, hf1, rfl⟩ := modifyState_eq_of_code h1 debit
    simp only [Account.debit] at hf1
    split at hf1
    · cases hf1
    · cases hf1
      have hget : ((tx.recordAccountRead address).setAccount address
          (some { tx.getAccount address with balance := (tx.getAccount address).balance - amount
            })).getAccount address =
          { tx.getAccount address with balance := (tx.getAccount address).balance - amount } := by
        simp [getAccount, getAccountOptional_setAccount_self]
      change modifyState fork _ address (Account.credit address amount) = .ok tx' at h
      have credit : ∀ account, Account.credit address amount
          (((tx.recordAccountRead address).setAccount address (some { tx.getAccount address with
            balance := (tx.getAccount address).balance - amount })).getAccount address) =
            .ok account → account.codeHash ≠ EMPTY_CODE_HASH := by
        intro account hf
        rw [hget] at hf
        simp only [Account.credit] at hf
        split at hf
        · cases hf; exact hcode
        · cases hf
      obtain ⟨acc2, hf2, rfl⟩ := modifyState_eq_of_code h credit
      rw [hget] at hf2
      simp only [Account.credit] at hf2
      split at hf2
      · cases hf2
        intro b _
        refine ⟨?_, fun _ => rfl, fun _ => rfl⟩
        by_cases hb : b = address
        · subst hb
          have hsome : tx.getAccountOptional b = some (tx.getAccount b) := by
            cases hx : tx.getAccountOptional b with
            | some account => simp [getAccount, hx]
            | none => exact absurd (by simp [getAccount, hx, EMPTY_ACCOUNT]) hcode
          rw [hsome, getAccountOptional_setAccount_self]
          congr 1
          cases hacc : tx.getAccount b
          simp [BitVec.sub_add_cancel]
        · simp [getAccountOptional_setAccount_of_ne _ _ hb]
      · cases hf2
end EthLib.Execution.State.TransactionState
