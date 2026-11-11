module

public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: code availability under changes of state

`HasCodes` requires code lookup to succeed for every current account.

`HasPreCodes` uses each account in the parent block view, before the transaction.

A change that keeps or clears an account's code hash keeps both properties.

Writing code keeps them too, since it stores code under the hash that the account receives.

A rollback to a snapshot of the same parent restores the snapshot's availability.

Incorporation starts a new transaction, whose pre-transaction accounts are the old current ones.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork Hash32)
open EthLib.Execution.State (Account EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.State.TransactionState

/-- Whether the state holds the code of every account. -/
def HasCodes (state : TransactionState) : Prop :=
  ∀ address, ∃ code, state.getCode (state.getAccount address).codeHash = .ok code

/-- Whether the state holds the code of every account before the transaction. -/
def HasPreCodes (state : TransactionState) : Prop :=
  ∀ address, ∃ code, state.getCode (state.getPreStateAccount address).codeHash = .ok code

/-- Writing code preserves successful lookup at every code hash. -/
theorem exists_getCode_setCode {fork : Fork} {state state' : TransactionState}
    {address : Address} {code : ByteArray} (h : state.setCode fork address code = .ok state')
    {hash : Hash32} (available : ∃ old, state.getCode hash = .ok old) :
    ∃ stored, state'.getCode hash = .ok stored := by
  obtain ⟨old, read⟩ := available
  by_cases changed : hash = Cryptography.Hash.Keccak.keccak256 code
  · by_cases empty : hash = EMPTY_CODE_HASH
    · exact ⟨.empty, by simp [getCode, empty]⟩
    · subst changed
      exact ⟨code, getCode_setCode_self h empty⟩
  · exact ⟨old, (getCode_setCode_of_ne h changed).trans read⟩

/-- A change that keeps or clears the code hash keeps the code of every account available. -/
theorem hasCodes_modifyState {fork : Fork} {state state' : TransactionState} {address : Address}
    {f : Account → Except State.StateError Account}
    (h : state.modifyState fork address f = .ok state') (available : HasCodes state)
    (hash : ∀ account, f (state.getAccount address) = .ok account →
      account.codeHash = (state.getAccount address).codeHash ∨
        account.codeHash = EMPTY_CODE_HASH) : HasCodes state' := by
  obtain ⟨account, changed, atAddress, elsewhere⟩ := modifyState_eq_ok h
  intro other
  rw [getCode_modifyState h]
  by_cases here : other = address
  · subst other
    rw [atAddress]
    rcases hash account changed with same | empty
    · rw [same]
      exact available address
    · exact ⟨.empty, by simp [getCode, empty]⟩
  · rw [elsewhere other here]
    exact available other

/-- An account change keeps availability for every pre-transaction account. -/
theorem hasPreCodes_modifyState {fork : Fork} {state state' : TransactionState}
    {address : Address} {f : Account → Except State.StateError Account}
    (h : state.modifyState fork address f = .ok state') (available : HasPreCodes state) :
    HasPreCodes state' := by
  intro other
  have account : state'.getPreStateAccount other = state.getPreStateAccount other := by
    simp only [getPreStateAccount, getPreStateAccountOptional, parent_modifyState h]
  rw [account, getCode_modifyState h]
  exact available other

/-- Writing code keeps the code of every current account available. -/
theorem hasCodes_setCode {fork : Fork} {state state' : TransactionState} {address : Address}
    {code : ByteArray} (h : state.setCode fork address code = .ok state')
    (available : HasCodes state) : HasCodes state' := by
  intro other
  by_cases here : other = address
  · subst other
    rw [(getAccount_setCode h).1]
    by_cases empty : Cryptography.Hash.Keccak.keccak256 code = EMPTY_CODE_HASH
    · exact ⟨.empty, by simp [getCode, empty]⟩
    · exact ⟨code, getCode_setCode_self h empty⟩
  · have account : state'.getAccount other = state.getAccount other := by
      unfold getAccount
      rw [(getAccount_setCode h).2 other here]
    rw [account]
    exact exists_getCode_setCode h (available other)

/-- Writing code keeps the code of every pre-transaction account available. -/
theorem hasPreCodes_setCode {fork : Fork} {state state' : TransactionState} {address : Address}
    {code : ByteArray} (h : state.setCode fork address code = .ok state')
    (available : HasPreCodes state) : HasPreCodes state' := by
  intro other
  have account : state'.getPreStateAccount other = state.getPreStateAccount other := by
    simp only [getPreStateAccount, getPreStateAccountOptional, parent_setCode h]
  rw [account]
  exact exists_getCode_setCode h (available other)

/-- Rolling back to a snapshot of the same parent restores its current code availability. -/
theorem hasCodes_restoreTxState {state snapshot : TransactionState}
    (parent : state.parent = snapshot.parent) (available : HasCodes snapshot) :
    HasCodes (state.restoreTxState snapshot) := by
  intro address
  rw [getCode_restoreTxState parent]
  simpa only [getAccount, getAccountOptional_restoreTxState parent] using available address

/-- Rolling back to a snapshot of the same parent restores its pre-transaction availability. -/
theorem hasPreCodes_restoreTxState {state snapshot : TransactionState}
    (parent : state.parent = snapshot.parent) (available : HasPreCodes snapshot) :
    HasPreCodes (state.restoreTxState snapshot) := by
  intro address
  have account : (state.restoreTxState snapshot).getPreStateAccount address =
      snapshot.getPreStateAccount address := by
    simp only [getPreStateAccount, getPreStateAccountOptional, restoreTxState, parent]
  rw [account, getCode_restoreTxState parent]
  exact available address

/-- Incorporation keeps the code of every account in the new transaction available. -/
theorem hasCodes_incorporateTxIntoBlock {state : TransactionState} (available : HasCodes state) :
    HasCodes state.incorporateTxIntoBlock := by
  intro address
  have account : state.incorporateTxIntoBlock.getAccount address = state.getAccount address := by
    unfold getAccount
    rw [getAccountOptional_incorporateTxIntoBlock]
  rw [account, getCode_incorporateTxIntoBlock]
  exact available address

/-- After incorporation, pre-transaction availability follows from the old current accounts. -/
theorem hasPreCodes_incorporateTxIntoBlock {state : TransactionState}
    (available : HasCodes state) : HasPreCodes state.incorporateTxIntoBlock := by
  intro address
  have account : state.incorporateTxIntoBlock.getPreStateAccount address =
      state.incorporateTxIntoBlock.getAccount address := by
    simp only [incorporateTxIntoBlock, ofBlock, getPreStateAccount, getPreStateAccountOptional,
      getAccount, getAccountOptional, Std.ExtTreeMap.getElem?_empty]
  rw [account]
  exact hasCodes_incorporateTxIntoBlock available address

end EthLib.Execution.Transactions
