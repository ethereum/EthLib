module

public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: code availability under changes of state

Code is available when lookup succeeds at the code hash of every current account.

Pre-transaction availability asks the same of each account in the parent block view.

Any account change keeps pre-transaction availability.

It keeps current availability when it keeps or clears the account's code hash.

Writing code keeps them too, since it stores code under the hash that the account receives.

Storage writes, touches and moves of ether keep every code hash, so they keep both.

A rollback to a snapshot of the same parent restores the snapshot's availability.

Incorporation starts a new transaction, whose pre-transaction accounts are the old current ones.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Bytes32 Fork Hash32 U256)
open EthLib.Execution.State (Account EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.State.TransactionState

/-- Whether the state holds the code of every account. -/
def HasCodes (state : TransactionState) : Prop :=
  ∀ address, ∃ code, state.getCode (state.getAccount address).codeHash = .ok code

/-- Whether the state holds the code of every account before the transaction. -/
def HasPreCodes (state : TransactionState) : Prop :=
  ∀ address, ∃ code, state.getCode (state.getPreStateAccount address).codeHash = .ok code

/-- Keeping every code and keeping or clearing each code hash keeps every current code available. -/
theorem hasCodes_of_getCode {state state' : TransactionState}
    (code : ∀ hash, state'.getCode hash = state.getCode hash)
    (hash : ∀ address, (state'.getAccount address).codeHash = (state.getAccount address).codeHash ∨
      (state'.getAccount address).codeHash = EMPTY_CODE_HASH)
    (available : HasCodes state) : HasCodes state' := by
  intro address
  rw [code]
  rcases hash address with same | empty
  · rw [same]
    exact available address
  · exact ⟨.empty, by simp [getCode, empty]⟩

/-- Keeping the block and every code keeps the code of every pre-transaction account available. -/
theorem hasPreCodes_of_getCode {state state' : TransactionState}
    (code : ∀ hash, state'.getCode hash = state.getCode hash)
    (parent : state'.parent = state.parent) (available : HasPreCodes state) :
    HasPreCodes state' := by
  intro address
  have account : state'.getPreStateAccount address = state.getPreStateAccount address := by
    simp only [getPreStateAccount, getPreStateAccountOptional, parent]
  rw [account, code]
  exact available address

/-- A wipe of the storage of an address keeps the code of every current account available. -/
theorem hasCodes_destroyStorage {state : TransactionState} (address : Address)
    (available : HasCodes state) : HasCodes (state.destroyStorage address) :=
  hasCodes_of_getCode (state := state) (state' := state.destroyStorage address) (fun _ => rfl)
    (fun _ => .inl rfl) available

/-- A wipe of storage keeps the code of every pre-transaction account available. -/
theorem hasPreCodes_destroyStorage {state : TransactionState} (address : Address)
    (available : HasPreCodes state) : HasPreCodes (state.destroyStorage address) :=
  hasPreCodes_of_getCode (fun _ => rfl) rfl available

/-- A deletion of an account keeps the code of every current account available.

The deleted account reads as the empty account, whose code is empty. -/
theorem hasCodes_destroyAccount {state : TransactionState} (address : Address)
    (available : HasCodes state) : HasCodes (state.destroyAccount address) := by
  refine hasCodes_of_getCode (state := state) (state' := state.destroyAccount address)
    (fun _ => rfl) (fun other => ?_) available
  rw [getAccount_destroyAccount]
  split
  · exact .inr rfl
  · exact .inl rfl

/-- A deletion of an account keeps the code of every pre-transaction account available. -/
theorem hasPreCodes_destroyAccount {state : TransactionState} (address : Address)
    (available : HasPreCodes state) : HasPreCodes (state.destroyAccount address) :=
  hasPreCodes_of_getCode (fun _ => rfl) rfl available

/-- A touch of an account keeps the code of every current account available. -/
theorem hasCodes_touchAccount {state : TransactionState} (address : Address)
    (available : HasCodes state) : HasCodes (state.touchAccount address) := by
  refine hasCodes_of_getCode (getCode_touchAccount state address) (fun other => .inl ?_) available
  by_cases here : other = address
  · rw [here, getAccount_touchAccount_self]
  · rw [getAccount_touchAccount here]

/-- A touch of an account keeps the code of every pre-transaction account available. -/
theorem hasPreCodes_touchAccount {state : TransactionState} (address : Address)
    (available : HasPreCodes state) : HasPreCodes (state.touchAccount address) :=
  hasPreCodes_of_getCode (getCode_touchAccount state address) (parent_touchAccount state address)
    available

/-- A storage write keeps the code of every current account available. -/
theorem hasCodes_setStorage {state state' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : state.setStorage address key value = .ok state')
    (available : HasCodes state) : HasCodes state' :=
  hasCodes_of_getCode (getCode_setStorage h)
    (fun _ => .inl (by unfold getAccount; rw [getAccountOptional_setStorage h])) available

/-- A storage write keeps the code of every pre-transaction account available. -/
theorem hasPreCodes_setStorage {state state' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : state.setStorage address key value = .ok state')
    (available : HasPreCodes state) : HasPreCodes state' :=
  hasPreCodes_of_getCode (getCode_setStorage h) (parent_setStorage h) available

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

/-- A debit of an account keeps its code hash. -/
private theorem codeHash_debit {address : Address} {amount : U256} {account account' : Account}
    (h : account.debit address amount = .ok account') : account'.codeHash = account.codeHash := by
  unfold Account.debit at h
  split at h <;> cases h
  rfl

/-- A credit of an account keeps its code hash. -/
private theorem codeHash_credit {address : Address} {amount : U256} {account account' : Account}
    (h : account.credit address amount = .ok account') : account'.codeHash = account.codeHash := by
  unfold Account.credit at h
  split at h <;> cases h
  rfl

/-- A move of ether keeps the code of every current account available. -/
theorem hasCodes_moveEther {fork : Fork} {state state' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : state.moveEther fork sender recipient amount = .ok state') (available : HasCodes state) :
    HasCodes state' := by
  unfold moveEther at h
  cases debited : state.modifyState fork sender (Account.debit sender amount) with
  | error e => simp [debited, bind, Except.bind] at h
  | ok mid =>
  simp only [debited, bind, Except.bind] at h
  exact hasCodes_modifyState h
    (hasCodes_modifyState debited available fun _ hf => .inl (codeHash_debit hf))
    fun _ hf => .inl (codeHash_credit hf)

/-- A move of ether keeps the code of every pre-transaction account available. -/
theorem hasPreCodes_moveEther {fork : Fork} {state state' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : state.moveEther fork sender recipient amount = .ok state')
    (available : HasPreCodes state) : HasPreCodes state' := by
  unfold moveEther at h
  cases debited : state.modifyState fork sender (Account.debit sender amount) with
  | error e => simp [debited, bind, Except.bind] at h
  | ok mid =>
  simp only [debited, bind, Except.bind] at h
  exact hasPreCodes_modifyState h (hasPreCodes_modifyState debited available)

/-- New ether at an address keeps the code of every current account available. -/
theorem hasCodes_createEther {fork : Fork} {state state' : TransactionState} {address : Address}
    {amount : U256} (h : state.createEther fork address amount = .ok state')
    (available : HasCodes state) : HasCodes state' :=
  hasCodes_modifyState h available fun _ hf => .inl (codeHash_credit hf)

/-- A new balance keeps the code of every current account available. -/
theorem hasCodes_setAccountBalance {fork : Fork} {state state' : TransactionState}
    {address : Address} {amount : U256}
    (h : state.setAccountBalance fork address amount = .ok state') (available : HasCodes state) :
    HasCodes state' :=
  hasCodes_modifyState h available fun _ hf => .inl (by cases hf; rfl)

/-- A rise of a nonce keeps the code of every current account available. -/
theorem hasCodes_incrementNonce {fork : Fork} {state state' : TransactionState}
    {address : Address} (h : state.incrementNonce fork address = .ok state')
    (available : HasCodes state) : HasCodes state' :=
  hasCodes_modifyState h available fun _ hf => .inl (by cases hf; rfl)

/-- A clear of an account that keeps its balance keeps the code of every current account available.

It wipes the storage and empties the code. -/
theorem hasCodes_clearAccountPreservingBalance {fork : Fork} {state state' : TransactionState}
    {address : Address} (h : state.clearAccountPreservingBalance fork address = .ok state')
    (available : HasCodes state) : HasCodes state' :=
  hasCodes_modifyState h (hasCodes_destroyStorage address available)
    fun _ hf => .inr (by cases hf; rfl)

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

/-- Rolling back to a snapshot of the same parent restores the snapshot's code availability. -/
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

/-- If every account has its code, every pre-transaction account has it after incorporation. -/
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
