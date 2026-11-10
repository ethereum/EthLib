module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.List
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: the supply of ether in the state of a transaction

The supply of a state is the sum of the balances of all its accounts, in wei.

An address with no account counts as the empty account, whose balance is 0.

So the sum can run over any list of distinct addresses that holds every nonzero balance.

A write that changes one balance changes the supply by the same amount.

A move of ether keeps the supply, and a creation of ether adds its amount.

The deletion of an account removes its balance from the supply.

A write of a nonce, a code or a word of storage keeps the supply.

So do a record of a read or of a created account, a write of transient storage and a touch.

So do a wipe of storage, and taking the reads of another state.

So do the clear of an account that keeps its balance, and the deletion of empty touched accounts.

A rollback gives back the supply of its snapshot, and the end of a transaction keeps the supply.

The supply of the state after a block is the sum of the balances of its accounts.

It is the supply of the block state, read as a transaction.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base

/-! ## The balance of one account -/

/-- A debit takes its amount from the balance, which holds it. -/
theorem Account.toNat_balance_debit {address : Address} {amount : U256}
    {account account' : Account} (h : Account.debit address amount account = .ok account') :
    account'.balance.toNat + amount.toNat = account.balance.toNat := by
  unfold Account.debit at h
  split at h
  · cases h
  · rename_i hfunds
    cases h
    have hle : amount.toNat ≤ account.balance.toNat := by simpa [BitVec.lt_def] using hfunds
    simp only [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
    omega

/-- A credit adds its amount to the balance. -/
theorem Account.toNat_balance_credit {address : Address} {amount : U256}
    {account account' : Account} (h : Account.credit address amount account = .ok account') :
    account'.balance.toNat = account.balance.toNat + amount.toNat := by
  unfold Account.credit at h
  split at h
  · rename_i hfit
    cases h
    simp only [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
  · cases h

namespace TransactionState

/-! ## The supply -/

/-- The addresses that may hold an account in a transaction state, each once.

They are those of the state before the block, and those that the block or the transaction wrote. -/
def addresses (tx : TransactionState) : List Address :=
  (tx.parent.preState.accounts.keys ++ tx.parent.accountWrites.keys ++
    tx.accountWrites.keys).eraseDups

/-- The balance of the account at an address, in wei, or 0 for an address with no account. -/
def balanceOf (tx : TransactionState) (address : Address) : Nat :=
  (tx.getAccount address).balance.toNat

/-- The supply of ether in a transaction state: the sum of the balances of its accounts, in wei. -/
def supply (tx : TransactionState) : Nat :=
  (tx.addresses.map tx.balanceOf).sum

/-- An address with a nonzero balance is among the addresses of the state. -/
theorem mem_addresses_of_balanceOf_ne_zero {tx : TransactionState} {address : Address}
    (h : tx.balanceOf address ≠ 0) : address ∈ tx.addresses := by
  unfold addresses
  rw [List.mem_eraseDups]
  simp only [List.mem_append, Std.ExtTreeMap.mem_keys]
  unfold balanceOf getAccount getAccountOptional at h
  split at h
  · rename_i hw
    exact .inr (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hw]; rfl))
  · split at h
    · rename_i _ hw
      exact .inl (.inr (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hw]; rfl)))
    · refine .inl (.inl (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr ?_))
      unfold State.getAccountOptional at h
      cases hp : tx.parent.preState.accounts[address]? with
      | none => rw [hp] at h; exact absurd rfl h
      | some _ => rfl

/-- The supply is the sum of the balances over any list of distinct addresses.

The list must hold every address with a nonzero balance. -/
theorem supply_eq_sum {tx : TransactionState} {addresses : List Address} (d : addresses.Nodup)
    (cover : ∀ address, tx.balanceOf address ≠ 0 → address ∈ addresses) :
    tx.supply = (addresses.map tx.balanceOf).sum :=
  sum_map_eq_of_nodup (nodup_eraseDups _) d (fun _ => mem_addresses_of_balanceOf_ne_zero) cover

/-- Two states with the same balance at every address have the same supply. -/
theorem supply_eq_of_balanceOf {tx tx' : TransactionState}
    (h : ∀ address, tx'.balanceOf address = tx.balanceOf address) : tx'.supply = tx.supply := by
  unfold supply
  rw [funext h]
  exact sum_map_eq_of_nodup (nodup_eraseDups _) (nodup_eraseDups _)
    (fun _ hne => mem_addresses_of_balanceOf_ne_zero (by rwa [← h] at hne))
    (fun _ => mem_addresses_of_balanceOf_ne_zero)

/-- Two states with the same account at every address have the same supply. -/
theorem supply_eq_of_getAccountOptional {tx tx' : TransactionState}
    (h : ∀ address, tx'.getAccountOptional address = tx.getAccountOptional address) :
    tx'.supply = tx.supply :=
  supply_eq_of_balanceOf fun address => by unfold balanceOf getAccount; rw [h]

/-- A state that reads as another at every address has the same supply. -/
theorem supply_eq_of_sameOutside {tx tx' : TransactionState} (h : SameOutside [] tx tx') :
    tx'.supply = tx.supply :=
  supply_eq_of_getAccountOptional fun address => (h address List.not_mem_nil).1

/-- A change of the balance at one address changes the supply by the same amount.

Every other balance must stay the same. -/
theorem supply_update {tx tx' : TransactionState} {address : Address}
    (h : ∀ other, other ≠ address → tx'.balanceOf other = tx.balanceOf other) :
    tx'.supply + tx.balanceOf address = tx.supply + tx'.balanceOf address := by
  let all := (address :: (tx.addresses ++ tx'.addresses)).eraseDups
  have d : all.Nodup := nodup_eraseDups _
  have mem : ∀ a, a ∈ tx.addresses ∨ a ∈ tx'.addresses ∨ a = address → a ∈ all := by
    intro a ha
    simp only [all, List.mem_eraseDups, List.mem_cons, List.mem_append]
    rcases ha with ha | ha | ha
    · exact .inr (.inl ha)
    · exact .inr (.inr ha)
    · exact .inl ha
  rw [supply_eq_sum d fun a ha => mem a (.inl (mem_addresses_of_balanceOf_ne_zero ha)),
    supply_eq_sum d fun a ha => mem a (.inr (.inl (mem_addresses_of_balanceOf_ne_zero ha)))]
  exact sum_map_add_eq_of_eq_off h d (mem address (.inr (.inr rfl)))

/-! ## The writes of one account -/

/-- A change of one account by `f` changes the supply by the change of its balance.

The change `f` succeeds on the account that the state reads. -/
theorem supply_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    ∃ account, f (tx.getAccount address) = .ok account ∧
      tx'.supply + tx.balanceOf address = tx.supply + account.balance.toNat := by
  obtain ⟨account, hf, hself, hother⟩ := modifyState_eq_ok h
  refine ⟨account, hf, ?_⟩
  have := supply_update (tx := tx) (tx' := tx') (address := address)
    fun other hne => by unfold balanceOf; rw [hother other hne]
  unfold balanceOf at this
  rwa [hself] at this

/-- A change of one account that keeps its balance keeps the supply. -/
theorem supply_modifyState_of_balance_eq {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (hf : ∀ account', f (tx.getAccount address) = .ok account' →
      account'.balance = (tx.getAccount address).balance)
    (h : tx.modifyState fork address f = .ok tx') : tx'.supply = tx.supply := by
  obtain ⟨account, hfa, hsum⟩ := supply_modifyState h
  rw [hf _ hfa] at hsum
  unfold balanceOf at hsum
  omega

/-- A move of ether keeps the supply. -/
theorem supply_moveEther {fork : Fork} {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx'.supply = tx.supply := by
  unfold moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  obtain ⟨debited, hd, hs1⟩ := supply_modifyState h1
  obtain ⟨credited, hc, hs2⟩ := supply_modifyState h2
  have := Account.toNat_balance_debit hd
  have := Account.toNat_balance_credit hc
  unfold balanceOf at hs1 hs2
  omega

/-- A creation of ether adds its amount to the supply. -/
theorem supply_createEther {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.createEther fork address amount = .ok tx') :
    tx'.supply = tx.supply + amount.toNat := by
  obtain ⟨credited, hc, hs⟩ := supply_modifyState h
  have := Account.toNat_balance_credit hc
  unfold balanceOf at hs
  omega

/-- A new balance at one address changes the supply by the change of that balance. -/
theorem supply_setAccountBalance {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    tx'.supply + tx.balanceOf address = tx.supply + amount.toNat := by
  obtain ⟨account, hf, hsum⟩ := supply_modifyState h
  cases hf
  exact hsum

/-- An increment of a nonce keeps the supply. -/
theorem supply_incrementNonce {fork : Fork} {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : tx'.supply = tx.supply :=
  supply_modifyState_of_balance_eq (fun _ hf => by cases hf; rfl) h

/-- A new code keeps the supply. -/
theorem supply_setCode {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') : tx'.supply = tx.supply := by
  obtain ⟨hself, hother⟩ := getAccount_setCode h
  refine supply_eq_of_balanceOf fun other => ?_
  unfold balanceOf
  by_cases hne : other = address
  · subst hne
    rw [hself]
  · unfold getAccount
    rw [hother other hne]

/-- A write of storage keeps the supply. -/
theorem supply_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') : tx'.supply = tx.supply :=
  supply_eq_of_getAccountOptional fun _ => getAccountOptional_setStorage h

/-- A touch of an account keeps the supply. -/
@[simp] theorem supply_touchAccount (tx : TransactionState) (address : Address) :
    (tx.touchAccount address).supply = tx.supply := by
  refine supply_eq_of_balanceOf fun other => ?_
  unfold balanceOf
  by_cases hne : other = address
  · subst hne
    rw [getAccount_touchAccount_self]
  · rw [getAccount_touchAccount hne]

/-- A record of a read of an account keeps the supply. -/
@[simp] theorem supply_recordAccountRead (tx : TransactionState) (address : Address) :
    (tx.recordAccountRead address).supply = tx.supply := rfl

/-- Taking the reads of another state keeps the supply. -/
@[simp] theorem supply_withReadsOf (tx other : TransactionState) :
    (tx.withReadsOf other).supply = tx.supply := rfl

/-- A record of a created account keeps the supply. -/
@[simp] theorem supply_markAccountCreated (tx : TransactionState) (address : Address) :
    (tx.markAccountCreated address).supply = tx.supply := rfl

/-- A write of transient storage keeps the supply. -/
@[simp] theorem supply_setTransientStorage (tx : TransactionState) (address : Address)
    (key : Bytes32) (value : U256) :
    (tx.setTransientStorage address key value).supply = tx.supply := rfl

/-- A wipe of the storage of an address keeps the supply. -/
@[simp] theorem supply_destroyStorage (tx : TransactionState) (address : Address) :
    (tx.destroyStorage address).supply = tx.supply :=
  supply_eq_of_getAccountOptional (getAccountOptional_destroyStorage tx address)

/-- The deletion of an account removes its balance from the supply. -/
theorem supply_destroyAccount (tx : TransactionState) (address : Address) :
    (tx.destroyAccount address).supply + tx.balanceOf address = tx.supply := by
  have hu := supply_update (tx := tx) (tx' := tx.destroyAccount address) (address := address)
    fun other hne => by simp only [balanceOf, getAccount_destroyAccount, hne, ↓reduceIte]
  have hself : (tx.destroyAccount address).balanceOf address = 0 := by
    simp only [balanceOf, getAccount_destroyAccount, ↓reduceIte]
    rfl
  omega

/-- A wipe of the nonce, the code and the storage of an account keeps the supply. -/
theorem supply_clearAccountPreservingBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} (h : tx.clearAccountPreservingBalance fork address = .ok tx') :
    tx'.supply = tx.supply := by
  unfold clearAccountPreservingBalance at h
  rw [supply_modifyState_of_balance_eq (fun _ hf => by cases hf; rfl) h, supply_destroyStorage]

/-- The deletion of the empty accounts among the touched ones keeps the supply. -/
@[simp] theorem supply_destroyTouchedEmptyAccounts (fork : Fork) (tx : TransactionState)
    (touched : List Address) :
    (tx.destroyTouchedEmptyAccounts fork touched).supply = tx.supply := by
  unfold destroyTouchedEmptyAccounts
  split
  · rfl
  · induction touched generalizing tx with
    | nil => rfl
    | cons address rest ih =>
      rw [List.foldl_cons, ih]
      split
      · rename_i hempty
        have := supply_destroyAccount tx address
        have hzero : tx.balanceOf address = 0 := by
          unfold balanceOf
          rw [eq_empty_of_accountExistsAndIsEmpty hempty]
          rfl
        omega
      · rfl

/-! ## The rollback and the end of a transaction -/

/-- A rollback to a snapshot of the same block gives back the supply of the snapshot. -/
theorem supply_restoreTxState {tx snapshot : TransactionState}
    (h : tx.parent = snapshot.parent) : (tx.restoreTxState snapshot).supply = snapshot.supply :=
  supply_eq_of_getAccountOptional (getAccountOptional_restoreTxState h)

/-- The end of a transaction moves its writes into its block and keeps the supply. -/
@[simp] theorem supply_incorporateTxIntoBlock (tx : TransactionState) :
    tx.incorporateTxIntoBlock.supply = tx.supply :=
  supply_eq_of_getAccountOptional (getAccountOptional_incorporateTxIntoBlock tx)

/-! ## Creations of ether in a row -/

/-- Creations of ether, one for each item in order, add the sum of their amounts to the supply. -/
theorem supply_foldlM_createEther {α : Type} {fork : Fork} (target : α → Address)
    (amount : α → U256) :
    ∀ (items : List α) {tx tx' : TransactionState},
      items.foldlM (fun tx x => tx.createEther fork (target x) (amount x)) tx = .ok tx' →
      tx'.supply = tx.supply + (items.map fun x => (amount x).toNat).sum
  | [], _, _, h => by
    cases h
    simp
  | _ :: rest, _, _, h => by
    obtain ⟨mid, hmid, h⟩ := Base.bind_ok_iff.mp h
    rw [supply_foldlM_createEther target amount rest h, supply_createEther hmid, List.map_cons,
      List.sum_cons, Nat.add_assoc]

end TransactionState

/-! ## The supply of a state -/

/-- The supply of ether in a state: the sum of the balances of its accounts, in wei. -/
def State.supply (state : State) : Nat :=
  (state.accounts.toList.map fun entry => entry.2.balance.toNat).sum

/-- The supply of a block state, read as a transaction, is the supply of the state after it. -/
theorem TransactionState.supply_ofBlock (block : BlockState) :
    (TransactionState.ofBlock block).supply = block.applyChanges.supply := by
  have read : ∀ address, (TransactionState.ofBlock block).balanceOf address =
      ((block.applyChanges.accounts[address]?).getD EMPTY_ACCOUNT).balance.toNat := by
    intro address
    unfold TransactionState.balanceOf TransactionState.getAccount
    rw [← BlockState.getAccountOptional_applyChanges]
    rfl
  rw [TransactionState.supply_eq_sum (Std.ExtTreeMap.nodup_keys (t := block.applyChanges.accounts))
    fun address hne => ?_]
  · unfold State.supply
    rw [← Std.ExtTreeMap.map_fst_toList_eq_keys, List.map_map]
    congr 1
    refine List.map_congr_left fun entry hmem => ?_
    rw [Function.comp_apply, read,
      (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (k := entry.1) (v := entry.2)).mp hmem]
    rfl
  · rw [read] at hne
    rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_iff_isSome_getElem?]
    cases h : block.applyChanges.accounts[address]? with
    | none =>
      rw [h] at hne
      exact absurd rfl hne
    | some _ => rfl

/-- The supply of a block with no write yet is the supply of the state before it. -/
theorem TransactionState.supply_ofPreState (pre : State) :
    (TransactionState.ofBlock ⟨pre, ∅, ∅, ∅, ∅⟩).supply = pre.supply := by
  rw [supply_ofBlock, BlockState.applyChanges_ofPreState]

end EthLib.Execution.State
