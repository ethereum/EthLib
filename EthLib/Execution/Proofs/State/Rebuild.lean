module

public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: a property of states under which a block state can be rebuilt

A block state can be rebuilt when its code matches its hash and empty accounts hold no storage.

A missing account counts as empty.

Adding ether keeps this, and so does moving the writes of a transaction into its block.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- Returned code matches its hash, and an empty or missing account has only zero storage.

An account whose only nonzero field is its balance may hold storage.

From Paris, a change that leaves an account empty deletes it with its storage. -/
structure RebuildInvariant (tx : TransactionState) : Prop where
  /-- Each returned code has the hash under which it is read. -/
  code : ∀ hash code, tx.getCode hash = .ok code → keccak256 code = hash
  /-- Empty and missing accounts hold no nonzero storage word. -/
  storage : ∀ address, tx.getAccount address = EMPTY_ACCOUNT →
    ∀ key, tx.getStorage address key = 0

/-- A block state can be rebuilt when, with no write on top, the property above holds. -/
def Rebuildable (block : BlockState) : Prop :=
  RebuildInvariant (TransactionState.ofBlock block)

/-- Adding ether cannot make a nonempty account empty. -/
theorem getAccount_eq_empty_of_createEther {fork : Fork}
    {tx tx' : TransactionState} {target : Address} {amount : U256}
    (h : tx.createEther fork target amount = .ok tx') (address : Address)
    (empty : tx'.getAccount address = EMPTY_ACCOUNT) : tx.getAccount address = EMPTY_ACCOUNT := by
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

/-- Under the property, adding ether keeps every storage word. -/
theorem RebuildInvariant.getStorage_createEther {fork : Fork} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (valid : RebuildInvariant tx)
    (h : tx.createEther fork target amount = .ok tx') (address : Address) (key : Bytes32) :
    tx'.getStorage address key = tx.getStorage address key := by
  rw [TransactionState.getStorage_modifyState h]
  split
  · rename_i deleted
    have empty : tx'.getAccount address = EMPTY_ACCOUNT := by
      simp only [TransactionState.getAccount, deleted.1, deleted.2, Option.getD_none]
    exact (valid.storage address
      (getAccount_eq_empty_of_createEther h address empty) key).symm
  · rfl

/-- Adding ether keeps the property. -/
theorem RebuildInvariant.createEther {fork : Fork} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (valid : RebuildInvariant tx)
    (h : tx.createEther fork target amount = .ok tx') : RebuildInvariant tx' := by
  refine ⟨?_, ?_⟩
  · intro hash code read
    rw [TransactionState.getCode_modifyState h] at read
    exact valid.code hash code read
  · intro address empty key
    rw [valid.getStorage_createEther h]
    exact valid.storage address
      (getAccount_eq_empty_of_createEther h address empty) key

/-- Incorporating a transaction into its block keeps the property. -/
theorem RebuildInvariant.ofBlock_incorporateTxIntoBlock {tx : TransactionState}
    (valid : RebuildInvariant tx) : Rebuildable tx.incorporateTxIntoBlock.parent := by
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

end EthLib.Execution.State
