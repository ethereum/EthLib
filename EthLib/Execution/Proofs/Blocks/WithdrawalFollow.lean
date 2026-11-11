module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Proofs.Blocks.AccessListFollow
public import EthLib.Execution.Proofs.State.Frame
public import EthLib.Execution.Proofs.State.Rebuild

/-!
# Proofs: the access-list builder follows the withdrawals

A withdrawal only adds ether to an account, so it writes no code and no storage word.

It may delete an empty account, whose storage is already zero when the block state can be rebuilt.

So the withdrawals keep every storage word, and the builder follows them.

They also keep the property that lets the block state be rebuilt.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State

private theorem withdrawalState_kept {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} {tx : TransactionState} (valid : Rebuildable block)
    (h : withdrawalState fork block withdrawals = .ok tx) :
    tx.parent = block ∧ RebuildInvariant tx ∧
      ∀ address key, tx.getStorage address key =
        (TransactionState.ofBlock block).getStorage address key := by
  apply foldlM_ok_invariant
    (fun tx => tx.parent = block ∧ RebuildInvariant tx ∧
      ∀ address key, tx.getStorage address key =
        (TransactionState.ofBlock block).getStorage address key) ?_
    ⟨rfl, valid, fun _ _ => rfl⟩ h
  intro before w after previous step
  exact ⟨(TransactionState.parent_createEther step).trans previous.1,
    previous.2.1.createEther step,
    fun address key => (previous.2.1.getStorage_createEther step address key).trans
      (previous.2.2 address key)⟩

/-- The withdrawals keep every storage word of a block state that can be rebuilt. -/
theorem getStorage_withdrawalState {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} {tx : TransactionState} (valid : Rebuildable block)
    (h : withdrawalState fork block withdrawals = .ok tx) (address : Address) (key : Bytes32) :
    tx.getStorage address key = (TransactionState.ofBlock block).getStorage address key :=
  (withdrawalState_kept valid h).2.2 address key

/-- The access-list builder follows the withdrawals of a block state that can be rebuilt. -/
theorem withdrawalState_followable {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} {tx : TransactionState} (valid : Rebuildable block)
    (h : withdrawalState fork block withdrawals = .ok tx) : Followable block tx := by
  obtain ⟨parent, invariant, storage⟩ := withdrawalState_kept valid h
  exact ⟨parent, fun address key _ => storage address key,
    fun _ _ code _ read => invariant.code _ code read⟩

/-- After the withdrawals, the block state can still be rebuilt. -/
theorem withdrawalState_rebuildable {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} {tx : TransactionState} (valid : Rebuildable block)
    (h : withdrawalState fork block withdrawals = .ok tx) :
    Rebuildable tx.incorporateTxIntoBlock.parent :=
  (withdrawalState_kept valid h).2.1.ofBlock_incorporateTxIntoBlock

end EthLib.Execution.Blocks
