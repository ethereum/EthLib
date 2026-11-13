module

public import EthLib.Execution.Proofs.Blocks.AccessListRebuild
public import EthLib.Execution.Proofs.Blocks.NoncesFit
public import EthLib.Execution.Proofs.Blocks.SystemCallFollow
public import EthLib.Execution.Proofs.Blocks.WithdrawalFollow
public import EthLib.Execution.Proofs.Transactions.Rebuild

/-!
# Proofs: the access list of a block rebuilds the state after it

Take a block state that can be rebuilt.

No account with nonce 0 in it has the code hash of a delegation indicator.

Each system call, each transaction that enters the block, and the withdrawals keep that property.

The access-list builder follows each of them.

So, from Glamsterdam, the list that the header commits to rebuilds the state after the block.

It needs only the property of the state before the block, and fewer than 2^32 - 1 transactions.

Source: [EIP-7928, Recording Semantics by Change Type][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.Transactions

/-- A block state that can be rebuilt, where no account with nonce 0 has a delegation's code hash.

Each code read has its hash, and no empty or missing account holds a nonzero storage word. -/
def RebuildableBlock (block : BlockState) : Prop :=
  Rebuildable block ∧ DelegationsHaveNonce (.ofBlock block)

/-- When the state at the end of a transaction keeps the rebuild properties, so does the block. -/
theorem _root_.EthLib.Execution.Evm.RebuildEnd.rebuildableBlock {block : BlockState}
    {tx : TransactionState} (valid : RebuildEnd block tx) :
    RebuildableBlock tx.incorporateTxIntoBlock.parent := by
  exact ⟨valid.toRebuildInvariant.ofBlock_incorporateTxIntoBlock,
    valid.delegations.ofBlock_incorporateTxIntoBlock⟩

/-- Withdrawals give no account with nonce 0 the code hash of a delegation indicator. -/
theorem withdrawalState_delegationsHaveNonce {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} {tx : TransactionState}
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : withdrawalState fork block withdrawals = .ok tx) :
    DelegationsHaveNonce (.ofBlock tx.incorporateTxIntoBlock.parent) := by
  refine DelegationsHaveNonce.ofBlock_incorporateTxIntoBlock ?_
  refine foldlM_ok_invariant DelegationsHaveNonce ?_ delegations h
  intro before w after previous step address code hnonce hhash hdeleg
  obtain ⟨-, hn, hc⟩ := TransactionState.getAccount_createEther step address
  rw [hn] at hnonce
  rw [hc] at hhash ⊢
  exact previous address code hnonce hhash hdeleg

/-- From Dencun, the calls of a body keep a rebuildable block state, and the builder follows each.

That covers the system calls, each transaction that enters the block, and the withdrawals.

Dencun is needed for the transactions, which then delete only accounts that they created. -/
theorem keepsFollowable_rebuildableBlock {fork : Fork} (hfork : .dencun ≤ fork)
    (env : BlockEnvironment fork) : KeepsFollowable env RebuildableBlock := by
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  refine ⟨?_, ?_, ?_⟩
  · intro block target data out hP h
    exact ⟨systemCall_followable hsd hP.1 hP.2 h,
      systemCall_rebuildable hsd hP.1 hP.2 h, systemCall_delegationsHaveNonce hsd hP.1 hP.2 h⟩
  · intro gas block tx included out hP _ h
    have valid := processTransaction_rebuildEnd hfork hP.1 hP.2 h
    exact ⟨valid.followable, valid.rebuildableBlock⟩
  · intro block withdrawals tx hP h
    exact ⟨withdrawalState_followable hP.1 h, withdrawalState_rebuildable hP.1 h,
      withdrawalState_delegationsHaveNonce hP.2 h⟩

/-- From Glamsterdam, the list that the header commits to rebuilds the state after the block.

The state before the block must be rebuildable.

No account with nonce 0 there has the code hash of a delegation indicator.

An account missing from a state reads as the empty account.

The nonce is in 64 bits, as the list holds it.

The block has fewer than 2^32 - 1 transactions.

From Hegota the transition is not yet specified, so this holds from Glamsterdam up to Hegota. -/
theorem stateTransition_rebuild_of_rebuildableBlock {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hFork : .glamsterdam ≤ fork) (hstart : RebuildableBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩)
    (hlength : block.transactions.length < 2 ^ 32 - 1)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      ∀ address,
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).balance =
          output.body.builder.build.balanceAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).balance ∧
        UInt64.ofNat ((post.getAccountOptional address).getD EMPTY_ACCOUNT).nonce =
          output.body.builder.build.nonceAfter address
            (UInt64.ofNat ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce) ∧
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash =
          output.body.builder.build.codeHashAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash ∧
        ∀ key, post.getStorage address key =
          output.body.builder.build.storageAfter address key
            (chain.state.getStorage address key) := by
  exact stateTransition_rebuild hFork
    (fun _ _ => keepsFollowable_rebuildableBlock (Nat.le_trans (by decide) hFork) _)
    hstart hlength h

/-- From Glamsterdam, the list that the header commits to gives each nonce after the block.

The state before the block must be rebuildable, and hold every nonce at most 2^64 - 1.

No account with nonce 0 there has the code hash of a delegation indicator.

The block has fewer than 2^32 - 1 transactions. -/
theorem stateTransition_rebuild_nonce_of_rebuildableBlock {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hFork : .glamsterdam ≤ fork) (hstart : RebuildableBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩)
    (hlength : block.transactions.length < 2 ^ 32 - 1) (hfit : chain.state.NoncesFit)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      ∀ address,
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).nonce =
          UInt64.toNat (output.body.builder.build.nonceAfter address
            (UInt64.ofNat ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce)) :=
  stateTransition_rebuild_nonce hFork
    (fun _ _ => keepsFollowable_rebuildableBlock (Nat.le_trans (by decide) hFork) _) hstart hlength
    hfit h

end EthLib.Execution.Blocks
