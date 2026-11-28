module

public import EthLib.Execution.Proofs.Blocks.AccessListRebuild
public import EthLib.Execution.Proofs.Blocks.NoncesFit
public import EthLib.Execution.Proofs.Blocks.SystemCallFollow
public import EthLib.Execution.Proofs.Blocks.WithdrawalFollow
public import EthLib.Execution.Proofs.Transactions.Rebuild

/-!
# Proofs: the access list of a block rebuilds the state after it

From Glamsterdam, the list that the header commits to rebuilds the state after the block.

It needs codes that match their hashes, no delegation at nonce 0, and few enough transactions.

It also needs that the block wipes no storage of an account that had nonce 0, no code and storage.

Source: [EIP-7928, Recording Semantics by Change Type][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.Transactions

/-- A block state that can be rebuilt, where no account with nonce 0 has a delegation's code hash.

Each code read has its hash, and no account with nonce 0 and no code holds storage. -/
def RebuildableBlock (block : BlockState) : Prop :=
  Rebuildable block ∧ DelegationsHaveNonce (.ofBlock block)

/-- On a state where no account with nonce 0 and no code holds storage, every wipe is allowed. -/
theorem _root_.EthLib.Execution.State.Rebuildable.wipeAllowed {pre : State}
    (valid : Rebuildable ⟨pre, ∅, ∅, ∅, ∅⟩)
    (address : Address) : WipeAllowed pre address := by
  by_cases hnc : HasNonceOrCode (.ofBlock ⟨pre, ∅, ∅, ∅, ∅⟩) address
  · exact .inl hnc
  · obtain ⟨hnonce, hcode⟩ := not_hasNonceOrCode_iff.mp hnc
    refine .inr fun key => ?_
    have h := valid.storage address hnonce hcode key
    unfold TransactionState.getStorage TransactionState.ofBlock at h
    simpa [StorageMap.slot] using h

/-- From Dencun, the calls of a body keep a block state ready on `pre`.

The builder follows each call whose wipes are allowed on `pre`.

That covers the system calls, each transaction that enters the block, and the withdrawals.

Dencun is needed for the transactions, which then delete only accounts that they created. -/
theorem keepsFollowable_rebuildReady {fork : Fork} (hfork : .dencun ≤ fork) (pre : State)
    (env : BlockEnvironment fork) : KeepsFollowable env (RebuildReady pre) (WipeAllowed pre) := by
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  refine ⟨?_, ?_, ?_⟩
  · intro block target data out ready h
    have valid := systemCall_rebuildState hsd ready.code ready.delegations h
    exact ⟨valid.parent, valid.rebuildReady ready, valid.followable ready.plain⟩
  · intro gas block tx included out ready _ h
    have valid := processTransaction_rebuildEnd hfork ready.code ready.delegations h
    exact ⟨valid.parent, valid.rebuildReady ready, valid.followable ready.plain⟩
  · intro block withdrawals tx ready h
    have valid := withdrawalState_rebuildState ready.code ready.delegations h
    exact ⟨valid.parent, valid.rebuildReady ready, valid.followable ready.plain⟩

/-- From Glamsterdam, the list that the header commits to rebuilds the state after the block.

From Hegota the transition is not yet specified, so for Hegota this speaks of the Glamsterdam rules.

The block must wipe no storage of an account that had nonce 0, no code and storage before it.

That is an assumption on the run: on mainnet, only a creation at one of 28 accounts breaks it. -/
theorem stateTransition_rebuild_of_wipeAllowed {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hFork : .glamsterdam ≤ fork)
    -- Each code read in the state before the block has its hash.
    (hcode : ∀ hash code,
      (TransactionState.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩).getCode hash = .ok code →
        keccak256 code = hash)
    -- No account with nonce 0 there has the code hash of a delegation indicator.
    (hdelegations : DelegationsHaveNonce (.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩))
    -- The block has fewer than 2^32 - 1 transactions.
    (hlength : block.transactions.length < 2 ^ 32 - 1)
    -- Each account whose storage the body wipes had a nonce or code, or no storage, before it.
    --
    -- A creation wipes the storage at its address.
    --
    -- So no creation lands on an account with nonce 0, no code and storage.
    (hwipes : ∀ hashes output, recentHashes chain.recent = .ok hashes →
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output →
      ∀ address ∈ output.block.storageClears, WipeAllowed chain.state address)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      -- An account missing from a state reads as the empty account.
      ∀ address,
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).balance =
          output.body.builder.build.balanceAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).balance ∧
        -- The nonce is in 64 bits, as the list holds it.
        UInt64.ofNat ((post.getAccountOptional address).getD EMPTY_ACCOUNT).nonce =
          output.body.builder.build.nonceAfter address
            (UInt64.ofNat ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce) ∧
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash =
          output.body.builder.build.codeHashAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash ∧
        ∀ key, post.getStorage address key =
          output.body.builder.build.storageAfter address key
            (chain.state.getStorage address key) :=
  stateTransition_rebuild hFork
    (fun _ _ => keepsFollowable_rebuildReady (Nat.le_trans (by decide) hFork) chain.state _)
    (RebuildReady.start hcode hdelegations) hlength hwipes h

/-- From Glamsterdam, the list that the header commits to rebuilds the state after the block.

From Hegota the transition is not yet specified, so this holds from Glamsterdam up to Hegota.

Mainnet breaks its hypothesis with 28 accounts of nonce 0 and no code that hold storage. -/
theorem stateTransition_rebuild_of_rebuildableBlock {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    -- The state before the block must be rebuildable.
    --
    -- No account with nonce 0 there has the code hash of a delegation indicator.
    (hFork : .glamsterdam ≤ fork) (hstart : RebuildableBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩)
    -- The block has fewer than 2^32 - 1 transactions.
    (hlength : block.transactions.length < 2 ^ 32 - 1)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      -- An account missing from a state reads as the empty account.
      ∀ address,
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).balance =
          output.body.builder.build.balanceAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).balance ∧
        -- The nonce is in 64 bits, as the list holds it.
        UInt64.ofNat ((post.getAccountOptional address).getD EMPTY_ACCOUNT).nonce =
          output.body.builder.build.nonceAfter address
            (UInt64.ofNat ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce) ∧
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash =
          output.body.builder.build.codeHashAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash ∧
        ∀ key, post.getStorage address key =
          output.body.builder.build.storageAfter address key
            (chain.state.getStorage address key) :=
  stateTransition_rebuild_of_wipeAllowed hFork hstart.1.code hstart.2 hlength
    (fun _ _ _ _ address _ => hstart.1.wipeAllowed address) h

/-- From Glamsterdam, the list that the header commits to gives each nonce after the block.

The hypotheses are those of the rebuild of the state after the block.

The state before the block must also hold every nonce at most 2^64 - 1. -/
theorem stateTransition_rebuild_nonce_of_wipeAllowed {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hFork : .glamsterdam ≤ fork)
    (hcode : ∀ hash code,
      (TransactionState.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩).getCode hash = .ok code →
        keccak256 code = hash)
    (hdelegations : DelegationsHaveNonce (.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩))
    (hlength : block.transactions.length < 2 ^ 32 - 1)
    (hwipes : ∀ hashes output, recentHashes chain.recent = .ok hashes →
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output →
      ∀ address ∈ output.block.storageClears, WipeAllowed chain.state address)
    (hfit : chain.state.NoncesFit) (h : stateTransition chain block checkSeal = .ok post) :
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
    (fun _ _ => keepsFollowable_rebuildReady (Nat.le_trans (by decide) hFork) chain.state _)
    (RebuildReady.start hcode hdelegations) hlength hwipes hfit h

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
  stateTransition_rebuild_nonce_of_wipeAllowed hFork hstart.1.code hstart.2 hlength
    (fun _ _ _ _ address _ => hstart.1.wipeAllowed address) hfit h

end EthLib.Execution.Blocks
