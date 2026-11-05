module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Transition
public import EthLib.Execution.Proofs.Blocks.Validate

/-!
# Proofs: the state transition of a block

A block that passes the transition commits to the state after it.

The state root of its header is the root of that state.

It also used the gas that its header states, and its Bloom filter is the filter of its logs.

Its fork is the active fork of its chain at its number and its time.

A transaction that cannot enter the block makes the block invalid, with its own error.

From Glamsterdam the transition fails as not yet specified.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State stateRoot)
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

variable {fork : Fork}

/-! ## The checks against the output -/

/-- The roots that the output gives hold the state root of the state after the block. -/
theorem outputRoots_state {transactions : List Transaction}
    {withdrawals : Since .shapella fork (List Withdrawal)} {output : BlockOutput fork}
    {post : State} {roots : OutputRoots}
    (h : outputRoots transactions withdrawals output post = .ok roots) :
    stateRoot keccak256 post = .ok roots.state := by
  unfold outputRoots at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨postRoot, hPost, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  exact mapError_ok_iff.mp hPost

/-- A block that passes the checks against its output used the gas that its header states.

Its state root and its Bloom filter are also those that its body gave. -/
theorem of_outputChecks {header : Header fork} {output : BlockOutput fork} {roots : OutputRoots}
    (h : firstFailure (outputChecks header output roots) = .ok ()) :
    output.gas.gasUsed = header.gasUsed ∧ roots.state = header.stateRoot ∧
      logsBloom output.logs = header.bloom := by
  have all := (firstFailure_eq_ok_iff _).mp h
  have get : ∀ c ∈ outputChecks header output roots, c.1 = true := all
  -- The first five checks come first in the list, before the checks of later forks.
  have first : ∀ c ∈ [(decide (output.gas.gasUsed = header.gasUsed),
      BlockError.wrongGasUsed header.gasUsed output.gas.gasUsed),
      (decide (roots.transactions = header.transactionsRoot), .wrongTransactionsRoot),
      (decide (roots.state = header.stateRoot), .wrongStateRoot),
      (decide (roots.receipts = header.receiptRoot), .wrongReceiptRoot),
      (decide (logsBloom output.logs = header.bloom), .wrongBloom)], c.1 = true :=
    fun c hc => get c (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hc)))
  refine ⟨?_, ?_, ?_⟩
  · exact of_decide_eq_true (first _ (.head _))
  · exact of_decide_eq_true (first _ (.tail _ (.tail _ (.head _))))
  · have := first _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    simpa using this

/-! ## The transactions -/

/-- A transaction that cannot enter its block makes the block invalid, with its error. -/
theorem applyTransaction_of_checkInclusion {env : BlockEnvironment fork} {index : Nat}
    {before : BodyOutput fork} {tx : Transaction} {e : InclusionError}
    (h : checkInclusion (UInt64.ofNat env.chainId) env before.gas (.ofBlock before.block) tx =
      .error e) :
    applyTransaction env index before tx = .error (.invalidTransaction index e) := by
  simp [applyTransaction, h, Except.mapError, bind, Except.bind]

/-! ## The transition -/

/-- From Glamsterdam, the transition fails, since the rules of that fork are not here yet. -/
theorem stateTransition_of_glamsterdam_le {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} (h : .glamsterdam ≤ fork) :
    stateTransition chain block checkSeal = .error (.aborted (.forkNotYetSpecified fork)) := by
  simp only [stateTransition, h, ↓reduceIte]
  rfl

/-- A block that passes the transition is at the active fork of its chain.

Its header commits to the state after it. -/
theorem of_stateTransition {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    chain.config.activeFork block.header.number block.header.timestamp.toNat = some fork ∧
      stateRoot keccak256 post = .ok block.header.stateRoot := by
  unfold stateTransition at h
  by_cases hFork : .glamsterdam ≤ fork
  · simp [hFork, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [hFork, ↓reduceIte] at h
    split at h
    · rename_i hActive
      obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
      obtain ⟨output, _, h⟩ := bind_ok_iff.mp h
      obtain ⟨roots, hRoots, h⟩ := bind_ok_iff.mp h
      obtain ⟨_, hChecks, h⟩ := bind_ok_iff.mp h
      cases h
      have hState := (of_outputChecks hChecks).2.1
      refine ⟨hActive, ?_⟩
      rw [← hState]
      exact outputRoots_state hRoots
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end EthLib.Execution.Blocks
