module

public import EthLib.Execution.Proofs.Blocks.AccessListRebuild
public import EthLib.Execution.Proofs.Blocks.Replay
public import EthLib.Execution.Proofs.Transactions.NoncesFit

/-!
# Proofs: the state transition keeps every nonce at most `2^64 - 1`

EIP-2681 limits every nonce to `2^64 - 1`.

Each transaction and each system call of a block keeps that bound.

The withdrawals, the rewards and the DAO transfer change only balances.

So a block that passes its transition on a state within the bound leaves a state within it.

From Glamsterdam, the block access list holds each nonce in 64 bits.

The bound then makes the nonces that the list rebuilds equal to the nonces after the block.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState EMPTY_ACCOUNT State TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork}

/-- Joining a state within the bound gives a body within the bound. -/
private theorem noncesFit_join {body body' : BodyState} {tx : TransactionState}
    (h : body.join tx = .ok body') (hfit : tx.NoncesFit) : body'.block.NoncesFit := by
  intro address
  rw [BodyState.getAccount_join h]
  exact hfit address

/-- A transaction that enters the body keeps every nonce within the bound. -/
theorem applyTransaction_noncesFit {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction} (hfit : before.block.NoncesFit)
    (h : applyTransaction env index before tx = .ok after) :
    after.block.NoncesFit := by
  obtain ⟨included, out, hcheck, hout, -, -, hjoin⟩ := applyTransaction_eq_ok h
  exact noncesFit_join hjoin (noncesFit_processTransaction hfit hcheck hout)

/-- The transactions of a block keep every nonce within the bound. -/
theorem applyTransactions_noncesFit {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork} (hfit : body.block.NoncesFit)
    (h : applyTransactions env body transactions = .ok output) :
    output.block.NoncesFit :=
  (applyTransactions_steps (fun a b : BodyOutput fork => a.block.NoncesFit → b.block.NoncesFit)
    (fun _ => id) (fun hab hbc fit => hbc (hab fit)) (fun h fit => applyTransaction_noncesFit fit h)
    h).1 hfit

/-- A system call keeps every nonce within the bound, at every fork. -/
private theorem systemCall_noncesFit {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput} (hfit : block.NoncesFit)
    (h : systemCall env block target data = .ok out) : out.state.NoncesFit := by
  simp only [systemCall] at h
  split at h <;>
  · obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact noncesFit_processMessageCall hfit hcall

/-- A system call that joins the body keeps every nonce within the bound. -/
private theorem join_systemCall_noncesFit {env : BlockEnvironment fork} {body body' : BodyState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput} (hfit : body.block.NoncesFit)
    (hcall : systemCall env body.block target data = .ok out)
    (hjoin : body.join out.state = .ok body') : body'.block.NoncesFit :=
  noncesFit_join hjoin (systemCall_noncesFit hfit hcall)

/-- From Pectra, the request contracts keep every nonce within the bound. -/
private theorem readRequests_noncesFit {env : BlockEnvironment fork} {body : BodyState}
    {result : BodyState × List ByteArray} (hfit : body.block.NoncesFit)
    (h : readRequests env body = .ok result) : result.1.block.NoncesFit := by
  by_cases hp : .pectra ≤ fork
  · rw [readRequests_of_pectra hp] at h
    refine foldlM_ok_invariant (fun st : BodyState × List ByteArray => st.1.block.NoncesFit)
      ?_ hfit h
    intro st c st' fit hstep
    obtain ⟨out, hout, hjoin, -⟩ := readRequest_eq_ok hstep
    exact join_systemCall_noncesFit fit (checkedSystemCall_ok hout).2.1 hjoin
  · rw [readRequests_of_lt_pectra (Nat.lt_of_not_le hp)] at h
    cases h
    exact hfit

/-- The system calls at the start of a block keep every nonce within the bound. -/
theorem startSystemCalls_noncesFit {env : BlockEnvironment fork} {parentHash : Hash32}
    {body body' : BodyState} (hfit : body.block.NoncesFit)
    (h : startSystemCalls env parentHash body = .ok body') :
    body'.block.NoncesFit := by
  obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok h
  have first : mid.block.NoncesFit := by
    by_cases hd : .dencun ≤ fork
    · obtain ⟨out, hout, hjoin⟩ := hFirst hd
      exact join_systemCall_noncesFit hfit hout hjoin
    · rw [hNoFirst hd]
      exact hfit
  by_cases hp : .pectra ≤ fork
  · obtain ⟨out, hout, hjoin⟩ := hSecond hp
    exact join_systemCall_noncesFit first hout hjoin
  · rw [hNoSecond hp]
    exact first

/-- The requests of a block keep every nonce within the bound. -/
theorem blockRequests_noncesFit {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} {logs : List Log} {result : BodyState × List ByteArray}
    (hfit : body.block.NoncesFit) (h : blockRequests depositContract env body logs = .ok result) :
    result.1.block.NoncesFit := by
  obtain ⟨hNoPectra, hPectra⟩ := blockRequests_eq_ok h
  by_cases hp : .pectra ≤ fork
  · obtain ⟨_, read, -, hread, rfl⟩ := hPectra hp
    exact readRequests_noncesFit (result := read) hfit ((readRequests_of_pectra hp).trans hread)
  · rw [hNoPectra hp]
    exact hfit

/-- A step that changes no nonce of a block within the bound keeps it within the bound. -/
private theorem onBlock_noncesFit {block block' : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (keeps : ∀ tx, step (.ofBlock block) = .ok tx → ∀ address,
      (tx.getAccount address).nonce = ((TransactionState.ofBlock block).getAccount address).nonce)
    (hfit : block.NoncesFit) (h : onBlock block step = .ok block') : block'.NoncesFit := by
  unfold onBlock at h
  obtain ⟨tx, htx, h⟩ := bind_ok_iff.mp h
  cases h
  intro address
  rw [TransactionState.getAccount_ofBlock_incorporateTxIntoBlock,
    keeps tx (mapError_ok_iff.mp htx) address]
  exact hfit address

/-- The DAO transfer keeps every nonce within the bound. -/
private theorem daoTransfer_noncesFit {config : ChainConfig} {number : Nat}
    {start state : BlockState} (hfit : start.NoncesFit)
    (h : daoTransfer config fork number start = .ok state) : state.NoncesFit := by
  unfold daoTransfer at h
  split at h
  · exact onBlock_noncesFit (fun _ hdao address => (applyDaoFork_nonce_codeHash hdao address).1)
      hfit h
  · cases h
    exact hfit

/-- The body of a block keeps every nonce within the bound. -/
theorem applyBody_noncesFit {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (hfit : start.NoncesFit) (h : applyBody config env block start = .ok output) :
    output.block.NoncesFit := by
  obtain ⟨_, body, txs, withdrawn, requested, hdao, hsys, htxs, hWithdrawn, hStays, hreq, hrew,
    -⟩ := applyBody_eq_ok h
  have fitTxs := applyTransactions_noncesFit
    (startSystemCalls_noncesFit (daoTransfer_noncesFit hfit hdao) hsys) htxs
  -- The withdrawals change only balances.
  have fitWithdrawn : withdrawn.block.NoncesFit := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨_, htx, hj⟩ := hWithdrawn hShapella
      intro address
      rw [BodyState.getAccount_join hj,
        (TransactionState.getAccount_foldlM_createEther _ _ _ htx address).2.1]
      exact fitTxs address
    · rw [hStays hShapella]
      exact fitTxs
  exact onBlock_noncesFit (fun _ hp address => (payRewards_nonce_codeHash hp address).1)
    (blockRequests_noncesFit (result := (requested, _)) fitWithdrawn hreq) hrew

/-- A block that passes its transition keeps every nonce within the bound.

Every nonce of the state before the block must be within the bound. -/
theorem stateTransition_noncesFit {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (hfit : chain.state.NoncesFit)
    (h : stateTransition chain block checkSeal = .ok post) :
    post.NoncesFit := by
  obtain ⟨env, output, hbody, hread⟩ := stateTransition_body h
  have fit := applyBody_noncesFit ((State.BlockState.noncesFit_ofState_iff _).mpr hfit) hbody
  refine (State.BlockState.noncesFit_ofState_iff post).mp fun address => ?_
  rw [hread]
  exact fit address

/-- A nonce of a state within the bound keeps its value through 64 bits. -/
private theorem toNat_ofNat_nonce {state : State} (hfit : state.NoncesFit) (address : Address) :
    ((state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce =
      (UInt64.ofNat ((state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce).toNat := by
  have hle : ((state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce ≤ MAX_NONCE := by
    cases hacc : state.getAccountOptional address with
    | none => exact Nat.zero_le _
    | some account => exact hfit address account hacc
  rw [UInt64.toNat_ofNat']
  unfold MAX_NONCE at hle
  omega

/-- From Glamsterdam, the list that a block commits to gives each nonce after the block.

The hypotheses are those of the rebuild of the state after the block.

The state before the block must also hold every nonce at most `2^64 - 1`.

The list holds a nonce in 64 bits, and the bound before and after the block makes that lossless. -/
theorem stateTransition_rebuild_nonce {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} {P : BlockState → Prop} (hFork : .glamsterdam ≤ fork)
    (hkeep : ∀ hashes, recentHashes chain.recent = .ok hashes →
      KeepsFollowable (blockEnvironment chain.config hashes block.header) P)
    (hstart : P ⟨chain.state, ∅, ∅, ∅, ∅⟩) (hlength : block.transactions.length < 2 ^ 32 - 1)
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
  let ⟨hashes, output, hHashes, hOutput, hHash, hall⟩ :=
    stateTransition_rebuild hFork hkeep hstart hlength h
  ⟨hashes, output, hHashes, hOutput, hHash, fun address =>
    (toNat_ofNat_nonce (stateTransition_noncesFit hfit h) address).trans
      (congrArg UInt64.toNat (hall address).2.1)⟩

end EthLib.Execution.Blocks
