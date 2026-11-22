module

public import EthLib.Execution.Proofs.Blocks.Failures
public import EthLib.Execution.Proofs.Blocks.NoncesFit
public import EthLib.Execution.Proofs.Transactions.StateAborts

/-!
# Proofs: before Hegotá, a block aborts only with an error of the state

A block aborts when a system call, a transaction or a read of a system contract aborts.

From Hegotá on, a block also aborts because its fork is not yet specified.

Let every nonce of the state before the block be at most `2^64 - 1`, the bound of EIP-2681.

Each step of the body keeps that bound, so each of them runs on a block state within it.

A call or a transaction on such a state aborts only with an error of the state.

So before Hegotá, the transition of a block aborts only with an error of the state.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-! ## Failures that abort only with an error of the state -/

/-- Whether an error of a block, when it is an abort, is an abort with an error of the state. -/
private def StateAbort (e : BlockError) : Prop :=
  ∀ x, e = .aborted x → ∃ error, x = .state error

/-- An abort with an error of the state meets the property. -/
private theorem stateAbort_aborted {e : EvmError} (h : ∃ error, e = .state error) :
    StateAbort (.aborted e) :=
  fun _ hx => by cases hx; exact h

/-! ## The calls of a block -/

/-- The message of a system call has the numbers of its block, and the base fee as gas price.

So its numbers fit words when those of the block do. -/
private theorem wordsFit_systemMessage {env : BlockEnvironment fork} (target : Address)
    (data : ByteArray) (hwords : env.WordsFit) :
    WordsFit (systemMessage env target data).blockEnv (systemMessage env target data).txEnv := by
  refine ⟨hwords, ?_⟩
  simp only [systemMessage]
  split
  · exact hwords.2.2.2.1 _
  · exact Nat.two_pow_pos 256

/-- A system call on a block within the bound aborts only with an error of the state. -/
private theorem systemCall_eq_error {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {e : EvmError} (hfit : block.NoncesFit)
    (hwords : env.WordsFit)
    (h : systemCall env block target data = .error e) : ∃ error, e = .state error := by
  simp only [systemCall] at h
  split at h <;>
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact Transactions.processMessageCall_eq_error hfit (wordsFit_systemMessage _ _ hwords) h
    · cases h

/-- A system call that joins a body within the bound aborts only with an error of the state. -/
private theorem systemCall_join_eq_error {env : BlockEnvironment fork} {body : BodyState}
    {target : Address} {data : ByteArray} {e : EvmError} (hfit : body.block.NoncesFit)
    (hwords : env.WordsFit)
    (h : (do
      let out ← systemCall env body.block target data
      (body.join out.state).mapError EvmError.state : Except EvmError BodyState) = .error e) :
    ∃ error, e = .state error := by
  rcases Base.bind_eq_error h with h | ⟨out, -, h⟩
  · exact systemCall_eq_error hfit hwords h
  · cases hj : body.join out.state with
    | error e' => rw [hj] at h; cases h; exact ⟨e', rfl⟩
    | ok _ => rw [hj] at h; cases h

/-- The system calls at the start of a block abort only with an error of the state. -/
private theorem startSystemCalls_eq_error {env : BlockEnvironment fork} {parentHash : Hash32}
    {body : BodyState} {e : EvmError} (hfit : body.block.NoncesFit) (hwords : env.WordsFit)
    (h : startSystemCalls env parentHash body = .error e) : ∃ error, e = .state error := by
  have second : ∀ mid : BodyState, mid.block.NoncesFit →
      (if Fork.pectra ≤ fork then do
        let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
        Except.mapError EvmError.state (mid.join out.state)
      else pure mid) = .error e → ∃ error, e = .state error := by
    intro mid fit h
    split at h
    · exact systemCall_join_eq_error fit hwords h
    · cases h
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨out, hout, h⟩
    · exact systemCall_eq_error hfit hwords h
    · rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
      · cases hj : body.join out.state with
        | error e' => rw [hj] at h; cases h; exact ⟨e', rfl⟩
        | ok _ => rw [hj] at h; cases h
      · exact second mid (BodyState.noncesFit_join (mapError_ok_iff.mp hmid)
          (systemCall_noncesFit hfit hout)) h
  · rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
    · cases h
    · cases hmid
      exact second _ hfit h

/-! ## The body of a block -/

/-- Before Hegotá, the leaves of a block body within the bound abort only with errors of the state.

Each of them keeps every nonce within the bound.

The numbers that the block pushes as words must fit them. -/
private theorem leaves (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (before : fork < .hegota) (hwords : env.WordsFit) :
    BodyLeaves config env block StateAbort BlockState.NoncesFit BlockState.NoncesFit
      (fun _ => True) where
  plain _ ha _ _ _ x hx := absurd hx (ha x)
  dao _ _ _ _ _ h := by cases h
  dao_inv _ _ fit h := daoTransfer_noncesFit fit h
  start _ fit _ h := stateAbort_aborted (startSystemCalls_eq_error fit hwords h)
  start_inv _ _ fit h := startSystemCalls_noncesFit fit h
  inclusion _ _ _ _ _ _ _ h := by cases h
  process _ _ _ fit included _ h :=
    stateAbort_aborted (Transactions.processTransaction_eq_error before fit hwords included h)
  transaction_inv _ _ _ _ fit h := applyTransaction_noncesFit fit h
  join _ _ _ _ _ _ h := by cases h
  withdraw _ _ _ _ _ _ h := by cases h
  withdraw_inv _ _ _ _ fit withdrawn joined := fun address => by
    rw [BodyState.getAccount_join joined,
      (TransactionState.getAccount_foldlM_createEther _ _ _ withdrawn address).2.1]
    exact fit address
  skip_inv _ _ fit := fit
  code _ _ _ _ h := stateAbort_aborted <| by
    obtain ⟨e, -, rfl⟩ := mapError_eq_error h
    exact ⟨e, rfl⟩
  call _ _ _ fit _ h := stateAbort_aborted (systemCall_eq_error fit hwords h)
  call_failed _ _ _ _ _ _ _ _ _ h := by cases h
  call_inv _ _ _ _ _ fit called joined :=
    BodyState.noncesFit_join joined (systemCall_noncesFit fit called)
  rewards _ _ _ _ _ h := by cases h

/-! ## The body and the transition -/

/-- Before Hegotá, the body of a block aborts only with an error of the state.

Every nonce of the block state that it starts from must be at most `2^64 - 1`.

The numbers that the block pushes as words must fit them. -/
theorem applyBody_aborted {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {e : EvmError} (before : fork < .hegota)
    (hfit : start.NoncesFit) (hwords : env.WordsFit)
    (h : applyBody config env block start = .error (.aborted e)) :
    ∃ error, e = .state error :=
  (leaves config env block before hwords).errorsMeet_applyBody hfit _ h e rfl

/-- Before Hegotá, the transition of a block aborts only with an error of the state.

Every nonce of the state before the block must be at most `2^64 - 1`.

The numbers of the header that the block pushes as words must fit them. -/
theorem stateTransition_aborted {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {e : EvmError} (before : fork < .hegota) (hfit : chain.state.NoncesFit)
    (hwords : ∀ hashes, (blockEnvironment chain.config hashes block.header).WordsFit)
    (h : stateTransition chain block checkSeal = .error (.aborted e)) :
    ∃ error, e = .state error := by
  have meets : ErrorsMeet StateAbort (stateTransition chain block checkSeal) :=
    errorsMeet_stateTransition (fun _ ha _ x hx => absurd hx (ha x))
      (fun hle => absurd hle (Nat.not_le_of_lt before))
      fun hashes => (leaves _ _ _ before (hwords hashes)).errorsMeet_applyBody
        ((State.BlockState.noncesFit_ofState_iff _).mpr hfit)
  exact meets _ h e rfl

end EthLib.Execution.Blocks
