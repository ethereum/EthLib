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

/-- A system call on a block within the bound aborts only with an error of the state. -/
private theorem systemCall_eq_error {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {e : EvmError} (hfit : block.NoncesFit)
    (h : systemCall env block target data = .error e) : ∃ error, e = .state error := by
  simp only [systemCall] at h
  split at h <;>
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact Transactions.processMessageCall_eq_error hfit h
    · cases h

/-- A system call that joins a body within the bound aborts only with an error of the state. -/
private theorem systemCall_join_eq_error {env : BlockEnvironment fork} {body : BodyState}
    {target : Address} {data : ByteArray} {e : EvmError} (hfit : body.block.NoncesFit)
    (h : (do
      let out ← systemCall env body.block target data
      (body.join out.state).mapError EvmError.state : Except EvmError BodyState) = .error e) :
    ∃ error, e = .state error := by
  rcases Base.bind_eq_error h with h | ⟨out, -, h⟩
  · exact systemCall_eq_error hfit h
  · cases hj : body.join out.state with
    | error e' => rw [hj] at h; cases h; exact ⟨e', rfl⟩
    | ok _ => rw [hj] at h; cases h

/-- The system calls at the start of a block abort only with an error of the state. -/
private theorem startSystemCalls_eq_error {env : BlockEnvironment fork} {parentHash : Hash32}
    {body : BodyState} {e : EvmError} (hfit : body.block.NoncesFit)
    (h : startSystemCalls env parentHash body = .error e) : ∃ error, e = .state error := by
  have second : ∀ mid : BodyState, mid.block.NoncesFit →
      (if Fork.pectra ≤ fork then do
        let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
        Except.mapError EvmError.state (mid.join out.state)
      else pure mid) = .error e → ∃ error, e = .state error := by
    intro mid fit h
    split at h
    · exact systemCall_join_eq_error fit h
    · cases h
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨out, hout, h⟩
    · exact systemCall_eq_error hfit h
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

/-- A transaction on a body within the bound aborts only with an error of the state. -/
private theorem errorsMeet_applyTransaction {env : BlockEnvironment fork} {index : Nat}
    {before : BodyOutput fork} (tx : Transaction) (hbefore : fork < .hegota)
    (hfit : before.block.NoncesFit) :
    ErrorsMeet StateAbort (applyTransaction env index before tx) := by
  unfold applyTransaction
  refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ h => by cases h)
    fun included hincl => ?_
  refine ErrorsMeet.bind (ErrorsMeet.aborted fun _ h => stateAbort_aborted <|
    Transactions.processTransaction_eq_error hbefore hfit (mapError_ok_iff.mp hincl) h)
    fun out hout => ?_
  refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ h => by cases h) fun body _ => ?_
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.pure _) fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.bind (ErrorsMeet.map _ (ErrorsMeet.mapError fun _ _ _ h => by cases h))
      fun _ _ => ErrorsMeet.pure _

/-- The transactions on a body within the bound abort only with an error of the state. -/
private theorem errorsMeet_applyTransactions {env : BlockEnvironment fork} {body : BodyState}
    (transactions : List Transaction) (hbefore : fork < .hegota)
    (hfit : body.block.NoncesFit) :
    ErrorsMeet StateAbort (applyTransactions env body transactions) := fun _ h =>
  foldlM_error_of_step (fun before : BodyOutput fork => before.block.NoncesFit) StateAbort
    (fun _ _ _ fit h => applyTransaction_noncesFit fit h)
    (fun _ _ e fit h => errorsMeet_applyTransaction _ hbefore fit e h)
    (b := ⟨body, .zero, 0, [], []⟩) hfit h

/-- A checked system call on a block within the bound aborts only with an error of the state. -/
private theorem errorsMeet_checkedSystemCall {env : BlockEnvironment fork} {block : BlockState}
    (target : Address) (data : ByteArray) (hfit : block.NoncesFit) :
    ErrorsMeet StateAbort (checkedSystemCall env block target data) := by
  unfold checkedSystemCall
  refine ErrorsMeet.bind (ErrorsMeet.aborted fun _ h => stateAbort_aborted <| ?_) fun _ _ => ?_
  · unfold codeAt at h
    dsimp only at h
    cases hc : (TransactionState.ofBlock block).getCode
        ((TransactionState.ofBlock block).getAccount target).codeHash with
    | error e' => rw [hc] at h; cases h; exact ⟨e', rfl⟩
    | ok _ => rw [hc] at h; cases h
  have rest : ErrorsMeet StateAbort (do
      let out ← (systemCall env block target data).mapError BlockError.aborted
      match out.error with
      | some error => throw (BlockError.systemCallFailed target error)
      | none => pure out) := by
    refine ErrorsMeet.bind
      (ErrorsMeet.aborted fun _ h => stateAbort_aborted (systemCall_eq_error hfit h))
      fun _ _ => ?_
    split
    · exact ErrorsMeet.throw fun _ h => by cases h
    · exact ErrorsMeet.pure _
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.throw fun _ h => by cases h) fun _ _ => rest
  · exact rest

/-- A request read on a body within the bound aborts only with an error of the state. -/
private theorem errorsMeet_readRequest {env : BlockEnvironment fork}
    {state : BodyState × List ByteArray} (contract : UInt8 × Address)
    (hfit : state.1.block.NoncesFit) : ErrorsMeet StateAbort (readRequest env state contract) := by
  unfold readRequest
  refine ErrorsMeet.bind (errorsMeet_checkedSystemCall _ _ hfit) fun _ _ => ?_
  exact ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ h => by cases h)
    fun _ _ => ErrorsMeet.pure _

/-- The request reads on a body within the bound abort only with an error of the state. -/
private theorem errorsMeet_readRequests {env : BlockEnvironment fork} {body : BodyState}
    (hfit : body.block.NoncesFit) : ErrorsMeet StateAbort (readRequests env body) := by
  unfold readRequests
  split
  · intro _ h
    refine foldlM_error_of_step (fun st : BodyState × List ByteArray => st.1.block.NoncesFit)
      StateAbort (fun st c st' fit hstep => ?_)
      (fun _ c e fit h => errorsMeet_readRequest c fit e h) hfit h
    obtain ⟨out, hout, hjoin, -⟩ := readRequest_eq_ok hstep
    exact BodyState.noncesFit_join hjoin
      (systemCall_noncesFit fit (checkedSystemCall_ok hout).2.1)
  · exact ErrorsMeet.ok _

/-- The requests of a body within the bound abort only with an error of the state. -/
private theorem errorsMeet_blockRequests {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} (logs : List Log) (hfit : body.block.NoncesFit) :
    ErrorsMeet StateAbort (blockRequests depositContract env body logs) := by
  unfold blockRequests
  split
  · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_readRequests hfit) fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.pure _

/-- The hash of the block access list never aborts. -/
private theorem errorsMeet_accessListHashOf (body : BodyState) (gasLimit : Nat) :
    ErrorsMeet StateAbort (accessListHashOf fork body gasLimit) := by
  unfold accessListHashOf
  split
  · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.map _ (ErrorsMeet.mapError fun _ _ _ h => by cases h)
  · exact ErrorsMeet.pure _

/-- Before Hegotá, a body within the bound aborts only with an error of the state. -/
private theorem errorsMeet_applyBody {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} (before : fork < .hegota)
    (hfit : start.NoncesFit) : ErrorsMeet StateAbort (applyBody config env block start) := by
  unfold applyBody
  refine ErrorsMeet.bind ?_ fun state hstate => ?_
  · unfold daoTransfer
    split
    · exact ErrorsMeet.onBlock fun _ _ _ h => by cases h
    · exact ErrorsMeet.pure _
  have f1 := daoTransfer_noncesFit hfit hstate
  refine ErrorsMeet.bind (ErrorsMeet.aborted fun _ h => stateAbort_aborted <|
    startSystemCalls_eq_error (body := .init state) f1 h) fun body hbody => ?_
  have f2 := startSystemCalls_noncesFit (body := .init state) f1 (mapError_ok_iff.mp hbody)
  refine ErrorsMeet.bind (errorsMeet_applyTransactions _ before f2) fun output houtput => ?_
  have f3 := applyTransactions_noncesFit f2 houtput
  dsimp only
  split
  · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ h => by cases h) fun tx htx => ?_
    refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ h => by cases h) fun b hb => ?_
    have fb : b.block.NoncesFit := by
      intro address
      rw [BodyState.getAccount_join (mapError_ok_iff.mp hb),
        (TransactionState.getAccount_foldlM_createEther _ _ _ (mapError_ok_iff.mp htx)
          address).2.1]
      exact f3 address
    refine ErrorsMeet.bind (errorsMeet_blockRequests _ fb) fun r _ => ?_
    obtain ⟨requested, requests⟩ := r
    refine ErrorsMeet.bind (ErrorsMeet.onBlock fun _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_accessListHashOf _ _) fun _ _ => ErrorsMeet.pure _
  · refine ErrorsMeet.bind (ErrorsMeet.pure _) fun b hb => ?_
    cases hb
    refine ErrorsMeet.bind (errorsMeet_blockRequests _ f3) fun r _ => ?_
    obtain ⟨requested, requests⟩ := r
    refine ErrorsMeet.bind (ErrorsMeet.onBlock fun _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_accessListHashOf _ _) fun _ _ => ErrorsMeet.pure _

/-! ## The body and the transition -/

/-- Before Hegotá, the body of a block aborts only with an error of the state.

Every nonce of the block state that it starts from must be at most `2^64 - 1`. -/
theorem applyBody_aborted {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {e : EvmError} (before : fork < .hegota)
    (hfit : start.NoncesFit) (h : applyBody config env block start = .error (.aborted e)) :
    ∃ error, e = .state error :=
  errorsMeet_applyBody before hfit _ h e rfl

/-- Before Hegotá, the transition of a block aborts only with an error of the state.

Every nonce of the state before the block must be at most `2^64 - 1`. -/
theorem stateTransition_aborted {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {e : EvmError} (before : fork < .hegota) (hfit : chain.state.NoncesFit)
    (h : stateTransition chain block checkSeal = .error (.aborted e)) :
    ∃ error, e = .state error := by
  have meets : ErrorsMeet StateAbort (stateTransition chain block checkSeal) :=
    errorsMeet_stateTransition (fun _ ha _ x hx => absurd hx (ha x))
      (fun hle => absurd hle (Nat.not_le_of_lt before))
      fun _ => errorsMeet_applyBody before ((State.BlockState.noncesFit_ofState_iff _).mpr hfit)
  exact meets _ h e rfl

end EthLib.Execution.Blocks
