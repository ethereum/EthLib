module

public import EthLib.Execution.Proofs.Blocks.Failures
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Evm.Call.Halts
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: a system call that must succeed fails only with an error that does not abort

The first frame of a message records the error that stopped it, or none when it succeeded.

That error never aborts: an error that aborts makes the whole run fail instead.

A system call returns the error of its first frame.

So a block fails for a system call that must succeed only with an error that does not abort.

In particular it never fails that way with an error of the state.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-- The error that the message of a transaction records, when it returns, does not abort. -/
theorem error_processMessageCall {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Transactions.Authorization}
    {paid : Std.ExtTreeSet Address} {out : Transactions.CallOutput}
    (h : Transactions.processMessageCall (Meter := Meter) chainId message state substate auths
      paid = .ok out) {e : EvmError} (he : out.error = some e) : e.aborts = false := by
  unfold Transactions.processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      cases he
      exact Bool.eq_false_iff.mpr ‹_›
  · split at h
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      unfold Transactions.CallOutput.ofFrame at he
      split at he
      · exact error_processCreateMessage hrun he
      · cases he
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      unfold Transactions.CallOutput.ofFrame at he
      split at he
      · exact error_processMessage hrun he
      · cases he

/-- The error that a system call records, when it returns, does not abort. -/
theorem error_systemCall {env : BlockEnvironment fork} {block : State.BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (h : systemCall env block target data = .ok out) {e : EvmError} (he : out.error = some e) :
    e.aborts = false := by
  unfold systemCall at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨out', hout, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact error_processMessageCall hout he

/-! ## The body of a block -/

/-- Whether an error of a block is no failed system call, or one whose error does not abort. -/
private def CallErrorOk (e : BlockError) : Prop :=
  ∀ address x, e = .systemCallFailed address x → x.aborts = false

/-- A checked system call fails only with an error of its call that does not abort. -/
private theorem errorsMeet_checkedSystemCall (env : BlockEnvironment fork)
    (block : State.BlockState) (target : Address) (data : ByteArray) :
    ErrorsMeet CallErrorOk (checkedSystemCall env block target data) := by
  intro e h address x he
  subst he
  obtain ⟨-, -, out, hout, herr⟩ := checkedSystemCall_eq_systemCallFailed_iff.mp h
  exact error_systemCall hout herr

/-- A transaction never fails for a system call. -/
private theorem errorsMeet_applyTransaction {env : BlockEnvironment fork} {index : Nat}
    {before : BodyOutput fork} (tx : Transaction) :
    ErrorsMeet CallErrorOk (applyTransaction env index before tx) := by
  unfold applyTransaction
  refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ _ h => by cases h) fun _ _ => ?_
  refine ErrorsMeet.bind (ErrorsMeet.aborted fun _ _ _ _ h => by cases h) fun _ _ => ?_
  refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ _ h => by cases h) fun _ _ => ?_
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.pure _) fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.bind (ErrorsMeet.map _ (ErrorsMeet.mapError fun _ _ _ _ h => by cases h))
      fun _ _ => ErrorsMeet.pure _

/-- The transactions of a block never fail for a system call. -/
private theorem errorsMeet_applyTransactions {env : BlockEnvironment fork} {body : BodyState}
    (transactions : List Transaction) :
    ErrorsMeet CallErrorOk (applyTransactions env body transactions) := fun _ h =>
  foldlM_error_of_step (fun _ : BodyOutput fork => True) CallErrorOk
    (fun _ _ _ _ _ => trivial) (fun _ _ e _ h => errorsMeet_applyTransaction _ e h)
    (b := ⟨body, .zero, 0, [], []⟩) trivial h

/-- A request read fails for a system call only with an error that does not abort. -/
private theorem errorsMeet_readRequest {env : BlockEnvironment fork}
    {state : BodyState × List ByteArray} (contract : UInt8 × Address) :
    ErrorsMeet CallErrorOk (readRequest env state contract) := by
  unfold readRequest
  refine ErrorsMeet.bind (errorsMeet_checkedSystemCall _ _ _ _) fun _ _ => ?_
  exact ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ _ h => by cases h)
    fun _ _ => ErrorsMeet.pure _

/-- The request reads fail for a system call only with an error that does not abort. -/
private theorem errorsMeet_readRequests {env : BlockEnvironment fork} {body : BodyState} :
    ErrorsMeet CallErrorOk (readRequests env body) := by
  unfold readRequests
  split
  · intro _ h
    exact foldlM_error_of_step (fun _ : BodyState × List ByteArray => True) CallErrorOk
      (fun _ _ _ _ _ => trivial) (fun _ c e _ h => errorsMeet_readRequest c e h) trivial h
  · exact ErrorsMeet.ok _

/-- The requests of a block fail for a system call only with an error that does not abort. -/
private theorem errorsMeet_blockRequests {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} (logs : List Log) :
    ErrorsMeet CallErrorOk (blockRequests depositContract env body logs) := by
  unfold blockRequests
  split
  · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.bind errorsMeet_readRequests fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.pure _

/-- The hash of the block access list never fails for a system call. -/
private theorem errorsMeet_accessListHashOf (body : BodyState) (gasLimit : Nat) :
    ErrorsMeet CallErrorOk (accessListHashOf fork body gasLimit) := by
  unfold accessListHashOf
  split
  · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.map _ (ErrorsMeet.mapError fun _ _ _ _ h => by cases h)
  · exact ErrorsMeet.pure _

/-- The body of a block fails for a system call only with an error that does not abort. -/
private theorem errorsMeet_applyBody {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : State.BlockState} :
    ErrorsMeet CallErrorOk (applyBody config env block start) := by
  unfold applyBody
  refine ErrorsMeet.bind ?_ fun _ _ => ?_
  · unfold daoTransfer
    split
    · exact ErrorsMeet.onBlock fun _ _ _ _ h => by cases h
    · exact ErrorsMeet.pure _
  refine ErrorsMeet.bind (ErrorsMeet.aborted fun _ _ _ _ h => by cases h) fun _ _ => ?_
  refine ErrorsMeet.bind (errorsMeet_applyTransactions _) fun _ _ => ?_
  dsimp only
  split
  · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ _ h => by cases h) fun _ _ => ?_
    refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ _ _ h => by cases h) fun _ _ => ?_
    refine ErrorsMeet.bind (errorsMeet_blockRequests _) fun r _ => ?_
    obtain ⟨requested, requests⟩ := r
    refine ErrorsMeet.bind (ErrorsMeet.onBlock fun _ _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_accessListHashOf _ _) fun _ _ => ErrorsMeet.pure _
  · refine ErrorsMeet.bind (ErrorsMeet.pure _) fun b hb => ?_
    cases hb
    refine ErrorsMeet.bind (errorsMeet_blockRequests _) fun r _ => ?_
    obtain ⟨requested, requests⟩ := r
    refine ErrorsMeet.bind (ErrorsMeet.onBlock fun _ _ _ _ h => by cases h) fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_accessListHashOf _ _) fun _ _ => ErrorsMeet.pure _

/-! ## The transition -/

/-- A block fails for a system call that must succeed only with an error that does not abort. -/
theorem stateTransition_systemCallFailed {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {address : Address} {e : EvmError}
    (h : stateTransition chain block checkSeal = .error (.systemCallFailed address e)) :
    e.aborts = false :=
  errorsMeet_stateTransition_of_plain (P := CallErrorOk)
    (fun _ _ _ hc _ address x he => absurd he (hc address x))
    (fun _ _ _ h => by cases h) (fun _ => errorsMeet_applyBody) _ h address e rfl

/-- A block never fails for a system call that must succeed with an error of the state. -/
theorem stateTransition_ne_systemCallFailed_state {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {address : Address}
    {error : State.StateError} :
    stateTransition chain block checkSeal ≠ .error (.systemCallFailed address (.state error)) :=
  fun h => by cases stateTransition_systemCallFailed h

end EthLib.Execution.Blocks
