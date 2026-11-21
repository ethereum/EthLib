module

public import EthLib.Execution.Proofs.Transactions.Unfold
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
  rw [Transactions.processMessageCall_unfold] at h
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

/-- The leaves of a block body fail for a system call only with an error that does not abort.

Only a call to a request contract can fail that way. -/
private theorem leaves (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) :
    BodyLeaves config env block CallErrorOk (fun _ => True) (fun _ => True) (fun _ => True) where
  plain _ _ _ hc _ address x he := absurd he (hc address x)
  dao _ _ _ _ _ _ h := by cases h
  start _ _ _ _ _ _ h := by cases h
  inclusion _ _ _ _ _ _ _ _ h := by cases h
  process _ _ _ _ _ _ _ _ _ h := by cases h
  join _ _ _ _ _ _ _ h := by cases h
  withdraw _ _ _ _ _ _ _ h := by cases h
  code _ _ _ _ _ _ _ h := by cases h
  call _ _ _ _ _ _ _ _ h := by cases h
  call_failed _ _ _ _ _ hout _ he _ _ h := by cases h; exact error_systemCall hout he
  rewards _ _ _ _ _ _ h := by cases h

/-! ## The transition -/

/-- A block fails for a system call that must succeed only with an error that does not abort. -/
theorem stateTransition_systemCallFailed {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {address : Address} {e : EvmError}
    (h : stateTransition chain block checkSeal = .error (.systemCallFailed address e)) :
    e.aborts = false :=
  errorsMeet_stateTransition_of_plain (P := CallErrorOk)
    (fun _ _ _ hc _ address x he => absurd he (hc address x))
    (fun _ _ _ h => by cases h) (fun _ => (leaves _ _ _).errorsMeet_applyBody trivial) _ h
    address e rfl

/-- A block never fails for a system call that must succeed with an error of the state. -/
theorem stateTransition_ne_systemCallFailed_state {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {address : Address}
    {error : State.StateError} :
    stateTransition chain block checkSeal ≠ .error (.systemCallFailed address (.state error)) :=
  fun h => by cases stateTransition_systemCallFailed h

end EthLib.Execution.Blocks
