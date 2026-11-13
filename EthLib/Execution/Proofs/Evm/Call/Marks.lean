module

public import EthLib.Execution.Proofs.Evm.Call.StepRules
public import EthLib.Execution.Proofs.Evm.Call.ToDelete

/-!
# Proofs: a frame keeps its accounts to delete, and a child without an error passes them on

SELFDESTRUCT can mark the account that runs it for deletion, in the substate of its frame.

From Cancun, it marks that account only when the transaction created it.

No write removes an account from that set, so a frame keeps its marks until it ends.

A child starts with the marks of its caller.

A child that ends without an error passes its marks to its caller.

By definition, a child that ends with an error passes none, and its caller keeps its own.

A call to code starts its frame from the state and the substate that it enters.

A creation does so once it prepares its account.

These facts hold at every fork.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The relation -/

/-- Every account that the first frame marks for deletion, the second marks too. -/
def ToDeleteLe (evm after : Evm fork Meter) : Prop :=
  ∀ address ∈ evm.substate.accountsToDelete, address ∈ after.substate.accountsToDelete

/-- Each write of a step keeps every account to delete. -/
theorem stepRules_toDeleteLe : StepRules fork (ToDeleteLe (fork := fork) (Meter := Meter)) where
  trans hab hbc x hx := hbc x (hab x hx)
  static h x hx := h.toDelete ▸ hx
  sstore _ _ _ _ _ _ _ _ hx := hx
  tstore _ _ _ _ _ hx := hx
  log _ _ hsub _ _ x hx := by rw [hsub]; exact hx
  selfdestruct _ _ h := by
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      intro x hx
      dsimp only
      split
      · exact Std.ExtTreeSet.mem_insert.mpr (.inr hx)
      · exact hx
  incrementNonce _ _ _ _ _ _ hx := hx
  incorporate _ _ hx := mem_accountsToDelete_incorporateChild.mpr (.inl hx)

/-- Every call and creation that returns a frame keeps the accounts to delete of its start.

That holds whether or not the message ends with an error.

The gas `n` of the message is a parameter, so that the proof can go by strong induction on it. -/
theorem toDeleteLe_processMessage_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ∀ address ∈ substate.accountsToDelete,
          address ∈ ended.val.substate.accountsToDelete) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ∀ address ∈ substate.accountsToDelete,
          address ∈ ended.val.substate.accountsToDelete) :=
  stepRules_toDeleteLe.processMessage
    (M := fun _ _ substate _ ended =>
      ∀ address ∈ substate.accountsToDelete, address ∈ ended.substate.accountsToDelete)
    (fun {message state _ substate _ _ ended} hentry hd x hx => by
      rw [(createdAccounts_rollbackOnError state ended).2]
      refine hd x ?_
      rcases hentry with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact hx
      · exact hx)
    (fun _ hm hd x hx => by
      rw [(createdAccounts_depositCode hd).2]
      exact hm x hx)
    (fun h => h) n

/-! ## A child that ends without an error -/

/-- A caller that takes in a child without an error marks every account that the child marks. -/
theorem toDeleteLe_incorporateChild {caller child : Evm fork Meter} (ok : child.error = none) :
    ToDeleteLe child (incorporateChild fork caller child) := by
  intro _ hx
  exact mem_accountsToDelete_incorporateChild.mpr (.inr ⟨ok, hx⟩)

/-- A caller that resumes after a call without an error marks every account the child marks. -/
theorem toDeleteLe_resumeCall {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after)
    (ok : child.error = none) : ToDeleteLe child after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  intro x hx
  show x ∈ e.substate.accountsToDelete
  rw [(pushWord_sameContext h1).substate]
  simp only [ok, Option.isNone_none, ↓reduceIte]
  exact toDeleteLe_incorporateChild ok x hx

/-- A creator that resumes after a creation without an error marks every account the child marks. -/
theorem toDeleteLe_resumeCreate {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after)
    (ok : child.error = none) : ToDeleteLe child after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  intro x hx
  show x ∈ e.substate.accountsToDelete
  rw [(pushWord_sameContext h1).substate]
  simp only [ok, Option.isNone_none, ↓reduceIte]
  exact toDeleteLe_incorporateChild ok x hx

/-- A frame that resumes after a message without an error marks every account that the child marks.

The message is the one that a step of a frame sends. -/
theorem toDeleteLe_resume {evm caller child after : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (sent : step fork evm = .ok (.child caller message resume))
    (resumed : resume child = .ok after) (ok : child.error = none) :
    ToDeleteLe child after := by
  rcases step_eq_child_resume sent with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact toDeleteLe_resumeCall resumed ok
  · exact toDeleteLe_resumeCreate resumed ok

/-! ## The frame that the code of a message starts from -/

/-- The frame `start` is the frame that the code of a message starts from, after its entry.

The message runs from the state `state`, the substate `substate` and the meter `meter`.

It goes to no precompile, and its frame starts from the state and the substate it enters. -/
def FrameStarts (fork : Fork) (message : Message fork) (state : TransactionState)
    (substate : Substate) (meter : Meter) (start : Evm fork Meter) : Prop :=
  precompileAddress fork message = none ∧
    ∃ entry entrySubstate, Entered fork message state substate entry entrySubstate ∧
      start = startFrame message entry entrySubstate meter

/-- The frame `start` is the frame that the code of a message starts from.

A call runs its code from the state `state`.

A creation first prepares its account in that state, and runs its init code from the result. -/
def CodeStarts (fork : Fork) (message : Message fork) (state : TransactionState)
    (substate : Substate) (meter : Meter) (start : Evm fork Meter) : Prop :=
  match message.target with
  | some _ => FrameStarts fork message state substate meter start
  | none => ∃ prepared, prepareCreation fork state message.currentTarget = .ok prepared ∧
      FrameStarts fork message prepared substate meter start

/-! ## Messages -/

/-- A rollback that leaves no error had no error to roll back. -/
theorem error_rollbackOnError {snapshot : TransactionState} {evm : Evm fork Meter}
    (ok : (rollbackOnError snapshot evm).error = none) : evm.error = none := by
  unfold rollbackOnError at ok
  split at ok <;> exact ok

/-- A deposit of code that leaves no error follows init code that left none. -/
theorem error_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) (ok : after.error = none) :
    evm.error = none := by
  unfold depositCode at h
  split at h
  · cases h
    exact ok
  · rename_i hs
    simpa using hs

end EthLib.Execution.Evm
