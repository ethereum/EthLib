module

public import EthLib.Execution.Proofs.Evm.Call.AccessesGrow
public import EthLib.Execution.Proofs.Evm.Call.BurnRun

/-!
# Proofs: every frame that a run reaches keeps the accesses of its start

A run reaches the frames of its steps, and the frames of the messages it sends, at any depth.

Each of them holds every address and storage key that the start of the run accessed.

A message that fails drops only what it added, so its caller keeps the accesses of the start.

Source: [EIP-2929, Specification][eip2929].

[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The substate at the start of a run. -/
def BurnStart.substate : BurnStart fork Meter → Substate
  | .frame evm | .body evm => evm.substate
  | .call _ _ substate _ | .create _ _ substate _ => substate

/-- A message starts with every access of the caller that sends it. -/
theorem BurnStart.accessesLe_child (caller : Evm fork Meter) (message : Message fork) :
    caller.substate.AccessesLe (BurnStart.child caller message).substate := by
  unfold BurnStart.child
  split <;> exact Substate.accessesLe_child _

/-- A certified run ends with every access of its start. -/
theorem RunBurns.accessesLe {start : BurnStart fork Meter} {ended : Evm fork Meter}
    {log : BurnLog} (h : RunBurns fork Meter start ended log) :
    start.substate.AccessesLe ended.substate := by
  induction h with
  | stopped => exact .refl _
  | halt => exact .refl _
  | next _ step _ ih => exact (stepRules_accessesLe.step step).trans ih
  | child _ step _ resumed _ ihRun ihTail =>
    -- The caller takes in the frame that ends the message, which holds the caller's accesses.
    exact ((stepRules_accessesLe.step step).2 _ _ resumed
      ((BurnStart.accessesLe_child _ _).trans ihRun)).trans ihTail
  | failedResume => exact .refl _
  | bodyFrame _ _ ih => exact ih
  | skipPrecompile => exact .refl _
  | precompile _ _ h => exact (staticStep_runPrecompile h).accesses
  | call entered _ _ ih =>
    exact ((accessesLe_entered entered).trans ih).trans (accessesLe_rollbackOnError _ _)
  | createRollback _ _ deposit _ _ ih =>
    rw [(depositCode_cases deposit).1]
    exact ih
  | createKeep _ _ deposit _ ih =>
    rw [(depositCode_cases deposit).1]
    exact ih

/-- Every frame that a run reaches holds every access of the start of the run.

That holds through every nested message, including the frames after a message that failed. -/
theorem RunReaches.accessesLe {start : BurnStart fork Meter} {reached : Evm fork Meter}
    (h : RunReaches fork Meter start reached) : start.substate.AccessesLe reached.substate := by
  induction h with
  | here => exact .refl _
  | next _ step _ ih => exact (stepRules_accessesLe.step step).trans ih
  | childRun _ step _ ih =>
    exact (stepRules_accessesLe.step step).1.trans ((BurnStart.accessesLe_child _ _).trans ih)
  | childTail _ step run resumed _ ih =>
    exact ((stepRules_accessesLe.step step).2 _ _ resumed
      ((BurnStart.accessesLe_child _ _).trans run.accessesLe)).trans ih
  | body _ _ ih => exact ih
  | call entered _ ih => exact (accessesLe_entered entered).trans ih
  | create _ _ ih => exact ih

omit [GasMeter Meter] in
/-- An access to a storage key that the frame has accessed is warm. -/
theorem accessStorageKey_fst_of_mem {evm : Evm fork Meter} {address : Address} {key : Bytes32}
    (h : key ∈ evm.substate.accessedStorageKeys.getD address ∅) :
    (accessStorageKey evm address key).1 = false := by
  unfold accessStorageKey
  split <;> simp [h]

omit [GasMeter Meter] in
/-- An access to an address that the frame has accessed is warm. -/
theorem accessAddress_fst_of_mem {evm : Evm fork Meter} {address : Address}
    (h : address ∈ evm.substate.accessedAddresses) : (accessAddress evm address).1 = false := by
  unfold accessAddress
  split <;> simp [h]

end EthLib.Execution.Evm
