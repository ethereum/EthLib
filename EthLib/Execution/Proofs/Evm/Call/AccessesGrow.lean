module

public import EthLib.Execution.Proofs.Evm.Call.StepRules

/-!
# Proofs: a run never drops an access

From Berlin, a transaction records the addresses and the storage keys that it accessed.

Each step only adds to those records, and a message starts with the records of its caller.

So every run of a frame, every call and every creation ends with every access it started with.

Source: [EIP-2929, Specification][eip2929].

[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Each write of a step keeps every access of the substate. -/
theorem stepRules_accessesLe :
    StepRules fork (fun a b : Evm fork Meter => a.substate.AccessesLe b.substate) where
  trans hab hbc := hab.trans hbc
  static h := h.accesses
  sstore _ _ _ _ _ _ _ := ⟨fun _ h => h, fun _ _ h => h⟩
  tstore _ _ _ _ := .refl _
  log _ _ hsub _ _ := by
    rw [hsub]
    exact ⟨fun _ h => h, fun _ _ h => h⟩
  -- SELFDESTRUCT changes the accounts to delete, the logs, the refund and the touched accounts.
  selfdestruct _ _ h := by
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact ⟨fun _ h => h, fun _ _ h => h⟩
  incrementNonce _ _ _ _ _ := .refl _
  -- A child that succeeds passes on its accesses, and one that fails passes on none.
  incorporate h := by
    unfold incorporateChild
    split
    · exact ⟨h.addresses, h.storageKeys⟩
    · exact ⟨fun _ h => h, fun _ _ h => h⟩

/-- A message starts from a substate with every access of the substate of its caller. -/
theorem Substate.accessesLe_child (substate : Substate) : substate.AccessesLe substate.child :=
  ⟨fun _ h => h, fun _ _ h => h⟩

/-- The substate that a message enters holds every access of the substate it is sent with. -/
theorem accessesLe_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    substate.AccessesLe entrySubstate := by
  rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .refl _
  · exact ⟨fun _ h => h, fun _ _ h => h⟩

/-- A rollback keeps every access of the frame that it undoes. -/
theorem accessesLe_rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) :
    evm.substate.AccessesLe (rollbackOnError snapshot evm).substate := by
  unfold rollbackOnError
  split <;> exact .refl _

/-- Every call and creation that ends keeps every access of the substate it is sent with.

That holds at every fork, whether its frame ends with an error or not.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_accessesLe [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        substate.AccessesLe ended.val.substate) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        substate.AccessesLe ended.val.substate) :=
  stepRules_accessesLe.processMessage
    (M := fun _ _ substate _ ended => substate.AccessesLe ended.substate)
    (fun hentry hrun =>
      ((accessesLe_entered hentry).trans hrun).trans (accessesLe_rollbackOnError _ _))
    (fun _ hm hd => by
      rw [(depositCode_cases hd).1]
      exact hm)
    (fun h => (Substate.accessesLe_child _).trans h) n

/-- A call that ends keeps every access of the substate it is sent with, even if its frame fails.

The caller always keeps them, and it gains what the call adds only when the call succeeds. -/
theorem accessesLe_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    substate.AccessesLe ended.val.substate :=
  (processMessage_accessesLe message.gas).1 message state substate meter held rfl ended h

/-- A creation that ends keeps every access of the substate it is sent with, even if it fails.

The caller always keeps them, and it gains what the creation adds only when it succeeds. -/
theorem accessesLe_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    substate.AccessesLe ended.val.substate :=
  (processMessage_accessesLe message.gas).2 message state substate meter held rfl ended h

end EthLib.Execution.Evm
