module

public import EthLib.Execution.Proofs.Evm.Call.ToDelete

/-!
# Proofs: from Paris, a message touches no account beyond those of its substate

From Spurious Dragon, a touched account that is empty goes at the end of its transaction.

[EIP-161][e161] sets this rule.

From Paris, no step touches an account.

From Paris, a caller keeps its own touched accounts, whether its child succeeds or fails.

So every call and creation that returns a frame touches no account beyond those it started with.

[e161]: https://eips.ethereum.org/EIPS/eip-161#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- From Paris, the end of a successful SELFDESTRUCT touches no account. -/
theorem touchedAccounts_finishSelfdestruct (hfork : .paris ≤ fork) {beneficiary : Address}
    {refund : Nat} {evm after : Evm fork Meter}
    (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.substate.touchedAccounts = evm.substate.touchedAccounts := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    dsimp only
    split
    · rename_i hc
      exact absurd hc.2.1 (Nat.not_lt.mpr hfork)
    · rfl

/-- From Paris, a caller that takes in its child keeps its own touched accounts. -/
theorem touchedAccounts_incorporateChild (hfork : .paris ≤ fork) (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).substate.touchedAccounts =
      caller.substate.touchedAccounts := by
  unfold incorporateChild
  split
  · show touchedOnSuccess fork caller child = _
    unfold touchedOnSuccess
    split
    · rename_i hc
      exact absurd hc.2 (Nat.not_lt.mpr hfork)
    · rfl
  · exact touchedOnError_of_outside (.inr hfork)

/-- From Paris, each write of a step touches no account. -/
theorem stepRules_touchedLe (hfork : .paris ≤ fork) :
    StepRules fork (fun a b : Evm fork Meter =>
      TouchedSubset b.substate.touchedAccounts a.substate.touchedAccounts) where
  trans hab hbc x hx := hab x (hbc x hx)
  static h x hx := h.touched ▸ hx
  sstore _ _ _ _ _ _ _ _ hx := hx
  tstore _ _ _ _ _ hx := hx
  log _ _ hsub x hx := by rw [hsub] at hx; exact hx
  selfdestruct _ _ h x hx := touchedAccounts_finishSelfdestruct hfork h ▸ hx
  incrementNonce _ _ _ _ _ hx := hx
  incorporate _ x hx := by rw [touchedAccounts_incorporateChild hfork] at hx; exact hx

/-- From Paris, every call and creation that returns a frame touches no new account.

Each account touched in that frame was touched in the substate the message started from.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem touchedAccounts_processMessage_induction [LawfulGasMeter Meter] (hfork : .paris ≤ fork)
    (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        TouchedSubset ended.val.substate.touchedAccounts substate.touchedAccounts) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        TouchedSubset ended.val.substate.touchedAccounts substate.touchedAccounts) :=
  (stepRules_touchedLe hfork).processMessage
    (M := fun _ _ substate _ ended =>
      TouchedSubset ended.substate.touchedAccounts substate.touchedAccounts)
    (fun {_ state _ _ _ _ ended} hentry hrun x hx => by
      rw [(createdAccounts_rollbackOnError state ended).2] at hx
      have hstart := hrun x hx
      rcases hentry with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact hstart)
    (fun _ hm hd x hx => hm x ((createdAccounts_depositCode hd).2 ▸ hx))
    (fun h x hx => absurd (h x hx) (by simp [Substate.child, Substate.empty]))
    n

/-- From Paris, a call that returns a frame touches no new account.

That holds whether or not the call ends with an error. -/
theorem touchedAccounts_processMessage [LawfulGasMeter Meter] (hfork : .paris ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    TouchedSubset ended.val.substate.touchedAccounts substate.touchedAccounts :=
  (touchedAccounts_processMessage_induction hfork message.gas).1 message state substate meter held
    rfl ended h

/-- From Paris, a creation that returns a frame touches no new account.

That holds whether or not the creation ends with an error. -/
theorem touchedAccounts_processCreateMessage [LawfulGasMeter Meter] (hfork : .paris ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    TouchedSubset ended.val.substate.touchedAccounts substate.touchedAccounts :=
  (touchedAccounts_processMessage_induction hfork message.gas).2 message state substate meter held
    rfl ended h

end EthLib.Execution.Evm
