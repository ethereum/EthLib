module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Evm.Call.MessageCall
public import EthLib.Execution.Proofs.Evm.Call.StaticStep

/-!
# Proofs: a message in a frame that must not change the state

A message that is static and is a call leaves the state as it was, up to the records of its reads.

The account, the storage and the transient storage of every address read as before.

That holds from Paris, whatever the code of the message does, however deep its calls.

The message runs code at an account that holds code, when it has code.

A value that it sends goes to its own sender, whose account holds code.

A message that fails rolls back to its start, so the statement holds for it too.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (EMPTY_CODE_HASH)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- A change of an account keeps the block of the state. -/
theorem parent_modifyState {fork : Fork} {tx tx' : State.TransactionState} {address : Address}
    {f : State.Account → Except State.StateError State.Account}
    (h : tx.modifyState fork address f = .ok tx') : tx'.parent = tx.parent := by
  obtain ⟨account, -, rfl⟩ := State.TransactionState.modifyState_eq_ok_iff.mp h
  split <;> rfl

omit [GasMeter Meter] in
/-- A move of ether keeps the block of the state. -/
theorem parent_moveEther {fork : Fork} {tx tx' : State.TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') : tx'.parent = tx.parent := by
  unfold State.TransactionState.moveEther at h
  cases h1 : tx.modifyState fork sender (State.Account.debit sender amount) with
  | error e => simp [h1, bind, Except.bind] at h
  | ok mid =>
    rw [h1] at h
    exact (parent_modifyState h).trans (parent_modifyState h1)

/-- A precompile is a static step. -/
theorem staticStep_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : StaticStep evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact staticStep_exceptionalHalt _ _
  · split at h
    · cases h
      exact staticStep_exceptionalHalt _ _
    · cases h
      exact ⟨StateKept.refl _, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- The frame that starts a static message is a static frame. -/
theorem StaticFrame.start {state : State.TransactionState} {message : Message fork}
    (h : StaticMessage state message) (substate : Substate) (meter : Meter) :
    StaticFrame (startFrame message state substate meter) :=
  ⟨h.1, rfl, h.2.2.1⟩

omit [GasMeter Meter] in
/-- A message that a state may send, from a state that differs from it only by reads. -/
theorem StaticMessage.of_sameOutside {state state' : State.TransactionState}
    {message : Message fork}
    (so : State.TransactionState.SameOutside [] state state') (h : StaticMessage state message) :
    StaticMessage state' message := by
  have acc : ∀ a, state'.getAccount a = state.getAccount a := fun a => by
    have := (so a (by simp)).1
    simp [State.TransactionState.getAccount, this]
  obtain ⟨m1, m2, m3, m4⟩ := h
  refine ⟨m1, m2, fun nonempty => ?_, fun t v => ?_⟩
  · rw [acc]; exact m3 nonempty
  · obtain ⟨c, hc⟩ := m4 t v
    exact ⟨c, by rw [acc]; exact hc⟩

/-- A message in a static frame leaves the state as it was, up to the records of its reads.

It also keeps the block of the state.

It is the induction on the gas of the message that the theorem below states for one message. -/
theorem processMessage_static [LawfulGasMeter Meter] (hfork : .paris ≤ fork) :
    ∀ (n : Nat) (message : Message fork) (state : State.TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas),
      message.gas = n → StaticMessage state message →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        State.TransactionState.SameOutside [] state ended.val.state ∧
          ended.val.state.parent = state.parent := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro message state substate meter held hn hmsg ended h
    rw [processMessage] at h
    obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hfork, ite_false] at hdo
    split at hdo
    all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
    all_goals
      have hS1 : State.TransactionState.SameOutside [] state state1 ∧
          state1.parent = state.parent ∧ StaticMessage state1 message := by
        first
        | (have ht := ‹message.shouldTransferValue = true ∧ message.value ≠ 0›
           have hm' := Base.mapError_ok_iff.mp hm
           obtain ⟨hcaller, hcode⟩ := hmsg.2.2.2 ht.1 ht.2
           rw [hcaller] at hm'
           have so := State.TransactionState.sameOutside_moveEther_self hcode hm'
           exact ⟨so, parent_moveEther hm', StaticMessage.of_sameOutside so hmsg⟩)
        | (cases hm
           exact ⟨State.TransactionState.SameOutside.refl _ _, rfl, hmsg⟩)
    all_goals
      obtain ⟨hso, hpar, hmsg1⟩ := hS1
      have core : State.TransactionState.SameOutside [] state ended0.val.state ∧
          ended0.val.state.parent = state.parent := by
        have conclude : State.TransactionState.SameOutside [] state1 ended0.val.state →
            ended0.val.state.parent = state1.parent →
            State.TransactionState.SameOutside [] state ended0.val.state ∧
              ended0.val.state.parent = state.parent :=
          fun so par => ⟨hso.trans so, par.trans hpar⟩
        rcases hpa : precompileAddress fork message with _ | addr
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
          · rename_i after hrun
            cases hdo
            have hst := staticStep_runFrame (hf := StaticFrame.start hmsg1 _ _) (h := hrun)
              (fun {evm' after'} hf' hstep =>
                staticResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
              (fun {evm' caller' message' resume'} hf' hstep =>
                staticResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
              (by
                intro caller' message' lt c used hf' hm hrun'
                split at hrun'
                · exact ih message'.gas (by omega) message' caller'.state _ _ _ rfl hm ⟨c, used⟩
                    hrun'
                · have := hm.2.1
                  simp_all)
            exact conclude hst.state hst.parent
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            exact conclude (State.TransactionState.SameOutside.refl _ _) rfl
          · split at hdo
            · rename_i after hrp
              cases hdo
              exact conclude (staticStep_runPrecompile hrp).state
                (staticStep_runPrecompile hrp).parent
            · cases hdo
              exact conclude (State.TransactionState.SameOutside.refl _ _) rfl
      have hval := congrArg Subtype.val rolled
      simp only at hval
      rw [← hval]
      unfold rollbackOnError
      split
      · exact ⟨State.TransactionState.sameOutside_restoreTxState core.2, core.2⟩
      · exact core

/-- A static message that is a call changes no address of the state, up to the records of reads.

From Paris, the account, storage and transient storage of every address read as before.

That holds whatever its code does, however deep its calls.

The message must be static and be a call, not a creation.

Its code, when it has any, runs at an account that holds code.

A value that it sends goes to its own sender, whose account holds code.

A message with no value, as STATICCALL sends, satisfies the last condition without a premise.

Before Paris a call touches the account that it calls, so the statement does not cover it. -/
theorem processMessage_sameOutside_static [LawfulGasMeter Meter] (hfork : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hmsg : StaticMessage state message) {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    State.TransactionState.SameOutside [] state ended.val.state :=
  (processMessage_static hfork message.gas message state substate meter held rfl hmsg ended h).1

end EthLib.Execution.Evm
