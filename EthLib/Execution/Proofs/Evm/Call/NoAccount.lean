module

public import EthLib.Execution.Proofs.Evm.Call.Settled
public import EthLib.Execution.Proofs.Evm.Call.Funded

/-!
# Proofs: no creation, and no hosted call, fails to write storage for lack of an account

SSTORE writes the storage of the address its frame runs at, and fails when it has no account.

A frame runs an instruction only when it has code.

A call with code runs at an account that holds code, or at the account of the frame that calls it.

A creation runs at its new address, which has an account once the creation starts.

From Spurious Dragon it holds a nonce of at least 1, and before Paris its start touches it.

Every step, call and creation keeps the settled accounts, so the frame keeps its account.

So no creation fails for a write of storage at an address with no account.

Nor does a call that runs with code only at a settled address.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Whether a message with code runs at an address that is settled in a state. -/
def Hosts (fork : Fork) (message : Message fork) (state : TransactionState) : Prop :=
  message.code.size ≠ 0 → Settled fork state message.currentTarget

/-! ## A run of a frame -/

/-- Whether a frame with code runs at an address that is settled in its state. -/
private def FrameHosts (evm : Evm fork Meter) : Prop :=
  evm.code.size ≠ 0 → Settled fork evm.state evm.message.currentTarget

omit [GasMeter Meter] in
/-- A frame related to one that runs at a settled address runs at a settled address too.

The relation keeps the settled accounts, the message and the code. -/
private theorem FrameHosts.of_rel {a b : Evm fork Meter} (h : FrameHosts a)
    (r : SettledLe fork a.state b.state ∧ b.message = a.message ∧ b.code = a.code) :
    FrameHosts b := fun hs => by
  rw [r.2.1]
  exact r.1 _ (h (r.2.2 ▸ hs))

/-- A frame with no code takes a step that only stops it. -/
private theorem step_of_size_eq_zero {evm : Evm fork Meter} (h : evm.code.size = 0) :
    step fork evm = .ok (.next (advance { evm with running := false })) :=
  step_of_size_le (by omega)

/-- A step from a frame that runs at a settled address never fails for no account. -/
private theorem step_ne_noAccount [LawfulGasMeter Meter] {evm : Evm fork Meter}
    (hosts : FrameHosts evm) (address : Address) :
    step fork evm ≠ .error (.state (.noAccount address)) := by
  intro h
  rcases step_eq_error_state h with ⟨_, h1⟩ | ⟨-, hnone⟩ | ⟨_, h1⟩
  · cases h1
  · have hsize : evm.code.size ≠ 0 := fun h0 => by
      rw [step_of_size_eq_zero h0] at h
      cases h
    obtain ⟨account, ha, -⟩ := hosts hsize
    rw [ha] at hnone
    cases hnone
  · cases h1

/-- Each call that a step sends runs with code only at a settled address.

The step must start from a frame that runs at a settled address. -/
private theorem step_eq_child_hosts {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} (hosts : FrameHosts evm)
    (h : step fork evm = .ok (.child caller message resume)) (call : message.target ≠ none) :
    Hosts fork message caller.state := by
  intro hsize
  have r := ((stepRules_settledLe.and stepRules_messageCode).step h).1
  have hev : evm.code.size ≠ 0 := fun h0 => by
    rw [step_of_size_eq_zero h0] at h
    cases h
  rcases step_eq_child_staticCode h call with heq | hstatic
  · rw [heq]
    exact r.1 _ (hosts hev)
  · exact r.1 _ (settled_of_getAccount (.inr (hstatic hsize)))

/-- A run of a frame that runs at a settled address never fails for no account.

Each call that the runner runs with code only at a settled address must never fail that way.

So must each creation that it runs.

Each message that the runner completes must keep every settled account. -/
private theorem runFrame_ne_noAccount [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (never : ∀ caller message lt, (message.target ≠ none → Hosts fork message caller.state) →
      ∀ address, runChild caller message lt ≠ .error (.state (.noAccount address)))
    (keeps : ∀ caller message lt ended, runChild caller message lt = .ok ended →
      SettledLe fork caller.state ended.val.state)
    {evm : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hosts : FrameHosts evm) (address : Address) :
    runFrame (step fork) (step_decreases fork) bound runChild evm within ≠
      .error (.state (.noAccount address)) := by
  have T := stepRules_settledLe (fork := fork) (Meter := Meter) |>.and stepRules_messageCode
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 _ _ hstep _ =>
    intro h
    cases h
    exact step_ne_noAccount hosts address hstep
  case case3 hstep _ ih => exact ih (hosts.of_rel (T.step hstep))
  case case4 hstep _ _ ran =>
    intro h
    cases h
    exact never _ _ _ (step_eq_child_hosts hosts hstep) address ran
  case case5 hstep _ _ _ _ _ resumed _ =>
    intro h
    cases h
    exact resume_ne_state hstep _ resumed
  case case7 hstep _ _ _ ran _ resumed _ ih =>
    refine ih (hosts.of_rel ⟨?_, ?_, ?_⟩)
    · rw [(sameContext_of_step_eq_child hstep resumed).state, state_incorporateChild]
      exact (T.step hstep).1.1.trans (keeps _ _ _ _ ran)
    · rw [(sameContext_of_step_eq_child hstep resumed).message, message_incorporateChild]
      exact (T.step hstep).1.2.1
    · rw [(sameContext_of_step_eq_child hstep resumed).code, code_incorporateChild]
      exact (T.step hstep).1.2.2
  all_goals nofun

/-! ## Calls and creations -/

/-- A change of an account never fails for no account when the change to the account never does. -/
private theorem modifyState_ne_noAccount {tx : TransactionState} {address other : Address}
    {f : State.Account → Except State.StateError State.Account}
    (hf : ∀ account, f account ≠ .error (.noAccount other)) :
    tx.modifyState fork address f ≠ .error (.noAccount other) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
  · exact hf _ h
  · dsimp only at h
    split at h <;> cases h

/-- A move of ether never fails for no account. -/
private theorem moveEther_ne_noAccount (tx : TransactionState) (sender recipient : Address)
    (amount : Base.U256) (address : Address) :
    (tx.moveEther fork sender recipient amount).mapError EvmError.state ≠
      .error (.state (.noAccount address)) := by
  intro h
  cases hx : tx.moveEther fork sender recipient amount with
  | ok a => rw [hx] at h; cases h
  | error e =>
    rw [hx] at h
    cases h
    rcases Base.bind_eq_error hx with h | ⟨a, -, h⟩
    · exact modifyState_ne_noAccount
        (fun _ => by unfold State.Account.debit; split <;> nofun) h
    · exact modifyState_ne_noAccount
        (fun _ => by unfold State.Account.credit; split <;> nofun) h

/-- No call or creation fails for a write of storage at an address with no account.

A call must run with code only at a settled address.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_ne_noAccount_of_gas [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n → Hosts fork message state →
      ∀ address, processMessage fork message state substate meter held ≠
        .error (.state (.noAccount address))) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ address, processCreateMessage fork message state substate meter held ≠
        .error (.state (.noAccount address))) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    -- Each message that a frame sends has less gas, so it never fails this way.
    have never : ∀ (caller : Evm fork Meter) (child : Message fork), child.gas < n →
        (child.target ≠ none → Hosts fork child caller.state) → ∀ address,
        (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) ≠ .error (.state (.noAccount address)) := by
      intro caller child lt hosts address h
      split at h
      · rename_i ht
        exact (ih child.gas lt).1 child _ _ _ _ rfl (hosts (by simp [ht])) address h
      · exact (ih child.gas lt).2 child _ _ _ _ rfl address h
    have keeps : ∀ (caller : Evm fork Meter) (child : Message fork) ended, (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) = .ok ended → SettledLe fork caller.state ended.val.state := by
      intro caller child ended h
      split at h
      · exact settledLe_processMessage h
      · exact settledLe_processCreateMessage h
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        Hosts fork message (startState fork message state) → ∀ address,
        processMessage fork message state substate meter held ≠
          .error (.state (.noAccount address)) := by
      intro message state substate meter held hn hosts address h
      rw [processMessage] at h
      simp only [Except.map] at h
      split at h
      · rename_i hdo
        cases h
        -- The frame starts at a settled address, so its run never fails this way.
        have ran : ∀ {entry : TransactionState},
            SettledLe fork (startState fork message state) entry → ∀ {e} {substate' : Substate}
            (h : runFrame (step fork) (step_decreases fork) message.gas
              (fun caller child _ => match child.target with
                | some _ => processMessage fork child caller.state caller.substate.child
                | none => processCreateMessage fork child caller.state caller.substate.child)
              (startFrame message entry substate' meter) held = .error e),
            e ≠ .state (.noAccount address) := fun entered _ _ hrun he => by
          subst he
          exact runFrame_ne_noAccount (fun caller child lt => never caller child (hn ▸ lt))
            (fun caller child _ ended ran => keeps caller child ended ran)
            (fun hs => entered _ (hosts hs)) address hrun
        split at hdo
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · exact moveEther_ne_noAccount _ _ _ _ address hm
          have entered := settledLe_moveEther (Base.mapError_ok_iff.mp hentry)
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran entered hrun rfl)
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · cases hm
          cases hentry
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran (SettledLe.refl _) hrun rfl)
      · cases h
    refine ⟨fun message state substate meter held hn hosts address => call message state substate
      meter held hn (fun hs => settledLe_startState message state _ (hosts hs)) address,
      fun message state substate meter held hn address h => ?_⟩
    rw [processCreateMessage] at h
    rcases Base.bind_eq_error h with hp | ⟨prepared, hprep, h⟩
    · unfold prepareCreation at hp
      split at hp
      · exact mapError_ne_of_isOk (State.TransactionState.incrementNonce_isOk _ _ _) _ hp
      · cases hp
    -- The new address has an account once the creation starts.
    have ready : Hosts fork message (startState fork message prepared) := fun _ => by
      unfold startState
      split
      · rename_i hlt
        obtain ⟨account, ha⟩ := Option.isSome_iff_exists.mp
          (State.TransactionState.isSome_getAccountOptional_touchAccount prepared
            message.currentTarget)
        exact ⟨account, ha, .inl hlt⟩
      · rename_i hge
        exact settled_of_getAccount (.inl (nonce_ne_zero_prepareCreation hprep
          (Nat.le_trans (by decide) (Nat.le_of_not_lt hge))))
    rcases Base.bind_eq_error h with hm | ⟨⟨evm, used⟩, -, h⟩
    · exact call message prepared substate meter held hn ready address hm
    split at h
    split at h
    · rename_i hdep
      cases h
      unfold depositCode at hdep
      dsimp only at hdep
      repeat' split at hdep
      all_goals first
        | (cases hdep; done)
        | (rcases Base.bind_eq_error hdep with hs | ⟨_, -, hs⟩
           · exact mapError_ne_of_isOk (State.TransactionState.setCode_isOk _ _ _ _) _ hs
           · cases hs)
    · cases h

/-- A call whose code runs only at a settled address never fails for no account.

That error comes only from a write of storage at an address with no account. -/
theorem processMessage_ne_noAccount [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (hosts : Hosts fork message state)
    (address : Address) :
    processMessage fork message state substate meter held ≠
      .error (.state (.noAccount address)) :=
  (processMessage_ne_noAccount_of_gas message.gas).1 message state substate meter held rfl hosts
    address

/-- No creation fails for a write of storage at an address with no account. -/
theorem processCreateMessage_ne_noAccount [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (address : Address) :
    processCreateMessage fork message state substate meter held ≠
      .error (.state (.noAccount address)) :=
  (processMessage_ne_noAccount_of_gas message.gas).2 message state substate meter held rfl address

end EthLib.Execution.Evm
