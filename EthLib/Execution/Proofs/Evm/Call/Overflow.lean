module

public import EthLib.Execution.Proofs.Evm.Call.Funded
public import EthLib.Execution.Proofs.Evm.Call.Supply

/-!
# Proofs: no call or creation overflows a balance when the supply leaves room

A credit fails when the balance it raises would reach `2^256`.

A message credits a balance in two places: the move of its value, and SELFDESTRUCT.

The move of a value takes the value from the caller first.

So the target ends with at most what two distinct balances hold, which is at most the supply.

From Cancun, SELFDESTRUCT moves the balance of its account like a value, by [EIP-6780][e6780].

Before Cancun, it first credits the beneficiary, then sets the balance of its account to 0.

So an account that is its own beneficiary first doubles its balance.

A supply below `2^255` leaves room for that, and a supply below `2^256` leaves room for a move.

No step raises the supply, and a frame that fails gives back the supply of its start.

So every frame of a message has at most the supply that the message starts with.

So no call or creation fails for a balance that would overflow, when that supply leaves room.

[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Whether a supply of `supply` wei leaves room for every credit of a message at `fork`.

Before Cancun, twice the supply must be below `2^256`, for a SELFDESTRUCT to its own account.

From Cancun, the supply itself must be below `2^256`. -/
def SupplyRoom (fork : Fork) (supply : Nat) : Prop :=
  (if fork < .dencun then 2 * supply else supply) < 2 ^ 256

/-- A smaller supply leaves room when a larger one does. -/
theorem SupplyRoom.mono {supply supply' : Nat} (h : supply' ≤ supply)
    (room : SupplyRoom fork supply) : SupplyRoom fork supply' := by
  unfold SupplyRoom at *
  by_cases hf : fork < .dencun <;> simp only [hf, ↓reduceIte] at room ⊢ <;> omega

/-- A supply that leaves room is below `2^256`. -/
theorem SupplyRoom.lt {supply : Nat} (room : SupplyRoom fork supply) : supply < 2 ^ 256 := by
  unfold SupplyRoom at room
  split at room <;> omega

/-- The transfer of the balance of SELFDESTRUCT never overflows when the supply leaves room.

Before Cancun, the beneficiary gains the balance of the account.

So it ends with at most twice the supply. -/
private theorem selfdestructTransfer_ne_balanceOverflow {tx : TransactionState}
    (room : SupplyRoom fork tx.supply) (originator beneficiary address : Address) :
    selfdestructTransfer fork tx originator beneficiary ≠ .error (.balanceOverflow address) := by
  intro h
  unfold selfdestructTransfer at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
    · exact TransactionState.moveEther_ne_balanceOverflow room.lt _ _ _ address h
    · split at h
      · cases TransactionState.modifyState_eq_error.mp h
      · cases h
  · rename_i hdencun
    rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
    · refine TransactionState.createEther_ne_balanceOverflow ?_ address h
      have := TransactionState.balanceOf_le_supply tx originator
      unfold TransactionState.balanceOf at this
      unfold SupplyRoom at room
      simp only [show fork < .dencun from Nat.lt_of_not_ge hdencun, ↓reduceIte] at room
      omega
    · cases TransactionState.modifyState_eq_error.mp h

/-- No step overflows a balance when the supply of its frame leaves room. -/
theorem step_ne_balanceOverflow [LawfulGasMeter Meter] {evm : Evm fork Meter}
    (room : SupplyRoom fork evm.state.supply) (address : Address) :
    step fork evm ≠ .error (.state (.balanceOverflow address)) := by
  intro h
  obtain ⟨tx, beneficiary, same, h⟩ := step_eq_balanceOverflow h
  rw [← TransactionState.supply_eq_of_sameOutside same] at room
  exact selfdestructTransfer_ne_balanceOverflow room _ _ address h

/-- A run of a frame never overflows a balance when the supply of its frame leaves room.

The bound `supply` leaves room, and the frame holds at most that supply.

Each call or creation that the runner runs with at most that supply must never overflow.

Each message that the runner completes must keep or lower the supply. -/
private theorem runFrame_ne_balanceOverflow [LawfulGasMeter Meter] {bound supply : Nat}
    {runChild : MessageRunner fork Meter bound} (room : SupplyRoom fork supply)
    (never : ∀ caller message lt, caller.state.supply ≤ supply →
      ∀ address, runChild caller message lt ≠ .error (.state (.balanceOverflow address)))
    (keeps : ∀ caller message lt ended, runChild caller message lt = .ok ended →
      ended.val.state.supply ≤ caller.state.supply)
    {evm : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (le : evm.state.supply ≤ supply) (address : Address) :
    runFrame (step fork) (step_decreases fork) bound runChild evm within ≠
      .error (.state (.balanceOverflow address)) := by
  have T := stepRules_supplyLe (fork := fork) (Meter := Meter)
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 _ _ hstep _ =>
    intro h
    cases h
    exact step_ne_balanceOverflow (room.mono le) address hstep
  case case3 hstep _ ih => exact ih (Nat.le_trans (T.step hstep).1 le)
  case case4 hstep _ _ ran =>
    intro h
    cases h
    exact never _ _ _ (Nat.le_trans (T.step hstep).1.1 le) address ran
  case case5 hstep _ _ _ _ _ resumed _ =>
    intro h
    cases h
    exact resume_ne_state hstep _ resumed
  case case7 hstep _ _ _ ran _ resumed _ ih =>
    refine ih ?_
    rw [(sameContext_of_step_eq_child hstep resumed).state, state_incorporateChild]
    exact Nat.le_trans (keeps _ _ _ _ ran) (Nat.le_trans (T.step hstep).1.1 le)
  all_goals nofun

/-- No call or creation overflows a balance when the supply it starts with leaves room.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_ne_balanceOverflow_of_gas [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      SupplyRoom fork state.supply → ∀ address,
        processMessage fork message state substate meter held ≠
          .error (.state (.balanceOverflow address))) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      SupplyRoom fork state.supply → ∀ address,
        processCreateMessage fork message state substate meter held ≠
          .error (.state (.balanceOverflow address))) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    -- Each message that a frame sends has less gas, so the induction covers it.
    have never : ∀ (caller : Evm fork Meter) (child : Message fork), child.gas < n →
        SupplyRoom fork caller.state.supply → ∀ address,
        (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) ≠ .error (.state (.balanceOverflow address)) := by
      intro caller child lt room address h
      split at h
      · exact (ih child.gas lt).1 child _ _ _ _ rfl room address h
      · exact (ih child.gas lt).2 child _ _ _ _ rfl room address h
    have keeps : ∀ (caller : Evm fork Meter) (child : Message fork) ended, (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) = .ok ended → ended.val.state.supply ≤ caller.state.supply := by
      intro caller child ended h
      split at h
      · exact (supplyLe_processMessage h).1
      · exact (supplyLe_processCreateMessage h).1
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        SupplyRoom fork state.supply → ∀ address,
        processMessage fork message state substate meter held ≠
          .error (.state (.balanceOverflow address)) := by
      intro message state substate meter held hn room address h
      rw [processMessage] at h
      simp only [Except.map] at h
      split at h
      · rename_i hdo
        cases h
        -- The frame starts with the supply of the message, so its run never overflows.
        have ran : ∀ {entry : TransactionState}, entry.supply ≤ state.supply →
            ∀ {e} {substate' : Substate}
            (h : runFrame (step fork) (step_decreases fork) message.gas
              (fun caller child _ => match child.target with
                | some _ => processMessage fork child caller.state caller.substate.child
                | none => processCreateMessage fork child caller.state caller.substate.child)
              (startFrame message entry substate' meter) held = .error e),
            e ≠ .state (.balanceOverflow address) := fun entered _ _ hrun he => by
          subst he
          exact runFrame_ne_balanceOverflow room
            (fun caller child lt le => never caller child (hn ▸ lt) (room.mono le))
            (fun caller child _ ended ran => keeps caller child ended ran) entered address hrun
        have started := supply_startState message state
        split at hdo
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · cases hx : (startState fork message state).moveEther fork message.caller
              message.currentTarget message.value with
            | ok a => rw [hx] at hm; cases hm
            | error e' =>
              rw [hx] at hm
              cases hm
              exact TransactionState.moveEther_ne_balanceOverflow (started ▸ room.lt) _ _ _
                address hx
          have entered := (TransactionState.supply_moveEther
            (Base.mapError_ok_iff.mp hentry)).trans started
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran (Nat.le_of_eq entered) hrun rfl)
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · cases hm
          cases hentry
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran (Nat.le_of_eq started) hrun rfl)
      · cases h
    refine ⟨call, fun message state substate meter held hn room address h => ?_⟩
    rw [processCreateMessage] at h
    rcases Base.bind_eq_error h with hp | ⟨prepared, hprep, h⟩
    · unfold prepareCreation at hp
      split at hp
      · exact mapError_ne_of_isOk (State.TransactionState.incrementNonce_isOk _ _ _) _ hp
      · cases hp
    rcases Base.bind_eq_error h with hm | ⟨⟨evm, used⟩, -, h⟩
    · exact call message prepared substate meter held hn
        (by rwa [supply_prepareCreation hprep]) address hm
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

/-- No call overflows a balance when the supply it starts with leaves room. -/
theorem processMessage_ne_balanceOverflow [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (room : SupplyRoom fork state.supply)
    (address : Address) :
    processMessage fork message state substate meter held ≠
      .error (.state (.balanceOverflow address)) :=
  (processMessage_ne_balanceOverflow_of_gas message.gas).1 message state substate meter held rfl
    room address

/-- No creation overflows a balance when the supply it starts with leaves room. -/
theorem processCreateMessage_ne_balanceOverflow [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (room : SupplyRoom fork state.supply)
    (address : Address) :
    processCreateMessage fork message state substate meter held ≠
      .error (.state (.balanceOverflow address)) :=
  (processMessage_ne_balanceOverflow_of_gas message.gas).2 message state substate meter held rfl
    room address

end EthLib.Execution.Evm
