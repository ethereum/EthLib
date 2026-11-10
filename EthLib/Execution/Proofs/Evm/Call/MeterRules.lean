module

public import EthLib.Execution.Proofs.Evm.Call.MeterSteps

/-!
# Proofs: a relation that every meter operation keeps holds across each message

A frame changes its meter only through the operations of the meter.

So a relation that each operation keeps holds across every successful message.

It relates the meter that the message starts with to the meter of the frame that ends it.

It must hold for any child of an absorb, so a frame needs no fact about its messages.

For the meter of [EIP-8037][eip8037], the starting reservoir and the committed spill stay the same.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

namespace MeterRules

variable {Q : Meter → Meter → Prop}

/-- Each step keeps the relation from the meter of its frame to the meter of each frame after it.

That holds of the frame that sends a message, and of the frame that resumes from any child. -/
theorem step (rules : MeterRules Q) {C : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    {evm : Evm fork Meter} {result : StepResult fork Meter} (h : step fork evm = .ok result) :
    StepResult.Keeps (fun a b => Q a.gas b.gas) C evm result := by
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hrun
        obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
        exact rules.instruction_keeps hrun hr
      · split at h
        · exact rules.messageInstruction_keeps ‹_› h
        · cases h
  · obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
    cases hr
    exact rules.refl _

/-- A successful run of a frame keeps the relation, whatever runs its messages. -/
theorem runFrame (rules : MeterRules Q) [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (Evm.step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    Q evm.gas after.gas :=
  rel_runFrame (R := fun a b => Q a.gas b.gas) (C := fun _ _ _ => True) (Inv := fun _ => True)
    (fun evm => rules.refl evm.gas) rules.trans (fun _ _ => trivial)
    (fun evm _ _ => rules.exhaust evm.gas) (fun _ h => rules.step h)
    (fun _ _ _ _ _ _ => trivial) trivial h

/-- A precompile keeps the relation. -/
theorem runPrecompile (rules : MeterRules Q) {address : Nat} {evm after : Evm fork Meter}
    (h : Evm.runPrecompile fork address evm = some after) : Q evm.gas after.gas := by
  unfold Evm.runPrecompile at h
  split at h
  · cases h
  · cases h
    exact rules.exhaust evm.gas
  · split at h
    · cases h
      exact rules.exhaust evm.gas
    · rename_i hc
      cases h
      exact rules.charge hc

/-- The end of a message keeps the relation, after a revert or a halt. -/
theorem rollbackOnError (rules : MeterRules Q) (snapshot : TransactionState)
    (evm : Evm fork Meter) : Q evm.gas (Evm.rollbackOnError snapshot evm).gas := by
  unfold Evm.rollbackOnError
  split
  · dsimp only
    split
    · exact rules.rollback evm.gas
    · exact rules.refl evm.gas
  · exact rules.refl evm.gas

/-- The deposit of code keeps the relation. -/
theorem depositCode (rules : MeterRules Q) {snapshot : TransactionState}
    {evm after : Evm fork Meter} (h : Evm.depositCode fork snapshot evm = .ok after) :
    Q evm.gas after.gas := by
  unfold Evm.depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact rules.refl evm.gas
  split at h
  · cases h
    exact rules.exhaust evm.gas
  split at h
  · cases h
    exact rules.exhaust evm.gas
  split at h
  · cases h
    split
    · exact rules.exhaust evm.gas
    · exact rules.refl evm.gas
  rename_i hc
  split at h
  · cases h
    exact rules.exhaust evm.gas
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  unfold chargeCodeDeposit at hc
  split at hc
  · obtain ⟨_, h1, h2⟩ := Base.bind_ok_iff.mp hc
    exact rules.trans (rules.charge h1) (rules.chargeState h2)
  · exact rules.charge hc

/-- Every successful call and creation relates its starting meter to the frame that ends it. -/
theorem processMessage_and (rules : MeterRules Q) [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, Evm.processMessage fork message state substate meter held = .ok ended →
        Q meter ended.val.gas) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, Evm.processCreateMessage fork message state substate meter held = .ok ended →
        Q meter ended.val.gas) :=
  processMessage_rel (R := fun a b => Q a.gas b.gas) (Inv := fun _ => True)
    (M := fun _ _ _ meter ended => Q meter ended.gas)
    (fun evm => rules.refl evm.gas) rules.trans (fun _ _ => trivial)
    (fun evm _ _ => rules.exhaust evm.gas) (fun _ h => rules.step h)
    (fun evm _ => rules.refl evm.gas) (fun h _ => rules.runPrecompile h)
    (fun {_ state _ _ _ _ ended} _ run =>
      rules.trans (run trivial) (rules.rollbackOnError state ended))
    (fun _ hm hd => rules.trans hm (rules.depositCode hd)) n

/-- The frame that ends a successful call is related to the meter it starts with. -/
theorem processMessage (rules : MeterRules Q) [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : Evm.processMessage fork message state substate meter held = .ok ended) :
    Q meter ended.val.gas :=
  (rules.processMessage_and message.gas).1 message state substate meter held rfl ended h

/-- The frame that ends a successful creation is related to the meter it starts with. -/
theorem processCreateMessage (rules : MeterRules Q) [LawfulGasMeter Meter]
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : Evm.processCreateMessage fork message state substate meter held = .ok ended) :
    Q meter ended.val.gas :=
  (rules.processMessage_and message.gas).2 message state substate meter held rfl ended h

end MeterRules

/-! ## The meter of EIP-8037 -/

/-- Each operation that a frame applies keeps the starting reservoir and the committed spill.

A commit and a rollback to the start of the frame change them, but no frame applies either. -/
theorem StateGasMeter.meterRules :
    MeterRules (fun a b : StateGasMeter => b.grant = a.grant ∧ b.committed = a.committed) where
  refl _ := ⟨rfl, rfl⟩
  trans hab hbc := ⟨hbc.1.trans hab.1, hbc.2.trans hab.2⟩
  charge {meter after amount} h := by
    simp only [GasMeter.charge, StateGasMeter.charge] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩
  chargeState {meter after amount} h := by
    simp only [GasMeter.chargeState, StateGasMeter.chargeState] at h
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · split at h
      · cases h
        exact ⟨rfl, rfl⟩
      · cases h
  refill _ _ := ⟨rfl, rfl⟩
  exhaust _ := ⟨rfl, rfl⟩
  rollback _ := ⟨rfl, rfl⟩
  drain _ := ⟨rfl, rfl⟩
  credit _ _ _ := ⟨rfl, rfl⟩
  absorb _ _ succeeded := by
    cases succeeded <;> exact ⟨rfl, rfl⟩

/-- A successful call keeps the starting reservoir that its meter records. -/
theorem StateGasMeter.processMessage_grant
    {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : Evm.processMessage fork message state substate meter held = .ok ended) :
    ended.val.gas.grant = meter.grant :=
  (StateGasMeter.meterRules.processMessage h).1

/-- A successful call keeps the committed spill of the meter it starts with. -/
theorem StateGasMeter.processMessage_committed
    {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : Evm.processMessage fork message state substate meter held = .ok ended) :
    ended.val.gas.committed = meter.committed :=
  (StateGasMeter.meterRules.processMessage h).2

/-- A successful creation keeps the starting reservoir that its meter records. -/
theorem StateGasMeter.processCreateMessage_grant
    {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : Evm.processCreateMessage fork message state substate meter held = .ok ended) :
    ended.val.gas.grant = meter.grant :=
  (StateGasMeter.meterRules.processCreateMessage h).1

/-- A successful creation keeps the committed spill of the meter it starts with. -/
theorem StateGasMeter.processCreateMessage_committed
    {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : Evm.processCreateMessage fork message state substate meter held = .ok ended) :
    ended.val.gas.committed = meter.committed :=
  (StateGasMeter.meterRules.processCreateMessage h).2

end EthLib.Execution.Evm
