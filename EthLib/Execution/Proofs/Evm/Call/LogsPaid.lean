module

public import EthLib.Execution.Proofs.Evm.Call.LogWeight
public import EthLib.Execution.Proofs.Evm.Call.LogsPaidSteps
public import EthLib.Execution.Proofs.Evm.Call.MeterRules

/-!
# Proofs: every log byte of a message is paid for by its gas

The potential of a frame is four times the weight of its logs, plus the gas it holds.

A LOG step adds a log and charges at least four times its weight, so it raises no potential.

Every other step adds no log, and raises the gas held only by taking back gas it gave a child.

A child that succeeds passes on its logs, and gives back the gas it holds.

From Glamsterdam, a message that moves ether to another account writes a transfer log of EIP-7708.

When an instruction sends the message, it pays for that log with gas the message never receives.

So no message raises the potential above its start, plus the allowance of its own transfer log.

That holds at every fork and for every lawful meter, whether or not the message ends with an error.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Base (U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The gas that pays for the transfer log a message may write, beyond the gas of the message.

A message that moves a positive amount of ether to another account writes one from Glamsterdam.

Any other message writes none, so it counts nothing beyond its own gas. -/
def messageAllowance (message : Message fork) : Nat :=
  if message.shouldTransferValue ∧ message.value ≠ 0 ∧ message.caller ≠ message.currentTarget then
    transferAllowance fork
  else 0

/-- The allowance of a message is at most the allowance of one transfer log at its fork. -/
theorem messageAllowance_le (message : Message fork) :
    messageAllowance message ≤ transferAllowance fork := by
  unfold messageAllowance
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-! ## Each step -/

/-- The potential of the second frame is at most that of the first. -/
private def LogsRel (a b : Evm fork Meter) : Prop :=
  logsPotential b ≤ logsPotential a

/-- The frame that ends a message has a potential of at most the gas of the message.

It may exceed that by the allowance of the message. -/
private def ChildPaid (_caller : Evm fork Meter) (message : Message fork)
    (child : Evm fork Meter) : Prop :=
  logsPotential child ≤ message.gas + messageAllowance message

/-- An allowance that a condition may drop is at most the allowance. -/
private theorem ite_le_left (p : Prop) [Decidable p] (a : Nat) : (if p then a else 0) ≤ a := by
  split <;> omega

/-- A message sent from a frame that paid for it, and its allowance, raises no potential. -/
private theorem keeps_child [LawfulGasMeter Meter] {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (logs : caller.substate.logs = evm.substate.logs)
    (gas : GasMeter.gasHeld caller.gas + message.gas + messageAllowance message ≤
      GasMeter.gasHeld evm.gas)
    (resumes : ∀ child after, resume child = .ok after →
      logsPotential after ≤ logsPotential caller + logsPotential child) :
    StepResult.Keeps LogsRel ChildPaid evm (.child caller message resume) := by
  refine ⟨logsPotential_le_of_logs logs (by omega), fun child after hres hc => ?_⟩
  have := resumes child after hres
  unfold ChildPaid at hc
  unfold LogsRel logsPotential at *
  rw [logs] at this
  omega

/-- The end of a call that paid its message and the allowance of its value raises no potential. -/
private theorem keeps_finishCall [LawfulGasMeter Meter] {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm e : Evm fork Meter}
    {result : StepResult fork Meter} (logs : e.substate.logs = evm.substate.logs)
    (gas : GasMeter.gasHeld e.gas + subCall +
        (if call.value = 0 then 0 else transferAllowance fork) ≤ GasMeter.gasHeld evm.gas)
    (h : finishCall kind call callee subCall newAccount expandBy e = .ok result) :
    StepResult.Keeps LogsRel ChildPaid evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    show logsPotential after ≤ logsPotential evm
    rw [logsPotential_skipCall hs]
    refine Nat.le_trans (Nat.add_le_add_right (logsPotential_refillStateGas _ _) _) ?_
    simp only [logsPotential, recordAccountRead, LawfulGasMeter.gasHeld_drain]
    rw [logs]
    split at gas <;> omega
  · unfold genericCall at h
    dsimp only at h
    split at h
    · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
      show logsPotential after ≤ logsPotential evm
      rw [logsPotential_skipCall hs]
      refine Nat.le_trans (Nat.add_le_add_right (logsPotential_refillStateGas _ _) _) ?_
      simp only [logsPotential, recordAccountRead, LawfulGasMeter.gasHeld_drain]
      rw [logs]
      split at gas <;> omega
    · cases h
      refine keeps_child logs ?_ (fun _ _ hres => logsPotential_resumeCall hres)
      simp only [recordAccountRead, LawfulGasMeter.gasHeld_drain]
      refine Nat.le_trans (Nat.add_le_add_left ?_ _) gas
      unfold messageAllowance
      dsimp only
      by_cases hk : kind = CallKind.delegatecall
      · subst hk
        simp
      · by_cases hv : call.value = 0
        · simp [hk, hv]
        · simp only [hv, ↓reduceIte]
          exact ite_le_left _ _

/-- A frame halted with the logs of an earlier frame has no more potential than it. -/
private theorem logsRel_exceptionalHalt [LawfulGasMeter Meter] {evm e : Evm fork Meter}
    (logs : e.substate.logs = evm.substate.logs) (error : EvmError) :
    LogsRel evm (exceptionalHalt e error) :=
  logsPotential_le_of_logs logs (by
    simp only [exceptionalHalt, LawfulGasMeter.gasHeld_exhaust]
    exact Nat.zero_le _)

/-- A step of a call instruction raises no potential.

That holds when its child has at most its gas, plus its allowance. -/
private theorem keeps_callStep [LawfulGasMeter Meter] {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    StepResult.Keeps LogsRel ChildPaid evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have l1 : e1.substate.logs = evm.substate.logs := by rw [popCallOperands_eq_ok h1]
  have g1 := (popCallOperands_pays h1).gasHeld
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  have l2 := logs_accessAddress e1 call.address
  have g2 := (accessAddress_pays e1 call.address).gasHeld
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  rw [hacc] at l2 g2
  dsimp only at l2 g2
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have l4 := logs_accessDelegation h4
    have g4 := (accessDelegation_pays h4).gasHeld
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      have above : callValueCost fork call.value ≤
          callExtraGas fork kind e4.state call cold callee := by
        unfold callExtraGas
        dsimp only
        omega
      obtain ⟨l5, g5⟩ := payCall_gasHeld above h5
      refine keeps_finishCall (l5.trans (l4.trans (l2.trans l1))) ?_ h
      simp only [recordAccountRead] at g4
      omega
    · exact logsRel_exceptionalHalt (l4.trans (l2.trans l1)) e
  · exact logsRel_exceptionalHalt (l2.trans l1) e

/-- A launch of a creation that paid its base price raises no potential.

That holds when its child has at most its gas, plus its allowance. -/
private theorem keeps_launchCreate [LawfulGasMeter Meter] {evm e : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (logs : e.substate.logs = evm.substate.logs)
    (gas : GasMeter.gasHeld e.gas + createBaseCost fork ≤ GasMeter.gasHeld evm.gas)
    (h : launchCreate e value initCode salt = .ok result) :
    StepResult.Keeps LogsRel ChildPaid evm result := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    show logsPotential after ≤ logsPotential evm
    rw [logsPotential_skipCall hs]
    simp only [logsPotential, recordAccountRead]
    rw [logs]
    omega
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have l0 := (logs_accessAddress (recordAccountRead { e with returnData := .empty }
    e.message.currentTarget) address).trans logs
  have g0 : GasMeter.gasHeld (recordAccountRead (accessAddress (recordAccountRead
      { e with returnData := .empty } e.message.currentTarget) address).2 address).gas ≤
      GasMeter.gasHeld e.gas :=
    Nat.le_trans (Nat.le_add_right _ _) (accessAddress_pays (recordAccountRead
      { e with returnData := .empty } e.message.currentTarget) address).gasHeld
  rcases keepReads_eq_ok h with hr | ⟨err, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
    have l2 : e2.substate.logs = evm.substate.logs :=
      (chargeGas_sameContext h2).logs.trans ((chargeStateGas_sameContext h1).logs.trans l0)
    have g2 := ((chargeStateGas_pays h1).trans (chargeGas_pays h2)).gasHeld
    have hc := transferAllowance_le_createBaseCost (fork := fork)
    split at hr
    · cases hr
      refine keeps_child l2 ?_ (fun _ _ hres => logsPotential_resumeCreate hres)
      simp only [LawfulGasMeter.gasHeld_drain]
      refine Nat.le_trans (Nat.add_le_add_left (Nat.le_trans (messageAllowance_le _) hc) _) ?_
      omega
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      show logsPotential _ ≤ logsPotential evm
      refine Nat.le_trans (logsPotential_le_of_logs (pushWord_sameContext h3).logs
        (Nat.le_trans (Nat.le_add_right _ _) (pushWord_pays h3).gasHeld)) ?_
      refine Nat.le_trans (logsPotential_refillStateGas { e2 with state } _) ?_
      exact logsPotential_le_of_logs l2 (by dsimp only; omega)
  · exact logsRel_exceptionalHalt l0 err

/-- A step of CREATE or CREATE2 raises no potential.

That holds when its child has at most its gas, plus its allowance. -/
private theorem keeps_createStep [LawfulGasMeter Meter] {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    StepResult.Keeps LogsRel ChildPaid evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have paid := (((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (popSalt_pays h4)).trans (chargeGasAndMemory_pays h5)).gasHeld
  have l5 : e5.substate.logs = evm.substate.logs :=
    ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
      (popWord_sameContext h3)).trans ((popSalt_eq_ok h4).2.1.trans
        (chargeGasAndMemory_sameContext h5))).logs
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact keeps_launchCreate l5 (by omega) h

/-- A step that may send a message raises no potential.

That holds when its child has at most its gas, plus its allowance. -/
private theorem keeps_messageInstruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : StepResult.Keeps LogsRel ChildPaid evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact keeps_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact keeps_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact keeps_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact keeps_createStep h
         · cases hrun)

/-- Each step of a running frame raises no potential.

That holds when each child has at most its gas, plus its allowance. -/
private theorem keeps_step [LawfulGasMeter Meter] {evm : Evm fork Meter}
    {result : StepResult fork Meter} (running : evm.running = true)
    (h : step fork evm = .ok result) : StepResult.Keeps LogsRel ChildPaid evm result := by
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hrun
        obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
        exact logsPotential_instruction hrun hr running
      · split at h
        · exact keeps_messageInstruction ‹_› h
        · cases h
  · obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
    cases hr
    exact Nat.le_refl _

/-! ## A run and a message -/

/-- The frame that ends a message has at most the potential it starts with, plus its allowance. -/
private def MessagePaid (message : Message fork) (_state : TransactionState) (substate : Substate)
    (meter : Meter) (ended : Evm fork Meter) : Prop :=
  4 * logsWeight ended.substate.logs.toList + GasMeter.gasHeld ended.gas ≤
    4 * logsWeight substate.logs.toList + GasMeter.gasHeld meter + messageAllowance message

/-- A message that a caller sends ends paid, when it ends with its potential bounded. -/
private theorem childPaid_of_childRel [LawfulGasMeter Meter] {caller : Evm fork Meter}
    {message : Message fork} {child : Evm fork Meter}
    (h : ChildRel MessagePaid caller message child) : ChildPaid caller message child := by
  unfold ChildRel MessagePaid at h
  have empty : caller.substate.child.logs.toList = [] := rfl
  rw [empty, logsWeight_nil, LawfulGasMeter.gasHeld_start] at h
  unfold ChildPaid logsPotential
  omega

/-- A precompile keeps the logs and holds no more gas, so it raises no potential. -/
private theorem logsPotential_runPrecompile [LawfulGasMeter Meter] {address : Nat}
    {evm after : Evm fork Meter} (h : runPrecompile fork address evm = some after) :
    logsPotential after ≤ logsPotential evm := by
  refine logsPotential_le_of_logs ?_ (gasHeld_runPrecompile_le h)
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    rfl
  · split at h <;> cases h <;> rfl

/-- The end of a message keeps the logs and holds no more gas, after a revert or a halt. -/
private theorem logsPotential_rollbackOnError [LawfulGasMeter Meter] (snapshot : TransactionState)
    (evm : Evm fork Meter) : logsPotential (rollbackOnError snapshot evm) ≤ logsPotential evm := by
  unfold rollbackOnError
  split
  · refine logsPotential_le_of_logs rfl ?_
    dsimp only
    split
    · exact LawfulGasMeter.gasHeld_rollback _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- The deposit of code keeps the logs and holds no more gas, so it raises no potential. -/
private theorem logsPotential_depositCode [LawfulGasMeter Meter] {snapshot : TransactionState}
    {evm after : Evm fork Meter} (h : depositCode fork snapshot evm = .ok after) :
    logsPotential after ≤ logsPotential evm := by
  refine logsPotential_le_of_logs ?_ (gasHeld_depositCode_le h)
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    split <;> rfl
  split at h
  · cases h
    rfl
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- An allowance under a condition is at most the allowance under a weaker condition. -/
private theorem ite_le_ite {p q : Prop} [Decidable p] [Decidable q] (h : p → q) (a : Nat) :
    (if p then a else 0) ≤ (if q then a else 0) := by
  by_cases hp : p
  · simp [hp, h hp]
  · simp [hp]

/-- A message starts with at most its allowance in logs beyond those of its caller. -/
private theorem logsWeight_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    4 * logsWeight entrySubstate.logs.toList ≤
      4 * logsWeight substate.logs.toList + messageAllowance message := by
  rcases h with ⟨-, -, rfl⟩ | ⟨ht, -, rfl⟩
  · omega
  · refine Nat.le_trans (logsWeight_pushTransferLog _ _ _ _) (Nat.add_le_add_left ?_ _)
    exact ite_le_ite (fun hc => ⟨ht.1, hc⟩) _

/-- Every call and creation that returns a frame raises its potential by at most its allowance.

The potential is four times the weight of the logs, plus the gas held.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_logsWeight_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        4 * logsWeight ended.val.substate.logs.toList + GasMeter.gasHeld ended.val.gas ≤
          4 * logsWeight substate.logs.toList + GasMeter.gasHeld meter +
            messageAllowance message) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        4 * logsWeight ended.val.substate.logs.toList + GasMeter.gasHeld ended.val.gas ≤
          4 * logsWeight substate.logs.toList + GasMeter.gasHeld meter +
            messageAllowance message) :=
  processMessage_frame_byKind (F := fun a b => logsPotential b ≤ logsPotential a)
    (Mcall := MessagePaid) (Mcreate := MessagePaid)
    (fun runs _ h => rel_runFrame (R := LogsRel) (C := ChildPaid) (Inv := fun _ => True)
      (fun _ => Nat.le_refl _) (fun hab hbc => Nat.le_trans hbc hab) (fun _ _ => trivial)
      (fun evm _ _ => logsRel_exceptionalHalt rfl _) (fun _ running h => keeps_step running h)
      (fun caller message lt ended _ hran => childPaid_of_childRel (by
        rw [← childRelByKind_self]
        exact runs caller message lt ended hran)) trivial h)
    (fun _ _ _ => Nat.le_refl _)
    (fun _ _ h => logsPotential_runPrecompile h)
    (fun {message state _ _ _ meter ended} entered frame => by
      have r := logsPotential_rollbackOnError state ended
      have e := logsWeight_entered entered
      unfold MessagePaid
      unfold logsPotential at r frame
      simp only [startFrame] at frame
      omega)
    (fun _ hm hd => by
      have d := logsPotential_depositCode hd
      unfold MessagePaid at *
      unfold logsPotential at d
      omega)
    n

/-- A call that returns a frame raises its potential by at most its own allowance.

The potential is four times the weight of the logs, plus the gas held.

That holds at every fork and for every lawful meter, whether or not the frame ends with an error. -/
theorem processMessage_logsWeight_messageAllowance [LawfulGasMeter Meter]
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    4 * logsWeight ended.val.substate.logs.toList + GasMeter.gasHeld ended.val.gas ≤
      4 * logsWeight substate.logs.toList + GasMeter.gasHeld meter + messageAllowance message :=
  (processMessage_logsWeight_induction message.gas).1 message state substate meter held rfl
    ended h

/-- A creation that returns a frame raises its potential by at most its own allowance.

The potential is four times the weight of the logs, plus the gas held.

That holds at every fork and for every lawful meter, whether or not the frame ends with an error. -/
theorem processCreateMessage_logsWeight_messageAllowance [LawfulGasMeter Meter]
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    4 * logsWeight ended.val.substate.logs.toList + GasMeter.gasHeld ended.val.gas ≤
      4 * logsWeight substate.logs.toList + GasMeter.gasHeld meter + messageAllowance message :=
  (processMessage_logsWeight_induction message.gas).2 message state substate meter held rfl
    ended h

/-- A call that returns a frame raises its potential by at most the allowance of a transfer log.

The potential is four times the weight of the logs, plus the gas held.

That holds at every fork and for every lawful meter, whether or not the frame ends with an error.

For a frame that ends with an error, the bound holds for the frame as returned.

Its caller then drops its logs. -/
theorem processMessage_logsWeight [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    4 * logsWeight ended.val.substate.logs.toList + GasMeter.gasHeld ended.val.gas ≤
      4 * logsWeight substate.logs.toList + GasMeter.gasHeld meter + transferAllowance fork :=
  Nat.le_trans (processMessage_logsWeight_messageAllowance h)
    (Nat.add_le_add_left (messageAllowance_le message) _)

/-- A creation that returns a frame raises its potential by at most the allowance of a transfer log.

The potential is four times the weight of the logs, plus the gas held.

That holds at every fork and for every lawful meter, whether or not the frame ends with an error.

For a frame that ends with an error, the bound holds for the frame as returned.

Its caller then drops its logs. -/
theorem processCreateMessage_logsWeight [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    4 * logsWeight ended.val.substate.logs.toList + GasMeter.gasHeld ended.val.gas ≤
      4 * logsWeight substate.logs.toList + GasMeter.gasHeld meter + transferAllowance fork :=
  Nat.le_trans (processCreateMessage_logsWeight_messageAllowance h)
    (Nat.add_le_add_left (messageAllowance_le message) _)

end EthLib.Execution.Evm
