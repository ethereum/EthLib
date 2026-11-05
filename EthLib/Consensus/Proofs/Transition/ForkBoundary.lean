module

public import EthLib.Consensus.Proofs.Transition.StateTransition
public import EthLib.Consensus.Transition.ForkBoundary

/-!
# Proofs: the state transition across a fork boundary

An upgrade moves the state to the next consensus fork of the schedule.

Before the first slot of the next fork epoch, the slots and blocks run as in one fork.

The fork of the state never moves back.

A valid block ran on the state of its own fork, at its slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- An upgrade moves the state to the next consensus fork of the schedule. -/
theorem upgradeNext_fork {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    (config.nextFork pre.fork).map Prod.fst = some post.val.fork := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed <;>
    first
      | (obtain ⟨_, -, rfl⟩ := computed; rfl)
      | (subst computed; rfl)

/-- With no upgrade due, the state stays as it is. -/
theorem processUpgrades_of_not_due {forked : ForkedBeaconState preset}
    (notDue : upgradeDue config forked = false) :
    processUpgrades config checks forked = .ok forked := by
  rw [processUpgrades]
  simp [notDue, pure, Except.pure]

/-- Away from the first slot of an epoch, no upgrade is due. -/
theorem upgradeDue_of_not_first {forked : ForkedBeaconState preset}
    (inside : forked.state.slot % preset.SLOTS_PER_EPOCH ≠ 0) :
    upgradeDue config forked = false := by
  simp [upgradeDue, inside]

/-- The upgrades never move the state to an earlier fork. -/
theorem processUpgrades_fork_le {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    forked.fork ≤ after.fork := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    -- One upgrade moves to a later fork, and the rest never move back.
    obtain ⟨step, -, rest⟩ := bind_ok_iff.mp computed
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le step.property (more step rest))
  | case2 forked _ =>
    cases computed
    exact Nat.le_refl _

/-- Before the first slot of the next fork epoch, no upgrade is due. -/
theorem upgradeDue_of_before {forked : ForkedBeaconState preset}
    (before : ∀ next ∈ config.nextFork forked.fork,
      forked.state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    upgradeDue config forked = false := by
  unfold upgradeDue
  cases scheduled : config.nextFork forked.fork with
  | none => simp
  | some next =>
    have early := before next scheduled
    simp only [Option.any_some, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine .inr fun same => ?_
    -- The epoch of the slot is its quotient by the epoch length, which stays below the fork epoch.
    have : (computeEpochAtSlot preset forked.state.slot).toNat < next.2.toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    rw [same] at this
    exact Nat.lt_irrefl _ this

/-- Before the first slot of the next fork epoch, one slot runs as in the fork of the state. -/
theorem advanceSlotAcross_of_before {fork : Fork} {state : BeaconState preset fork}
    (before : ∀ next ∈ config.nextFork fork,
      state.slot.toNat + 1 < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    advanceSlotAcross config checks ⟨fork, state⟩ =
      (advanceSlot config state).map (ForkedBeaconState.mk fork) := by
  unfold advanceSlotAcross
  cases advanced : advanceSlot config state with
  | error => rfl
  | ok after =>
    have notDue : upgradeDue config (⟨fork, after⟩ : ForkedBeaconState preset) = false :=
      upgradeDue_of_before fun next scheduled => by
        rw [show after.slot.toNat = state.slot.toNat + 1 from advanceSlot_slot advanced]
        exact before next scheduled
    simp [bind, Except.bind, Except.map, processUpgrades_of_not_due notDue]

/-- Before the first slot of the next fork epoch, the slots run as in the fork of the state. -/
theorem processSlotsAcross_of_before {fork : Fork} {state : BeaconState preset fork}
    {slot : Slot}
    (before : ∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    processSlotsAcross config checks ⟨fork, state⟩ slot =
      (processSlots config state slot).map (ForkedBeaconState.mk fork) := by
  have loop : ∀ (count : Nat) (state : BeaconState preset fork),
      state.slot.toNat + count ≤ slot.toNat →
      advanceSlotsAcross config checks count ⟨fork, state⟩ =
        (advanceSlots config count state).map (ForkedBeaconState.mk fork) := by
    intro count
    induction count with
    | zero => intro state _; rfl
    | succ count more =>
      intro state within
      simp only [advanceSlotsAcross, advanceSlots]
      rw [advanceSlotAcross_of_before fun next scheduled => by
        have := before next scheduled
        omega]
      cases advanced : advanceSlot config state with
      | error => rfl
      | ok after =>
        have := advanceSlot_slot advanced
        simp [bind, Except.bind, Except.map, more after (by omega)]
  unfold processSlotsAcross processSlots
  by_cases later : state.slot < slot
  · have := UInt64.lt_iff_toNat_lt.mp later
    simp [ensure, later, bind, Except.bind,
      loop (slot.toNat - state.slot.toNat) state (by omega)]
  · simp [ensure, later, bind, Except.bind, Except.map]

/-- A valid block ran on the state of its own fork, advanced to its slot. -/
theorem stateTransitionAcross_ok {fork : Fork} {engine : ExecutionEngine preset fork}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    ∃ advanced, processSlotsAcross config checks forked signed.message.slot =
        .ok ⟨fork, advanced⟩ ∧
      applySignedBlock config checks engine advanced signed validateResult = .ok after := by
  simp only [stateTransitionAcross, bind_ok_iff] at computed
  obtain ⟨⟨fork', advanced⟩, slotsOk, applied⟩ := computed
  by_cases same : fork' = fork
  · subst same
    simp only [↓reduceDIte] at applied
    exact ⟨advanced, slotsOk, applied⟩
  · simp [same, throw, throwThe, MonadExceptOf.throw] at applied

/-- Before the first slot of the next fork epoch, the transition is that of the fork. -/
theorem stateTransitionAcross_of_before {fork : Fork} {engine : ExecutionEngine preset fork}
    {state : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (before : ∀ next ∈ config.nextFork fork,
      signed.message.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    stateTransitionAcross config checks engine ⟨fork, state⟩ signed validateResult =
      stateTransition config checks engine state signed validateResult := by
  unfold stateTransitionAcross stateTransition
  rw [processSlotsAcross_of_before before]
  cases processSlots config state signed.message.slot <;> simp [bind, Except.bind, Except.map]

end EthLib.Consensus
