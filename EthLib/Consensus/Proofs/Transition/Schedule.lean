module

public import EthLib.Consensus.Proofs.ForkSchedule
public import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Proofs: the fork of a state follows the schedule

A state is on the schedule when its fork is the fork at the epoch of its slot.

The transition upgrades one fork at a time, only at the first epoch of the next fork.

When the forks of the configuration start in order, it still reaches the fork of every epoch.

So a run that starts on the schedule stays on it.

A Phase 0 genesis state is on it unless Altair starts at once.

Then a run from genesis stays on it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The fork of a state is the fork at the epoch of its slot. -/
def OnSchedule (config : Config) (forked : ForkedBeaconState preset) : Prop :=
  forked.fork = config.forkAtEpoch (computeEpochAtSlot preset forked.state.slot)

/--
The upgrades at the first slot of an epoch reach the fork at that epoch.

The state starts at a consensus fork at or before that fork.

Every later consensus fork starts at that epoch or after it.
-/
private theorem processUpgrades_onSchedule (ordered : config.ForkEpochsOrdered)
    {forked after : ForkedBeaconState preset} {start : Epoch}
    (computed : processUpgrades config checks forked = .ok after)
    (first : forked.state.slot % preset.SLOTS_PER_EPOCH = 0)
    (current : config.activationEpoch forked.fork = some start)
    (below : forked.fork ≤ config.forkAtEpoch (computeEpochAtSlot preset forked.state.slot))
    (pending : ∀ fork begin, config.activationEpoch fork = some begin → forked.fork < fork →
      computeEpochAtSlot preset forked.state.slot ≤ begin) :
    OnSchedule config after := by
  -- Each due upgrade keeps the slot, and reaches a consensus fork at or before the scheduled one.
  obtain ⟨slot, atMost, begin, consensus⟩ := processUpgrades_induction_due
    (property := fun s => s.state.slot = forked.state.slot ∧
      s.fork ≤ config.forkAtEpoch (computeEpochAtSlot preset forked.state.slot) ∧
      ∃ begin, config.activationEpoch s.fork = some begin)
    (fun {pre post} due ⟨same, _, _⟩ ok => by
      have reached := upgradeNext_fork ok
      cases scheduled : config.nextFork pre.fork with
      | none => simp [upgradeDue, scheduled] at due
      | some next =>
        obtain ⟨fork, epoch⟩ := next
        simp only [upgradeDue, scheduled, Option.any_some, Bool.and_eq_true, beq_iff_eq,
          same] at due
        simp only [scheduled, Option.map_some, Option.some.injEq] at reached
        obtain ⟨-, starts⟩ := Config.nextFork_activationEpoch scheduled
        refine ⟨(upgradeFrame_upgradeNext ok).slot.trans same, ?_, epoch, reached ▸ starts⟩
        exact reached ▸ Config.le_forkAtEpoch starts (due.2 ▸ UInt64.le_refl _))
    ⟨rfl, below, start, current⟩ computed
  unfold OnSchedule
  rw [slot]
  -- A fork below the scheduled one would have its next fork start at this very epoch.
  rcases Nat.lt_or_eq_of_le atMost with early | same
  · exfalso
    obtain ⟨last, lastStarts, lastStarted⟩ :=
      Config.activationEpoch_forkAtEpoch (config := config)
        (computeEpochAtSlot preset forked.state.slot)
    obtain ⟨next, epoch, scheduled, notAfter⟩ :=
      Config.exists_nextFork_le consensus lastStarts early
    obtain ⟨later, starts⟩ := Config.nextFork_activationEpoch scheduled
    have upper := UInt64.le_trans (Config.activationEpoch_le_of_le ordered starts lastStarts
      notAfter) lastStarted
    have lower := pending next epoch starts
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le computed) later)
    exact processUpgrades_nextFork_ne computed scheduled first (UInt64.le_antisymm lower upper)
  · exact Fork.ctorIdx_injective same

/-- When the forks start in order, one slot and its upgrades keep a state on the schedule. -/
theorem advanceSlotAcross_onSchedule (ordered : config.ForkEpochsOrdered)
    {forked after : ForkedBeaconState preset} (on : OnSchedule config forked)
    (computed : advanceSlotAcross config checks forked = .ok after) : OnSchedule config after := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp computed
  have next := advanceSlot_slot slotOk
  have epochOf : ∀ slot : Slot,
      (computeEpochAtSlot preset slot).toNat = slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    intro slot
    simp [computeEpochAtSlot, UInt64.toNat_div]
  by_cases first : advanced.slot % preset.SLOTS_PER_EPOCH = 0
  · -- At the first slot of an epoch, the epoch moves on by one.
    have divides : preset.SLOTS_PER_EPOCH.toNat ∣ advanced.slot.toNat := by
      have := congrArg UInt64.toNat first
      simp only [UInt64.toNat_mod, UInt64.toNat_zero] at this
      exact Nat.dvd_of_mod_eq_zero this
    have moved : (computeEpochAtSlot preset advanced.slot).toNat =
        (computeEpochAtSlot preset forked.state.slot).toNat + 1 := by
      have divides' : preset.SLOTS_PER_EPOCH.toNat ∣ forked.state.slot.toNat + 1 := next ▸ divides
      rw [epochOf, epochOf, next, Nat.succ_div]
      simp [divides']
    obtain ⟨start, current, started⟩ := Config.activationEpoch_forkAtEpoch (config := config)
      (computeEpochAtSlot preset forked.state.slot)
    refine processUpgrades_onSchedule ordered upgrades first (by rw [on]; exact current) ?_ ?_
    · exact Nat.le_trans (Nat.le_of_eq (congrArg Fork.ctorIdx on))
        (Config.forkAtEpoch_mono (show computeEpochAtSlot preset forked.state.slot ≤
          computeEpochAtSlot preset advanced.slot from UInt64.le_iff_toNat_le.mpr (by omega)))
    · -- A later consensus fork has not started at the epoch of the state, so starts after it.
      intro fork begin starts later
      change computeEpochAtSlot preset advanced.slot ≤ begin
      have notStarted : ¬begin ≤ computeEpochAtSlot preset forked.state.slot := fun started =>
        Nat.lt_irrefl _ (Nat.lt_of_lt_of_le later (on ▸ Config.le_forkAtEpoch starts started))
      rw [UInt64.le_iff_toNat_le] at notStarted ⊢
      omega
  · -- Elsewhere no upgrade is due, and the epoch stays.
    rw [processUpgrades_of_not_due (upgradeDue_of_not_first first)] at upgrades
    cases upgrades
    have kept : computeEpochAtSlot preset advanced.slot =
        computeEpochAtSlot preset forked.state.slot := by
      have notDivides : ¬preset.SLOTS_PER_EPOCH.toNat ∣ forked.state.slot.toNat + 1 := by
        intro divides
        apply first
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_mod, UInt64.toNat_zero, next]
        exact Nat.mod_eq_zero_of_dvd divides
      apply UInt64.toNat_inj.mp
      rw [epochOf, epochOf, next, Nat.succ_div]
      simp [notDivides]
    show forked.fork = _
    rw [kept]
    exact on

/-- When the forks start in order, slots and their upgrades keep a state on the schedule. -/
theorem advanceSlotsAcross_onSchedule (ordered : config.ForkEpochsOrdered) :
    ∀ {count : Nat} {forked after : ForkedBeaconState preset}, OnSchedule config forked →
      advanceSlotsAcross config checks count forked = .ok after → OnSchedule config after
  | 0, _, _, on, computed => by
    cases computed
    exact on
  | _ + 1, _, _, on, computed => by
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp computed
    exact advanceSlotsAcross_onSchedule ordered
      (advanceSlotAcross_onSchedule ordered on nextOk) rest

/-- When the forks start in order, advancing to a later slot keeps a state on the schedule. -/
theorem processSlotsAcross_onSchedule (ordered : config.ForkEpochsOrdered)
    {forked after : ForkedBeaconState preset} {slot : Slot} (on : OnSchedule config forked)
    (computed : processSlotsAcross config checks forked slot = .ok after) :
    OnSchedule config after := by
  simp only [processSlotsAcross, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact advanceSlotsAcross_onSchedule ordered on advanced

/-- When the forks start in order, each step of a run keeps a state on the schedule. -/
theorem Step.onSchedule (ordered : config.ForkEpochsOrdered)
    {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (on : OnSchedule config before) :
    OnSchedule config after := by
  cases step with
  | slot ok => exact advanceSlotAcross_onSchedule ordered on ok
  | block engine signed _ ok =>
    unfold OnSchedule
    rw [(frame_processBlock (applySignedBlock_ok ok).2.1).slot]
    exact on

/-- When the forks start in order, a run that starts on the schedule stays on it. -/
theorem Run.onSchedule (ordered : config.ForkEpochsOrdered) {first last : ForkedBeaconState preset}
    (run : Run config checks first last) (on : OnSchedule config first) :
    OnSchedule config last := by
  induction run with
  | nil => exact on
  | snoc _ step ih => exact step.onSchedule ordered ih

/-- When the forks start in order, the upgrades due at slot zero bring a Phase 0 state onto it. -/
theorem processUpgrades_onSchedule_of_phase0 (ordered : config.ForkEpochsOrdered)
    {forked after : ForkedBeaconState preset} (phase0 : forked.fork = .phase0)
    (zero : forked.state.slot = 0)
    (computed : processUpgrades config checks forked = .ok after) : OnSchedule config after := by
  refine processUpgrades_onSchedule ordered computed (by simp [zero]) (by rw [phase0]; rfl) ?_ ?_
  · exact Nat.le_trans (Nat.le_of_eq (congrArg Fork.ctorIdx phase0))
      (Config.le_forkAtEpoch (fork := .phase0) rfl UInt64.zero_le)
  · intro fork begin _ _
    simp [zero, computeEpochAtSlot, UInt64.zero_le]

/-- When the forks start in order, a Phase 0 state at slot zero is on the schedule.

That holds exactly when Altair does not start at epoch zero. -/
theorem onSchedule_iff_of_phase0 (ordered : config.ForkEpochsOrdered)
    {forked : ForkedBeaconState preset} (phase0 : forked.fork = .phase0)
    (zero : forked.state.slot = 0) :
    OnSchedule config forked ↔ 0 < config.ALTAIR_FORK_EPOCH := by
  obtain ⟨fork, state⟩ := forked
  subst phase0
  unfold OnSchedule
  dsimp only at zero ⊢
  rw [zero, show computeEpochAtSlot preset 0 = 0 by simp [computeEpochAtSlot]]
  constructor
  · -- Were Altair to start at epoch zero, the fork there would be Altair or later.
    intro same
    apply UInt64.not_le.mp
    intro altair
    have := Config.le_forkAtEpoch (config := config) (fork := .altair) rfl altair
    rw [← same] at this
    exact absurd this (by decide)
  · -- A consensus fork after Phase 0 starts no earlier than Altair, so not at epoch zero.
    intro altair
    obtain ⟨first, starts, started⟩ := Config.activationEpoch_forkAtEpoch (config := config) 0
    revert starts
    generalize config.forkAtEpoch 0 = fork
    intro starts
    cases fork
    case phase0 => rfl
    all_goals
      first
        | exact absurd altair (UInt64.not_lt.mpr (UInt64.le_trans
            (Config.activationEpoch_le_of_le ordered (earlier := .altair) rfl starts
              (by decide)) started))
        | simp [Config.activationEpoch] at starts

/-- When the forks start in order, a run from a Phase 0 genesis stays on the schedule.

It needs Altair to start after epoch zero, since a run applies no upgrade at genesis. -/
theorem Run.onSchedule_of_genesis (ordered : config.ForkEpochsOrdered)
    {g x : ForkedBeaconState preset} (genesis : Genesis config checks g)
    (phase0 : g.fork = .phase0) (altair : 0 < config.ALTAIR_FORK_EPOCH)
    (run : Run config checks g x) : OnSchedule config x := by
  obtain ⟨_, _, _, initialized⟩ := genesis
  have zero := (initializeBeaconStateFromEth1_checkpoints initialized).1
  exact run.onSchedule ordered ((onSchedule_iff_of_phase0 ordered phase0 zero).mpr altair)

end EthLib.Consensus
