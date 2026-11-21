module

public import EthLib.Consensus.Proofs.Proposers
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# Proofs: from Fulu, a run keeps the proposer that the lookahead names for a slot

From Fulu the state names the proposers of this epoch and of the next epochs of the seed lookahead.

The epoch step moves each kept entry back by one epoch.

Blocks keep the lookahead, and so do the upgrades to Gloas and to Heze.

So along a run, the entry of a slot names one proposer until the run reaches that slot.

At that slot, the state computes that proposer for its block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

section Moves

variable {fork : Fork} {state after : BeaconState preset fork}

/-- Two states with the same lookahead of proposers. -/
private def Kept (state after : BeaconState preset fork) : Prop :=
  after.proposerLookahead = state.proposerLookahead

/-- Every state keeps its own lookahead. -/
private theorem Kept.refl (state : BeaconState preset fork) : Kept state state :=
  rfl

/-- Two steps in a row that keep the lookahead keep it. -/
private theorem Kept.trans {first second third : BeaconState preset fork}
    (one : Kept first second) (two : Kept second third) : Kept first third :=
  Eq.trans two one

/-- A step that keeps the inputs of a payload keeps the lookahead. -/
private theorem Kept.of_payloadInputs (inputs : PayloadInputs state after) : Kept state after :=
  inputs.proposerLookahead

/-- From Fulu, the epoch transition moves each kept proposer of the lookahead back by one epoch. -/
theorem processEpoch_proposerLookahead (fulu : .fusaka ≤ fork)
    (computed : processEpoch config checks state = .ok after) {position : Nat}
    (inside : position + preset.SLOTS_PER_EPOCH.toNat <
      (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :
    (after.proposerLookahead fulu)[position]? =
      (state.proposerLookahead fulu)[position + preset.SLOTS_PER_EPOCH.toNat]? := by
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) fulu
  have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) fulu
  obtain ⟨cleared, mixed, rooted, rotated, synced, looked, initial, mixedOk, rootedOk, rotation,
    syncedOk, lookedOk, windowed⟩ := processEpoch_randaoCut computed
  have head : Kept state cleared := Kept.of_payloadInputs (payloadInputs_epochPrefix initial)
  simp only [EpochStage.Edge, altair, capella, ↓reduceDIte] at rootedOk rotation syncedOk
  simp only [EpochStage.Edge, fulu, ↓reduceDIte] at lookedOk windowed
  have middle : Kept cleared synced := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    subst rotation
    exact (Kept.of_payloadInputs
      (payloadInputsLaws.processHistoricalSummariesUpdate rootedOk)).trans
      ((show Kept rooted (processParticipationFlagUpdates rooted altair) from rfl).trans
        (Kept.of_payloadInputs (payloadInputsLaws.processSyncCommitteeUpdates syncedOk)))
  have tail : Kept looked after := by
    split at windowed
    · exact Kept.of_payloadInputs (payloadInputsLaws.processPtcWindow windowed)
    · exact windowed ▸ Kept.refl _
  obtain ⟨_, _, _, _, shifted⟩ := processProposerLookahead_spec lookedOk
  have before : synced.proposerLookahead = state.proposerLookahead := head.trans middle
  rw [show after.proposerLookahead = looked.proposerLookahead from tail, ← before,
    Vector.getElem?_eq_getElem (by omega), Vector.getElem?_eq_getElem inside,
    shifted _ (by omega)]
  simp only [Vector.size, inside, ↓reduceDIte]

/-- Two states whose lookaheads name the same proposer for each slot that both cover, from Fulu.

The epoch of the second state starts no earlier than that of the first. -/
def ProposerLookaheadShifted (x y : ForkedBeaconState preset) : Prop :=
  currentEpochStart x.state ≤ currentEpochStart y.state ∧
    ∀ (early : .fusaka ≤ x.fork) (late : .fusaka ≤ y.fork) (slot : Nat),
      currentEpochStart y.state ≤ slot →
      slot < currentEpochStart x.state +
        (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      (y.state.proposerLookahead late)[slot - currentEpochStart y.state]? =
        (x.state.proposerLookahead early)[slot - currentEpochStart x.state]?

/-- Every state agrees with itself. -/
theorem ProposerLookaheadShifted.refl (x : ForkedBeaconState preset) :
    ProposerLookaheadShifted x x :=
  ⟨Nat.le_refl _, fun _ _ _ _ _ => rfl⟩

/-- Two agreements in a row give one, when the fork does not move back between them. -/
theorem ProposerLookaheadShifted.trans {first second third : ForkedBeaconState preset}
    (one : ProposerLookaheadShifted first second)
    (two : ProposerLookaheadShifted second third) (forks : first.fork ≤ second.fork) :
    ProposerLookaheadShifted first third :=
  ⟨Nat.le_trans one.1 two.1, fun early late slot low high => by
    rw [two.2 (Nat.le_trans early forks) late slot low (by have := one.1; omega),
      one.2 early (Nat.le_trans early forks) slot (by have := two.1; omega) high]⟩

/-- One slot keeps the proposer of each slot that both lookaheads cover. -/
private theorem proposerLookaheadShifted_advanceSlot
    (computed : advanceSlot config checks state = .ok after) :
    ProposerLookaheadShifted ⟨fork, state⟩ ⟨fork, after⟩ := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have startAfter : currentEpochStart { epoched with slot := next } =
      (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [currentEpochStart, getCurrentEpoch_toNat, sum]
  unfold ProposerLookaheadShifted
  dsimp only
  rw [startAfter, currentEpochStart, getCurrentEpoch_toNat]
  obtain ⟨boundary, epochedOk⟩ | ⟨inside, rfl⟩ := epochIfLast_cases epochedOk
  · have mod : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat boundary
      simpa [UInt64.toNat_mod, sum] using this
    -- The slot ends the epoch, so the next epoch starts one epoch later.
    rw [Nat.succ_div_of_mod_eq_zero mod, Nat.add_mul, Nat.one_mul]
    refine ⟨by omega, fun fulu _ slot low high => ?_⟩
    have moved := processEpoch_proposerLookahead fulu epochedOk
      (position := slot - (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat *
        preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat)) (by omega)
    rw [show slot - state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat =
      slot - (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_EPOCH.toNat) + preset.SLOTS_PER_EPOCH.toNat by omega]
    exact moved
  · have mod : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 := fun zero =>
      inside (UInt64.toNat_inj.mp (by simpa [UInt64.toNat_mod, sum] using zero))
    -- Inside the epoch, the epoch and the lookahead stay.
    rw [Nat.succ_div_of_mod_ne_zero mod]
    exact ⟨Nat.le_refl _, fun _ _ _ _ _ => rfl⟩

/-- Any count of slots keeps the proposer of each slot that both lookaheads cover. -/
theorem proposerLookaheadShifted_advanceSlots :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
        ProposerLookaheadShifted ⟨fork, state⟩ ⟨fork, after⟩
  | 0, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ProposerLookaheadShifted.refl _
  | count + 1, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨_, first, rest⟩ := computed
    exact (proposerLookaheadShifted_advanceSlot first).trans
      (proposerLookaheadShifted_advanceSlots count rest) (Nat.le_refl _)

/-- From Fulu, the proposer of a state is the entry of its lookahead at its slot. -/
theorem getBeaconProposerIndex_of_proposerLookahead (fulu : .fusaka ≤ fork)
    (nonzero : preset.SLOTS_PER_EPOCH ≠ 0) {index : ValidatorIndex}
    (found : (state.proposerLookahead fulu)[state.slot.toNat - currentEpochStart state]? =
      some index) :
    getBeaconProposerIndex state = .ok index := by
  have position : (state.slot % preset.SLOTS_PER_EPOCH).toNat =
      state.slot.toNat - currentEpochStart state := by
    rw [UInt64.toNat_mod, currentEpochStart, getCurrentEpoch_toNat]
    have := Nat.mod_add_div' state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    omega
  unfold getBeaconProposerIndex
  simp only [fulu, nonzero, ↓reduceDIte, position]
  rw [Vector.getElem?_eq_some_iff] at found
  obtain ⟨_, found⟩ := found
  rw [found]
  rfl

end Moves

/-- From Fulu, an upgrade keeps the lookahead: those to Gloas and to Heze copy it. -/
private theorem upgradeNext_proposerLookahead {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) (early : .fusaka ≤ pre.fork)
    (late : .fusaka ≤ post.val.fork) :
    post.val.state.proposerLookahead late = pre.state.proposerLookahead early := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToGloas, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, onboarded⟩ := upgraded
    obtain ⟨⟨_, _, rfl⟩, _⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    rfl
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl
  -- Every earlier fork is before Fulu, and Heze and the blob forks have no next fork.
  all_goals first
    | exact absurd early (by dsimp only; decide)
    | (simp only [upgradeNext] at computed; cases computed)

/-- An upgrade keeps the slot, and from Fulu the lookahead. -/
private theorem proposerLookaheadShifted_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    ProposerLookaheadShifted pre post.val := by
  have epoch : getCurrentEpoch post.val.state = getCurrentEpoch pre.state := by
    simp only [getCurrentEpoch, (upgradeFrame_upgradeNext computed).slot]
  unfold ProposerLookaheadShifted currentEpochStart
  refine ⟨Nat.le_of_eq (by rw [epoch]), fun early late _ _ _ => ?_⟩
  rw [epoch, upgradeNext_proposerLookahead computed early late]

/-- A step of a chain keeps the proposer of each slot that both lookaheads cover. -/
private theorem ChainStep.proposerLookaheadShifted {x y : ForkedBeaconState preset}
    (step : ChainStep config checks x y) : ProposerLookaheadShifted x y := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    -- The slot, then each upgrade due at the slot it reaches.
    exact (processUpgrades_induction (forked := ⟨x.fork, advanced⟩)
      (property := fun u => x.fork ≤ u.fork ∧ ProposerLookaheadShifted x u)
      (fun {_ post} ⟨le, holds⟩ stepOk => ⟨Nat.le_trans le (Nat.le_of_lt post.property),
        holds.trans (proposerLookaheadShifted_upgradeNext stepOk) le⟩)
      ⟨Nat.le_refl _, proposerLookaheadShifted_advanceSlot advancedOk⟩ upgraded).2
  | @block _ state after engine signed validated ok =>
    -- A block keeps the slot and the lookahead.
    have frame := frame_processBlock (applySignedBlock_ok ok).2.1
    have look := processBlock_proposerLookahead (applySignedBlock_ok ok).2.1
    have epoch : getCurrentEpoch after = getCurrentEpoch state := by
      simp only [getCurrentEpoch, frame.slot]
    unfold ProposerLookaheadShifted currentEpochStart
    refine ⟨Nat.le_of_eq (by dsimp only; rw [epoch]), fun early _ _ _ _ => ?_⟩
    dsimp only
    rw [epoch, look]

/-- A run keeps the proposer of each slot that both lookaheads cover. -/
private theorem Run.proposerLookaheadShifted {x y : ForkedBeaconState preset}
    (run : Run config checks x y) : ProposerLookaheadShifted x y := by
  induction run with
  | nil => exact .refl _
  | snoc pre step ih =>
    exact ih.trans step.chainStep.proposerLookaheadShifted (fork_le_of_chainSteps pre.chainSteps)

/-- From Fulu, a run keeps the proposer that the lookahead of its first state names for a slot.

The slot is in the epochs that the lookahead covers, and the run ends at or before it.

The last state then names the same proposer at the position of that slot. -/
theorem Run.proposerLookahead_getElem? {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (fulu : .fusaka ≤ x.fork) {slot : Nat}
    (started : currentEpochStart x.state ≤ slot)
    {proposer : ValidatorIndex}
    (found : (x.state.proposerLookahead fulu)[slot - currentEpochStart x.state]? = some proposer)
    (early : y.state.slot.toNat ≤ slot) :
    (y.state.proposerLookahead (Nat.le_trans fulu (fork_le_of_chainSteps run.chainSteps)))[slot -
        currentEpochStart y.state]? = some proposer := by
  -- The found entry lies inside the lookahead of the first state.
  have inside := (Vector.getElem?_eq_some_iff.mp found).1
  -- The last epoch starts at or before the slot of the last state.
  have reached : currentEpochStart y.state ≤ y.state.slot.toNat := by
    rw [currentEpochStart, getCurrentEpoch_toNat]
    exact Nat.div_mul_le_self _ _
  rw [run.proposerLookaheadShifted.2 fulu _ slot (by omega) (by omega)]
  exact found

/-- From Fulu, the state that a run reaches at a slot computes the proposer named for it earlier.

The name is the entry of that slot in the lookahead of the first state of the run. -/
theorem Run.getBeaconProposerIndex_of_proposerLookahead {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (fulu : .fusaka ≤ x.fork) {slot : Nat}
    (started : currentEpochStart x.state ≤ slot)
    {proposer : ValidatorIndex}
    (found : (x.state.proposerLookahead fulu)[slot - currentEpochStart x.state]? = some proposer)
    (reached : y.state.slot.toNat = slot) :
    getBeaconProposerIndex y.state = .ok proposer := by
  -- With no slot in an epoch, the lookahead is empty and holds no entry.
  have nonzero : preset.SLOTS_PER_EPOCH ≠ 0 := fun zero => by
    have inside := (Vector.getElem?_eq_some_iff.mp found).1
    simp only [zero, UInt64.toNat_zero, Nat.mul_zero] at inside
    omega
  apply Consensus.getBeaconProposerIndex_of_proposerLookahead
    (Nat.le_trans fulu (fork_le_of_chainSteps run.chainSteps)) nonzero
  rw [reached]
  exact run.proposerLookahead_getElem? fulu started found (Nat.le_of_eq reached)

end EthLib.Consensus
