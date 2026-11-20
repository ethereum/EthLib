module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Proofs: a trace of the steps of a chain, with their inputs

A step of a chain says that one state follows from another, but it does not keep the block.

A run keeps each step with its inputs: the slot step, or the signed block and its engine.

So a theorem about a run can name the blocks of that run and the attestations in them.

A block step of a run checks its state root, and is applied on a state with no upgrade due.

Each step of a run is a step of a chain, so the invariants of chains hold along a run.

Slots and blocks before the next fork form runs.

A run has at most one block for each slot it covers.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A genesis state built from deposits.

It need not be valid for launch. -/
def Genesis (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset) : Prop :=
  ∃ hash time deposits,
    initializeBeaconStateFromEth1 config checks hash time deposits = .ok g.state

/-- One step of a run: a slot, or a signed block applied with its state root checked. -/
inductive Step (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Type where
  | slot {before after} (ok : advanceSlotAcross config checks before = .ok after) :
      Step config checks before after
  | block {fork : Fork} {before after : BeaconState preset fork}
      (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
      (due : upgradeDue config ⟨fork, before⟩ = false)
      (ok : applySignedBlock config checks engine before signed true = .ok after) :
      Step config checks ⟨fork, before⟩ ⟨fork, after⟩

/-- A sequence of steps from `first`, which keeps the input of each step. -/
inductive Run (config : Config) (checks : SignatureChecks) (first : ForkedBeaconState preset) :
    ForkedBeaconState preset → Type where
  | nil : Run config checks first first
  | snoc {middle last} (pre : Run config checks first middle)
      (step : Step config checks middle last) : Run config checks first last

/-- The steps of `pre`, then the steps of `tail`. -/
def Run.append {first middle last : ForkedBeaconState preset}
    (pre : Run config checks first middle) (tail : Run config checks middle last) :
    Run config checks first last :=
  match tail with
  | .nil => pre
  | .snoc tail step => .snoc (pre.append tail) step

/-- A step is in a run, with its inputs, not only its two states. -/
inductive Run.Contains {first : ForkedBeaconState preset} :
    {last before after : ForkedBeaconState preset} → Run config checks first last →
      Step config checks before after → Prop where
  | last {middle after} (pre : Run config checks first middle)
      (step : Step config checks middle after) : Contains (.snoc pre step) step
  | earlier {middle last before after} {pre : Run config checks first middle}
      {step : Step config checks before after} (member : Contains pre step)
      (next : Step config checks middle last) : Contains (.snoc pre next) step

/-- A step of a run is a step of a chain. -/
theorem Step.chainStep {x y : ForkedBeaconState preset} (step : Step config checks x y) :
    ChainStep config checks x y := by
  cases step with
  | slot ok => exact .slot ok
  | block engine signed _ ok => exact .block engine signed true ok

/-- A step that crosses an epoch is the slot that ends it: a block keeps the slot. -/
theorem Step.eq_slot_of_crossing {x y : ForkedBeaconState preset} (step : Step config checks x y)
    (crossing : getCurrentEpoch x.state < getCurrentEpoch y.state) :
    ∃ ok : advanceSlotAcross config checks x = .ok y, step = .slot ok := by
  cases step with
  | slot ok => exact ⟨ok, rfl⟩
  | block engine signed due ok =>
    exact absurd (by simp only [getCurrentEpoch, (frame_processBlock
      (applySignedBlock_ok ok).2.1).slot]) (UInt64.ne_of_lt crossing).symm

/-- A run is a sequence of steps of a chain. -/
theorem Run.chainSteps {x y : ForkedBeaconState preset} (run : Run config checks x y) :
    Relation.ReflTransGen (ChainStep config checks) x y := by
  induction run with
  | nil => exact .refl
  | snoc _ step ih => exact ih.tail step.chainStep

/-- Appending runs is associative. -/
theorem Run.append_assoc {a b c d : ForkedBeaconState preset} (one : Run config checks a b)
    (two : Run config checks b c) (three : Run config checks c d) :
    one.append (two.append three) = (one.append two).append three := by
  induction three with
  | nil => rfl
  | snoc three step ih => exact congrArg (fun run => run.snoc step) ih

/-- A step of two appended runs is a step of one of them. -/
theorem Run.contains_append {g x y u v : ForkedBeaconState preset}
    (pre : Run config checks g x) (tail : Run config checks x y)
    (step : Step config checks u v) :
    (pre.append tail).Contains step ↔ pre.Contains step ∨ tail.Contains step := by
  induction tail with
  | nil =>
    constructor
    · exact Or.inl
    · rintro (member | member)
      · exact member
      · cases member
  | snoc tail next ih =>
    constructor
    · intro member
      cases member with
      | last => exact .inr (.last _ _)
      | earlier member =>
        rcases ih.mp member with member | member
        · exact .inl member
        · exact .inr (.earlier member next)
    · rintro (member | member)
      · exact .earlier (ih.mpr (.inl member)) next
      · cases member with
        | last => exact .last _ _
        | earlier member => exact .earlier (ih.mpr (.inr member)) next

/-- A step of a run splits it into the run before the step, the step and the run after it. -/
theorem Run.contains_split {g a x y : ForkedBeaconState preset}
    (run : Run config checks g a) (step : Step config checks x y) (member : run.Contains step) :
    ∃ (pre : Run config checks g x) (post : Run config checks y a),
      run = (pre.snoc step).append post := by
  induction member with
  | last pre step => exact ⟨pre, .nil, rfl⟩
  | earlier member next ih =>
    obtain ⟨pre, post, same⟩ := ih
    exact ⟨pre, post.snoc next, congrArg (fun run => run.snoc next) same⟩

namespace DirectSafety.Apriori.Internal

/-- A segment of a run that starts in an epoch either stays in it or ends it with one slot.

Every step of the segment `mid` starts at the epoch of its start `m`.

If the segment leaves the epoch, its last step is the slot that ends it, after an inner run. -/
theorem segment_slot_cases {m n : ForkedBeaconState preset} (mid : Run config checks m n)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state) :
    getCurrentEpoch n.state = getCurrentEpoch m.state ∨
      ∃ (u : ForkedBeaconState preset) (inner : Run config checks m u)
        (boundary : advanceSlotAcross config checks u = .ok n),
        mid = inner.snoc (.slot boundary) ∧
        getCurrentEpoch u.state = getCurrentEpoch m.state ∧
        getCurrentEpoch u.state < getCurrentEpoch n.state := by
  by_cases same : getCurrentEpoch n.state = getCurrentEpoch m.state
  · exact .inl same
  right
  cases mid with
  | nil => exact absurd rfl same
  | @snoc u _ inner step =>
  have uEpoch : getCurrentEpoch u.state = getCurrentEpoch m.state := starts step (.last _ _)
  have crossing : getCurrentEpoch u.state < getCurrentEpoch n.state :=
    UInt64.lt_of_le_of_ne step.chainStep.currentEpoch_le
      (fun equal => same (equal.symm.trans uEpoch))
  -- The last step leaves the epoch, so it is the slot that ends it.
  obtain ⟨boundary, rfl⟩ := step.eq_slot_of_crossing crossing
  exact ⟨u, inner, boundary, rfl, uEpoch, crossing⟩

/-- A step of a pre-Gloas run is pre-Gloas, and its input epoch is at most the run's end epoch. -/
theorem Run.contains_step_facts {x y u v : ForkedBeaconState preset}
    {tail : Run config checks x y} {step : Step config checks u v} (member : tail.Contains step)
    (early : y.fork < .glamsterdam) :
    ∃ (pre : Run config checks x u) (post : Run config checks v y),
      tail = (pre.snoc step).append post ∧ u.fork < .glamsterdam ∧
        (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
  obtain ⟨pre, post, split⟩ := tail.contains_split step member
  exact ⟨pre, post, split, Nat.lt_of_le_of_lt
    (Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)) early,
    UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)⟩

end DirectSafety.Apriori.Internal

/-- The number of block steps of a run. -/
def Run.blockCount {first last : ForkedBeaconState preset} :
    Run config checks first last → Nat
  | .nil => 0
  | .snoc pre (.slot _) => pre.blockCount
  | .snoc pre (.block ..) => pre.blockCount + 1

/-- The blocks of two runs in sequence are the blocks of each. -/
theorem Run.blockCount_append {a b c : ForkedBeaconState preset}
    (pre : Run config checks a b) (tail : Run config checks b c) :
    (pre.append tail).blockCount = pre.blockCount + tail.blockCount := by
  induction tail with
  | nil => rfl
  | snoc tail step ih =>
    cases step <;> simp only [Run.append, Run.blockCount, ih, Nat.add_assoc]

/-- A run of empty slots, when the last of them stays before the next fork.

The run has no block step.

It contains the slot step from each state on the way, so an epoch call can name it. -/
private theorem run_of_advanceSlots {fork : Fork} (count : Nat)
    {state after : BeaconState preset fork}
    (advanced : advanceSlots config checks count state = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      after.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    ∃ run : Run config checks ⟨fork, state⟩ ⟨fork, after⟩, run.blockCount = 0 ∧
      ∀ k < count, ∀ {mid : BeaconState preset fork},
        advanceSlots config checks k state = .ok mid →
        ∃ (stepped : ForkedBeaconState preset)
          (across : advanceSlotAcross config checks ⟨fork, mid⟩ = .ok stepped),
          run.Contains (.slot across) := by
  induction count generalizing state with
  | zero =>
    cases advanced
    exact ⟨.nil, rfl, fun k below => absurd below (Nat.not_lt_zero k)⟩
  | succ count ih =>
    obtain ⟨next, stepped, rest⟩ := bind_ok_iff.mp advanced
    have slotsEq := advanceSlots_slot count rest
    have nextSlot := advanceSlot_slot stepped
    -- No upgrade is due at the slot the step reaches, so the step stays in the fork.
    have across : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, next⟩ := by
      rw [advanceSlotAcross_of_before (fun nextFork scheduled => by
        have := before nextFork scheduled
        omega), stepped]
      rfl
    obtain ⟨tail, none, slots⟩ := ih rest
    refine ⟨(Run.nil.snoc (.slot across)).append tail, ?_, fun k below mid reached => ?_⟩
    · rw [Run.blockCount_append, none]
      rfl
    cases k with
    | zero =>
      -- No slot yet: the step from `state` is the first step of the run.
      simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at reached
      subst reached
      exact ⟨_, across, (Run.contains_append _ tail _).mpr (.inl (.last _ _))⟩
    | succ k =>
      -- The first slot leads to `next`, and the rest of the walk is that of the later slots.
      simp only [advanceSlots, bind_ok_iff, stepped, Except.ok.injEq, exists_eq_left'] at reached
      obtain ⟨stepped', across', member⟩ := slots k (by omega) reached
      exact ⟨stepped', across', (Run.contains_append _ tail _).mpr (.inr member)⟩

/-- A run from a state to the state at a later slot, when the slot stays before the next fork. -/
theorem run_of_processSlots {fork : Fork} {state after : BeaconState preset fork} {slot : Slot}
    (processed : processSlots config checks state slot = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, state⟩ ⟨fork, after⟩) := by
  have lastSlot := (processSlots_slot processed).2
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
  obtain ⟨_, _, advanced⟩ := processed
  obtain ⟨run, -⟩ := run_of_advanceSlots _ advanced (by simpa only [lastSlot] using before)
  exact ⟨run⟩

/-- The slots up to a block and the block, when its slot is before the next fork.

The slots form a run with no block step, to the state that the block applies to.

No upgrade is due at that state, so the block is one step of a run after them. -/
theorem run_of_stateTransition {fork : Fork} {state after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (transitioned : stateTransition config checks engine state signed true = .ok after)
    (before : ∀ next ∈ config.nextFork fork,
      signed.message.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    ∃ (advanced : BeaconState preset fork) (slots : Run config checks ⟨fork, state⟩
      ⟨fork, advanced⟩) (_ : upgradeDue config ⟨fork, advanced⟩ = false)
      (_ : applySignedBlock config checks engine advanced signed true = .ok after),
      slots.blockCount = 0 ∧
      ∀ k < signed.message.slot.toNat - state.slot.toNat, ∀ {mid : BeaconState preset fork},
        advanceSlots config checks k state = .ok mid →
        ∃ (stepped : ForkedBeaconState preset)
          (across : advanceSlotAcross config checks ⟨fork, mid⟩ = .ok stepped),
          slots.Contains (.slot across) := by
  simp only [stateTransition, bind_ok_iff] at transitioned
  obtain ⟨advanced, slotsOk, applied⟩ := transitioned
  have advancedSlot := (processSlots_slot slotsOk).2
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, run⟩ := slotsOk
  obtain ⟨slots, walk⟩ := run_of_advanceSlots _ run (by simpa only [advancedSlot] using before)
  exact ⟨advanced, slots, upgradeDue_of_before fun next scheduled =>
    advancedSlot ▸ before next scheduled, applied, walk⟩

/-- Each block spends its state's free slot, and each slot step supplies at most one more.

A slot is free when the latest block header is before it. -/
private theorem Run.blockCount_le {first last : ForkedBeaconState preset}
    (run : Run config checks first last) :
    run.blockCount +
      (if last.state.latestBlockHeader.slot < last.state.slot then 1 else 0) +
        first.state.slot.toNat ≤ last.state.slot.toNat + 1 := by
  induction run with
  | nil =>
    simp only [Run.blockCount]
    split <;> omega
  | @snoc middle last pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      have moved : last.state.slot.toNat = middle.state.slot.toNat + 1 :=
        (congrArg UInt64.toNat (processUpgrades_slot upgraded)).trans (advanceSlot_slot advancedOk)
      simp only [Run.blockCount]
      split at ih <;> split <;> omega
    | @block fork before after engine signed due ok =>
      have processed := (applySignedBlock_ok ok).2.1
      obtain ⟨atSlot, newer, -⟩ := processBlock_parentRoot processed
      obtain ⟨_, _, kept⟩ := latestBlockHeader_processBlock processed
      have slot := (frame_processBlock processed).slot
      -- The block uses the free slot of the state before it, and leaves none after it.
      have free : before.latestBlockHeader.slot < before.slot := atSlot ▸ newer
      have spent : ¬ after.latestBlockHeader.slot < after.slot := by
        rw [kept, slot, ← atSlot]
        exact UInt64.lt_irrefl _
      have slotNat : after.slot.toNat = before.slot.toNat := congrArg UInt64.toNat slot
      simp only [Run.blockCount, spent, ↓reduceIte]
      simp only [free, ↓reduceIte] at ih
      omega

/-- A run has at most one block step for each slot of its range. -/
theorem Run.blocks_le_slots {first last : ForkedBeaconState preset}
    (run : Run config checks first last) {a b : Nat} (low : a ≤ first.state.slot.toNat)
    (high : last.state.slot.toNat ≤ b) : run.blockCount ≤ b - a + 1 := by
  have := run.blockCount_le
  split at this <;> omega

/-- A later epoch of the same period is the same epoch, or it does not start a period. -/
private theorem epoch_same_or_not_start {period earlier later : Nat} (le : earlier ≤ later)
    (same : later / max 1 period = earlier / max 1 period) :
    later = earlier ∨ later % period ≠ 0 := by
  by_cases start : later % period = 0
  · left
    rcases Nat.eq_zero_or_pos period with zero | positive
    · subst zero
      simp only [Nat.mod_zero] at start
      omega
    · have divides := Nat.div_add_mod later period
      have rest := Nat.div_add_mod earlier period
      have same' : later / period = earlier / period := by
        simpa only [Nat.max_eq_right (Nat.succ_le_of_lt positive)] using same
      rw [start, same'] at divides
      omega
  · exact .inr start

/-- Induct over a run inside one period of epochs, with the run so far. -/
theorem Run.induction_of_same_period {x : ForkedBeaconState preset} (period : Epoch)
    (motive : (z : ForkedBeaconState preset) → Run config checks x z → Prop)
    (start : motive x .nil)
    (blockStep : ∀ {f : Fork} {s t : BeaconState preset f} (engine : ExecutionEngine preset f)
      (signed : SignedBeaconBlock preset f) (due : upgradeDue config ⟨f, s⟩ = false)
      (ok : applySignedBlock config checks engine s signed true = .ok t)
      (pre : Run config checks x ⟨f, s⟩), f < .glamsterdam → motive ⟨f, s⟩ pre →
        motive ⟨f, t⟩ (pre.snoc (.block engine signed due ok)))
    (slotStep : ∀ {middle last : ForkedBeaconState preset} (pre : Run config checks x middle)
      (ok : advanceSlotAcross config checks middle = .ok last), last.fork < .glamsterdam →
      (getCurrentEpoch last.state = getCurrentEpoch middle.state ∨
        getCurrentEpoch last.state % period ≠ 0) →
      motive middle pre → motive last (pre.snoc (.slot ok)))
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam)
    (same : (getCurrentEpoch y.state).toNat / max 1 period.toNat =
      (getCurrentEpoch x.state).toNat / max 1 period.toNat) :
    motive y tail := by
  induction tail with
  | nil => exact start
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have high := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    have midSame : (getCurrentEpoch middle.state).toNat / max 1 period.toNat =
        (getCurrentEpoch x.state).toNat / max 1 period.toNat := by
      have above := Nat.div_le_div_right (c := max 1 period.toNat) high
      have below := Nat.div_le_div_right (c := max 1 period.toNat) low
      omega
    have prior := ih middleEarly midSame
    cases step with
    | block engine signed due ok => exact blockStep engine signed due ok pre early prior
    | slot ok =>
      refine slotStep pre ok early ?_ prior
      rcases epoch_same_or_not_start high (same.trans midSame.symm) with equal | inside
      · exact .inl (UInt64.toNat_inj.mp equal)
      · refine .inr fun zero => inside ?_
        simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat zero

end EthLib.Consensus
