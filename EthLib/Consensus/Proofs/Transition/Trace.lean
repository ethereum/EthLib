module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Transition.Genesis
import EthLib.Base.Proofs.MapM
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Proofs: a trace of the steps of a chain, with their inputs

A step of a chain says that one state follows from another, but it does not keep the block.

A run keeps each step with its inputs: the slot step, or the signed block and its engine.

So a theorem about a run can name the blocks of that run and the attestations in them.

Each step of a run is a step of a chain, so the invariants of chains hold along a run.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A genesis state built from deposits.

It need not be valid for launch. -/
def Genesis (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset) : Prop :=
  ∃ hash time deposits before,
    initializeBeaconStateFromEth1 config checks hash time deposits before = .ok g.state

/-- A genesis state built from deposits is before Altair. -/
theorem Genesis.before {g : ForkedBeaconState preset} (genesis : Genesis config checks g) :
    g.fork < .altair :=
  let ⟨_, _, _, before, _⟩ := genesis
  before

private theorem header_deposit {fork : Fork} {before after : BeaconState preset fork}
    {early : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks early before deposit = .ok after) :
    after.latestBlockHeader = before.latestBlockHeader := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok ok
  exact (frame_applyDeposit applied).latestBlockHeader

/-- A genesis state built from deposits has its latest block header at slot zero.

The state root of that header is zero. -/
theorem genesis_header {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) :
    g.state.latestBlockHeader.slot = 0 ∧
      g.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 := by
  obtain ⟨hash, time, deposits, before, initialized⟩ := genesis
  obtain ⟨time, root, deposited, activated, finalRoot, dep, act, stateEq⟩ :=
    initializeBeaconStateFromEth1_ok initialized
  have depositedHeader : deposited.latestBlockHeader =
      (emptyGenesisState config before time hash deposits.size.toUInt64 root).latestBlockHeader :=
    foldlM_ok_invariant (fun s => s.latestBlockHeader =
      (emptyGenesisState config before time hash deposits.size.toUInt64 root).latestBlockHeader)
      (fun _ _ _ same ok => by
        simp only [genesisDeposit, bind_ok_iff] at ok
        obtain ⟨_, _, ok⟩ := ok
        exact (header_deposit ok).trans same) rfl dep
  have activatedHeader : activated.latestBlockHeader = deposited.latestBlockHeader :=
    foldlM_ok_invariant (fun s => s.latestBlockHeader = deposited.latestBlockHeader)
      (fun _ _ _ same ok => by
        simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, set⟩ := ok
        exact (payloadInputs_setValidatorAt set).latestBlockHeader.trans same) rfl act
  rw [stateEq]
  change activated.latestBlockHeader.slot = 0 ∧
    activated.latestBlockHeader.stateRoot = Vector.replicate 32 0
  rw [activatedHeader, depositedHeader]
  exact ⟨rfl, rfl⟩

/-- One step of a run: a slot, or a signed block applied with its state root checked. -/
inductive Step (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Type where
  | slot {before after} (ok : advanceSlotAcross config checks before = .ok after) :
      Step config checks before after
  | block {fork : Fork} {before after : BeaconState preset fork}
      (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
      -- A block step of a run is applied on a state with no upgrade due.
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

/-- Prepending the empty run leaves a run unchanged. -/
theorem Run.nil_append {x y : ForkedBeaconState preset} (r : Run config checks x y) :
    Run.nil.append r = r := by
  induction r with
  | nil => rfl
  | snoc r step ih => exact congrArg (fun run => run.snoc step) ih

/-- Appending runs is associative. -/
theorem Run.append_assoc {a b c d : ForkedBeaconState preset} (one : Run config checks a b)
    (two : Run config checks b c) (three : Run config checks c d) :
    one.append (two.append three) = (one.append two).append three := by
  induction three with
  | nil => rfl
  | snoc three step ih => exact congrArg (fun run => run.snoc step) ih

/-- A run split at a step is the run before it and the run from the step. -/
theorem Run.snoc_append_eq {x a b c : ForkedBeaconState preset}
    (pre : Run config checks x a) (step : Step config checks a b)
    (post : Run config checks b c) :
    (pre.snoc step).append post = pre.append ((Run.nil.snoc step).append post) := by
  rw [Run.append_assoc]
  rfl

/-- A run from a state without a property to a state with it splits at a step that gains it. -/
theorem Run.split_at_flip {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (P : ForkedBeaconState preset → Prop) (missing : ¬P x) (held : P y) :
    ∃ (m n : ForkedBeaconState preset) (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      tail = (pre.snoc step).append post ∧ ¬P m ∧ P n := by
  induction tail with
  | nil => exact absurd held missing
  | @snoc middle last pre step ih =>
    by_cases inside : P middle
    · obtain ⟨m, n, a, one, rest, split, hm, hn⟩ := ih inside
      refine ⟨m, n, a, one, rest.snoc step, ?_, hm, hn⟩
      rw [split]
      rfl
    · exact ⟨middle, last, pre, step, .nil, rfl, inside, held⟩

/-- One step of a chain moves the current epoch on by at most one. -/
theorem ChainStep.epoch_le_succ {a b : ForkedBeaconState preset}
    (step : ChainStep config checks a b) :
    (getCurrentEpoch b.state).toNat ≤ (getCurrentEpoch a.state).toNat + 1 := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    simp only [processUpgrades_slot upgrades, advanceSlot_slot slotOk]
    rw [Nat.succ_div]
    split <;> omega
  | block engine signed validate ok =>
    simp only [getCurrentEpoch, (frame_processBlock (applySignedBlock_ok ok).2.1).slot]
    exact Nat.le_succ _

/-- A run from an epoch to a later one has a slot step that leaves a given epoch between them. -/
theorem Run.cross_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (k : Nat) (low : (getCurrentEpoch x.state).toNat ≤ k)
    (high : k < (getCurrentEpoch y.state).toNat) :
    ∃ (z n : ForkedBeaconState preset) (pre : Run config checks x z)
      (ok : advanceSlotAcross config checks z = .ok n) (rest : Run config checks n y),
      tail = (pre.snoc (Step.slot ok)).append rest ∧ (getCurrentEpoch z.state).toNat = k ∧
        (getCurrentEpoch n.state).toNat = k + 1 := by
  obtain ⟨m, n, pre, step, post, split, hm, hn⟩ :=
    Run.split_at_flip tail (fun z => k < (getCurrentEpoch z.state).toNat) (by omega) high
  have missing : ¬k < (getCurrentEpoch m.state).toNat := hm
  have gained : k < (getCurrentEpoch n.state).toNat := hn
  have bound := step.chainStep.epoch_le_succ
  have crossing : getCurrentEpoch m.state < getCurrentEpoch n.state :=
    UInt64.lt_iff_toNat_lt.mpr (by omega)
  obtain ⟨ok, rfl⟩ := step.eq_slot_of_crossing crossing
  exact ⟨m, n, pre, ok, post, split, by omega, by omega⟩

/-- A run that starts at or before an epoch and ends at or after it passes a state of that epoch. -/
theorem Run.exists_epoch_split {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (k : Nat)
    (low : (getCurrentEpoch x.state).toNat ≤ k) (high : k ≤ (getCurrentEpoch y.state).toNat) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks x z) (post : Run config checks z y),
      (getCurrentEpoch z.state).toNat = k ∧ tail = pre.append post := by
  by_cases last : k = (getCurrentEpoch y.state).toNat
  · exact ⟨y, tail, .nil, last.symm, rfl⟩
  · obtain ⟨z, n, pre, ok, rest, split, hz, -⟩ := Run.cross_split tail k low (by omega)
    exact ⟨z, pre, (Run.nil.snoc (Step.slot ok)).append rest, hz,
      split.trans (pre.snoc_append_eq (Step.slot ok) rest)⟩

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

/-- Slots that advance a state across forks form a run.

Unlike the slots of one fork, they may cross an upgrade. -/
theorem run_of_advanceSlotsAcross :
    ∀ (count : Nat) {x y : ForkedBeaconState preset},
      advanceSlotsAcross config checks count x = .ok y → Nonempty (Run config checks x y)
  | 0, x, y, computed => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨.nil⟩
  | count + 1, x, y, computed => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨middle, middleOk, rest⟩ := computed
    obtain ⟨tail⟩ := run_of_advanceSlotsAcross count rest
    exact ⟨(Run.nil.snoc (.slot middleOk)).append tail⟩

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

/-- A run has at most one block for each slot of the epochs that it touches. -/
theorem Run.blockCount_le_epochs {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) :
    tail.blockCount ≤
      ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat := by
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, Nat.sub_mul]
  have low := Nat.div_mul_le_self x.state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have high := Nat.lt_mul_div_succ y.state.slot.toNat positive
  rw [Nat.mul_comm] at high
  have blocks := tail.blocks_le_slots low (b :=
    (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat - 1) (by omega)
  have startLe := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat] at startLe
  have ordered := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat startLe
  rw [Nat.add_mul, Nat.one_mul] at blocks ⊢
  omega

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
      (pre : Run config checks x ⟨f, s⟩), motive ⟨f, s⟩ pre →
        motive ⟨f, t⟩ (pre.snoc (.block engine signed due ok)))
    (slotStep : ∀ {middle last : ForkedBeaconState preset} (pre : Run config checks x middle)
      (ok : advanceSlotAcross config checks middle = .ok last),
      (getCurrentEpoch last.state = getCurrentEpoch middle.state ∨
        getCurrentEpoch last.state % period ≠ 0) →
      motive middle pre → motive last (pre.snoc (.slot ok)))
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (same : (getCurrentEpoch y.state).toNat / max 1 period.toNat =
      (getCurrentEpoch x.state).toNat / max 1 period.toNat) :
    motive y tail := by
  induction tail with
  | nil => exact start
  | @snoc middle last pre step ih =>
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have high := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    have midSame : (getCurrentEpoch middle.state).toNat / max 1 period.toNat =
        (getCurrentEpoch x.state).toNat / max 1 period.toNat := by
      have above := Nat.div_le_div_right (c := max 1 period.toNat) high
      have below := Nat.div_le_div_right (c := max 1 period.toNat) low
      omega
    have prior := ih midSame
    cases step with
    | block engine signed due ok => exact blockStep engine signed due ok pre prior
    | slot ok =>
      refine slotStep pre ok ?_ prior
      rcases epoch_same_or_not_start high (same.trans midSame.symm) with equal | inside
      · exact .inl (UInt64.toNat_inj.mp equal)
      · refine .inr fun zero => inside ?_
        simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat zero

end EthLib.Consensus
