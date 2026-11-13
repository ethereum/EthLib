module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.RootLinks
public import EthLib.Consensus.Proofs.Transition.Trace

/-!
# Proofs: each checkpoint of a beacon state names a block of its own chain

A chain predicate holds the roots allowed at each slot.

It is meant as the latest block of a chain at or before each slot.

A state agrees with it from an anchor slot on when the following holds.

Each root that the state records from the anchor on is a root of the chain at its slot.

Each checkpoint whose epoch starts above the anchor names a root of the chain at that start.

A block, the slots and the upgrades keep this, for a chain extended by the roots they record.

A state with the invariant of valid blocks agrees with every chain from its own slot on.

Along a run, the chain is the roots that the states of the run record.

With ordered links in each state, the finalized block is at or before the current justified one.

Each checkpoint names the block at the start of its epoch, as Gasper §4.1 defines checkpoints.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A state agrees with a chain from an anchor slot on.

The chain holds the roots allowed at each slot, meant as the latest block at or before it.

Nothing is claimed about roots below the anchor, or checkpoints that start at or below it. -/
structure ChainRoots {fork : Fork} (anchor : Slot) (chain : Slot → Root → Prop)
    (state : BeaconState preset fork) : Prop where
  /-- The state is at or above the anchor. -/
  above : anchor ≤ state.slot
  /-- Each root that the state records from the anchor on is the root of the chain at its slot. -/
  window : ∀ (slot : Slot) (root : Root), anchor ≤ slot →
    getBlockRootAtSlot state slot = .ok root → chain slot root
  /-- Each checkpoint whose epoch starts above the anchor starts before the slot of the state.

  Its root is the root of the chain at the first slot of its epoch. -/
  checkpoints : ∀ checkpoint ∈ [state.currentJustifiedCheckpoint,
      state.previousJustifiedCheckpoint, state.finalizedCheckpoint],
    anchor.toNat < checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat →
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat ∧
        chain (checkpoint.epoch * preset.SLOTS_PER_EPOCH) checkpoint.root

/-- In 64 bits, the first slot of an epoch is the product of the epoch and the slots per epoch.

That holds when the product fits. -/
private theorem toNat_epoch_mul {epoch : Epoch}
    (fits : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    (epoch * preset.SLOTS_PER_EPOCH).toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt fits]

/-- A larger chain agrees with the state, if it holds the old one between the anchor and the state.
-/
theorem ChainRoots.mono {fork : Fork} {anchor : Slot} {chain wider : Slot → Root → Prop}
    {state : BeaconState preset fork} (holds : ChainRoots anchor chain state)
    (le : ∀ (slot : Slot) (root : Root), anchor ≤ slot → slot < state.slot →
      chain slot root → wider slot root) :
    ChainRoots anchor wider state := by
  refine ⟨holds.above, fun slot root above read => le slot root above
    (getBlockRootAtSlot_read read).1 (holds.window slot root above read), ?_⟩
  intro checkpoint mem late
  obtain ⟨before, chained⟩ := holds.checkpoints checkpoint mem late
  have fits := state.slot.toNat_lt
  have product := toNat_epoch_mul (preset := preset) (epoch := checkpoint.epoch) (by omega)
  refine ⟨before, le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    (UInt64.lt_iff_toNat_lt.mpr (by omega)) chained⟩

/-- Two states with the same slot, roots and checkpoints agree with the same chains. -/
theorem ChainRoots.congr {fork post : Fork} {anchor : Slot} {chain : Slot → Root → Prop}
    {state : BeaconState preset fork} {other : BeaconState preset post}
    (slot : other.slot = state.slot) (roots : other.blockRoots = state.blockRoots)
    (current : other.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint)
    (previous : other.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (finalized : other.finalizedCheckpoint = state.finalizedCheckpoint)
    (holds : ChainRoots anchor chain state) : ChainRoots anchor chain other := by
  have reads := getBlockRootAtSlot_congr slot roots
  refine ⟨by rw [slot]; exact holds.above,
    fun index root above read => holds.window index root above (by rw [← reads]; exact read), ?_⟩
  intro checkpoint mem late
  rw [current, previous, finalized] at mem
  rw [slot]
  exact holds.checkpoints checkpoint mem late

/-- A state with the invariant of valid blocks agrees with every chain from its own slot on.

Its checkpoint epochs are ordered and end at most at its previous epoch.

So each checkpoint epoch starts at or below the slot of the state.

The state records no root at or above its own slot, so the claim on roots is empty. -/
theorem ChainRoots.of_invariant {fork : Fork} {state : BeaconState preset fork}
    (holds : Invariant state) (chain : Slot → Root → Prop) :
    ChainRoots state.slot chain state := by
  refine ⟨UInt64.le_refl _, fun slot root above read =>
    absurd (getBlockRootAtSlot_read read).1 (UInt64.not_lt.mpr above), ?_⟩
  intro checkpoint mem late
  exfalso
  have ordered := holds.ordered
  have settled := holds.settled
  have previous := getPreviousEpoch_le state
  unfold CheckpointsOrdered at ordered
  unfold JustifiedSettled at settled
  rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le] at ordered
  rw [UInt64.le_iff_toNat_le] at settled previous
  -- Each checkpoint epoch is at most the current epoch.
  have epochLe : checkpoint.epoch.toNat ≤ state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [← getCurrentEpoch_toNat]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> omega
  have scaled := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochLe
  have whole := Nat.div_mul_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  omega

section Transition

variable {fork : Fork} {anchor : Slot} {chain : Slot → Root → Prop}

/-- After one slot, the finalized checkpoint is one of the three checkpoints before it. -/
private theorem advanceSlot_finalized {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after) :
    after.finalizedCheckpoint = state.finalizedCheckpoint ∨
      after.finalizedCheckpoint = state.previousJustifiedCheckpoint ∨
      after.finalizedCheckpoint = state.currentJustifiedCheckpoint := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    dsimp only
    rw [frame.finalized]
    rcases processJustificationAndFinalization_ok justifiedOk with same | ⟨_, _, _, weighed⟩
    · left
      rw [same, cachedFrame.finalized]
    · rw [← cachedFrame.finalized, ← cachedFrame.previousJustified,
        ← cachedFrame.currentJustified]
      exact (weighJustificationAndFinalization_checkpoints weighed).2.2.1
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact .inl cachedFrame.finalized

/-- After one slot, each checkpoint is a checkpoint before it, or names a recorded root.

That root is the one that the state before records at the start of its epoch. -/
private theorem advanceSlot_checkpoint_cases
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after) :
    ∀ checkpoint ∈ [after.currentJustifiedCheckpoint, after.previousJustifiedCheckpoint,
        after.finalizedCheckpoint],
      checkpoint ∈ [state.currentJustifiedCheckpoint, state.previousJustifiedCheckpoint,
          state.finalizedCheckpoint] ∨
        getBlockRoot state checkpoint.epoch = .ok checkpoint.root := by
  intro checkpoint mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
  rcases mem with rfl | rfl | rfl
  · by_cases same : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
    · exact .inl (.inl same)
    · exact .inr (advanceSlot_getBlockRoot_currentJustified_of_ne window computed same).2.1
  · rcases advanceSlot_previousJustified computed with same | ⟨same, -⟩
    · exact .inl (.inr (.inl same))
    · exact .inl (.inl same)
  · rcases advanceSlot_finalized computed with same | same | same
    · exact .inl (.inr (.inr same))
    · exact .inl (.inr (.inl same))
    · exact .inl (.inl same)

/-- The upgrades due at a slot keep the finalized checkpoint. -/
private theorem processUpgrades_finalized {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    after.state.finalizedCheckpoint = forked.state.finalizedCheckpoint :=
  processUpgrades_induction
    (property := fun state => state.state.finalizedCheckpoint = forked.state.finalizedCheckpoint)
    (fun same stepOk => (upgradeFrame_upgradeNext stepOk).finalized.trans same) rfl computed

/-- A header with a state root other than zero stays the same through slots across forks. -/
private theorem advanceSlotsAcross_latestBlockHeader_of_ne :
    ∀ (count : Nat) {forked after : ForkedBeaconState preset},
      advanceSlotsAcross config checks count forked = .ok after →
      forked.state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 →
      after.state.latestBlockHeader = forked.state.latestBlockHeader
  | 0, forked, after, computed, _ => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    rw [← computed]
  | count + 1, forked, after, computed, filled => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨-, -, -, _, -, header⟩ := advanceSlotAcross_cases nextOk
    simp only [filled, ↓reduceIte] at header
    rw [advanceSlotsAcross_latestBlockHeader_of_ne count rest (header ▸ filled), header]

/-- The root of the header after a slot is that of the header at the end, or of the header before.

The slots go across forks.

The header before counts only when the slot leaves it unfilled.

Then the state before hashes to zero. -/
private theorem hashTreeRoot_latestBlockHeader_advanceSlotsAcross {count : Nat}
    {forked next last : ForkedBeaconState preset}
    (step : advanceSlotAcross config checks forked = .ok next)
    (rest : advanceSlotsAcross config checks count next = .ok last) {root : Root}
    (rooted : hashTreeRoot next.state.latestBlockHeader = .ok root) :
    hashTreeRoot last.state.latestBlockHeader = .ok root ∨
      (hashTreeRoot forked.state = .ok (Vector.replicate 32 0) ∧
        hashTreeRoot forked.state.latestBlockHeader = .ok root) := by
  obtain ⟨-, -, -, stateRoot, hashed, header⟩ := advanceSlotAcross_cases step
  by_cases filled : next.state.latestBlockHeader.stateRoot = Vector.replicate 32 0
  · obtain ⟨zero, same⟩ := header_unfilled_of_filled header filled
    rw [same] at rooted
    exact .inr ⟨zero ▸ hashed, rooted⟩
  · exact .inl (by
      rw [advanceSlotsAcross_latestBlockHeader_of_ne count rest filled]
      exact rooted)

/-- One slot keeps the agreement, if the chain holds the root that the slot records.

The buffer of roots must cover two epochs. -/
theorem ChainRoots.of_advanceSlot
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {state after : BeaconState preset fork} (holds : ChainRoots anchor chain state)
    (computed : advanceSlot config checks state = .ok after)
    (recorded : ∀ (slot : Slot) (root : Root), state.slot ≤ slot →
      getBlockRootAtSlot after slot = .ok root → chain slot root) :
    ChainRoots anchor chain after := by
  have succ := advanceSlot_slot computed
  have aboveNat := UInt64.le_iff_toNat_le.mp holds.above
  refine ⟨UInt64.le_iff_toNat_le.mpr (by omega), ?_, ?_⟩
  · intro slot root above read
    rcases getBlockRootAtSlot_advanceSlot_cases computed read with ⟨-, old⟩ | ⟨same, -⟩
    · exact holds.window slot root above old
    · exact recorded slot root (same ▸ UInt64.le_refl _) read
  · intro checkpoint mem late
    rcases advanceSlot_checkpoint_cases window computed checkpoint mem with old | rooted
    · obtain ⟨before, chained⟩ := holds.checkpoints checkpoint old late
      exact ⟨by omega, chained⟩
    · -- A new checkpoint names the root that the state before records at its start.
      obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp rooted
      obtain ⟨fits, startEq⟩ := mulChecked_ok_iff.mp startOk
      have startIs : start = checkpoint.epoch * preset.SLOTS_PER_EPOCH :=
        UInt64.toNat_inj.mp (by rw [toNat_epoch_mul fits]; exact startEq)
      have before := UInt64.lt_iff_toNat_lt.mp (getBlockRootAtSlot_read read).1
      refine ⟨by omega, ?_⟩
      rw [← startIs]
      exact holds.window start _ (UInt64.le_iff_toNat_le.mpr (by omega)) read

/-- One slot with its upgrades keeps the agreement, if the chain holds the root it records.

The buffer of roots must cover two epochs. -/
theorem ChainRoots.of_advanceSlotAcross
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {forked after : ForkedBeaconState preset} (holds : ChainRoots anchor chain forked.state)
    (computed : advanceSlotAcross config checks forked = .ok after)
    (recorded : ∀ (slot : Slot) (root : Root), forked.state.slot ≤ slot →
      getBlockRootAtSlot after.state slot = .ok root → chain slot root) :
    ChainRoots anchor chain after.state := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  have slot := processUpgrades_slot upgraded
  have roots := processUpgrades_blockRoots upgraded
  have justified := processUpgrades_justified upgraded
  have reads := getBlockRootAtSlot_congr slot roots
  refine (ChainRoots.of_advanceSlot window holds advancedOk ?_).congr slot roots justified.2
    justified.1 (processUpgrades_finalized upgraded)
  intro index root atLeast read
  exact recorded index root atLeast (by rw [reads]; exact read)

/-- Slots, with the upgrades on the way, keep the agreement for the chain they extend.

From the slot of the first state on, the chain gains the root of the header of the last state.

When the first state hashes to the zero root, it also gains the root of the first header.

The buffer of roots must cover two epochs. -/
theorem ChainRoots.of_advanceSlotsAcross
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {count : Nat} {forked after : ForkedBeaconState preset}
    (holds : ChainRoots anchor chain forked.state)
    (computed : advanceSlotsAcross config checks count forked = .ok after) :
    ChainRoots anchor (fun slot root => chain slot root ∨ (forked.state.slot ≤ slot ∧
      (hashTreeRoot after.state.latestBlockHeader = .ok root ∨
        (hashTreeRoot forked.state = .ok (Vector.replicate 32 0) ∧
          hashTreeRoot forked.state.latestBlockHeader = .ok root)))) after.state := by
  induction count generalizing forked chain with
  | zero =>
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds.mono fun _ _ _ _ held => .inl held
  | succ count ih =>
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    have succ := (advanceSlotAcross_cases nextOk).1
    -- The first slot records the root of the next header, which the wider chain holds.
    have one : ChainRoots anchor (fun slot root => chain slot root ∨ (forked.state.slot ≤ slot ∧
        (hashTreeRoot after.state.latestBlockHeader = .ok root ∨
          (hashTreeRoot forked.state = .ok (Vector.replicate 32 0) ∧
            hashTreeRoot forked.state.latestBlockHeader = .ok root)))) next.state := by
      refine ChainRoots.of_advanceSlotAcross window (holds.mono fun _ _ _ _ held => .inl held)
        nextOk ?_
      intro slot root atLeast read
      rcases (advanceSlotAcross_cases nextOk).2.2.1 read with ⟨below, -⟩ | ⟨-, rooted⟩
      · exact absurd atLeast (UInt64.not_le.mpr below)
      · exact .inr ⟨atLeast, hashTreeRoot_latestBlockHeader_advanceSlotsAcross nextOk rest rooted⟩
    refine (ih one rest).mono ?_
    rintro slot root - - (held | ⟨later, rooted | ⟨-, rooted⟩⟩)
    · exact held
    · have := UInt64.le_iff_toNat_le.mp later
      exact .inr ⟨UInt64.le_iff_toNat_le.mpr (by omega), .inl rooted⟩
    · have := UInt64.le_iff_toNat_le.mp later
      exact .inr ⟨UInt64.le_iff_toNat_le.mpr (by omega),
        hashTreeRoot_latestBlockHeader_advanceSlotsAcross nextOk rest rooted⟩

/-- Slots in one fork keep the agreement for the chain they extend.

From the slot of the first state on, the chain gains the root of the header of the last state.

When the first state hashes to the zero root, it also gains the root of the first header.

The buffer of roots must cover two epochs. -/
private theorem ChainRoots.of_advanceSlots
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∀ (count : Nat) {chain : Slot → Root → Prop} {state after : BeaconState preset fork},
      ChainRoots anchor chain state → advanceSlots config checks count state = .ok after →
      ChainRoots anchor (fun slot root => chain slot root ∨ (state.slot ≤ slot ∧
        (hashTreeRoot after.latestBlockHeader = .ok root ∨
          (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
            hashTreeRoot state.latestBlockHeader = .ok root)))) after
  | 0, chain, state, after, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds.mono fun _ _ _ _ held => .inl held
  | count + 1, chain, state, after, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    have succ := advanceSlot_slot nextOk
    -- The first slot records the root of the next header, which the wider chain holds.
    have one : ChainRoots anchor (fun slot root => chain slot root ∨ (state.slot ≤ slot ∧
        (hashTreeRoot after.latestBlockHeader = .ok root ∨
          (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
            hashTreeRoot state.latestBlockHeader = .ok root)))) next := by
      refine ChainRoots.of_advanceSlot window (holds.mono fun _ _ _ _ held => .inl held)
        nextOk ?_
      intro slot root atLeast read
      rcases getBlockRootAtSlot_advanceSlot_cases nextOk read with ⟨below, -⟩ | ⟨-, rooted⟩
      · exact absurd atLeast (UInt64.not_le.mpr below)
      · exact .inr ⟨atLeast, hashTreeRoot_latestBlockHeader_advanceSlots nextOk rest rooted⟩
    refine (ChainRoots.of_advanceSlots window count one rest).mono ?_
    rintro slot root - - (held | ⟨later, rooted | ⟨-, rooted⟩⟩)
    · exact held
    · have := UInt64.le_iff_toNat_le.mp later
      exact .inr ⟨UInt64.le_iff_toNat_le.mpr (by omega), .inl rooted⟩
    · have := UInt64.le_iff_toNat_le.mp later
      exact .inr ⟨UInt64.le_iff_toNat_le.mpr (by omega),
        hashTreeRoot_latestBlockHeader_advanceSlots nextOk rest rooted⟩

/-- A block keeps the agreement for the chain it extends.

From the slot of the state before on, the chain gains the parent root of the block.

When the state before hashes to the zero root, it also gains the root of its latest header.

The buffer of roots must cover two epochs. -/
theorem ChainRoots.of_stateTransition
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {engine : ExecutionEngine preset fork} {state post : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (holds : ChainRoots anchor chain state)
    (computed : stateTransition config checks engine state signed validateResult = .ok post) :
    ChainRoots anchor (fun slot root => chain slot root ∨ (state.slot ≤ slot ∧
      (root = signed.message.parentRoot ∨
        (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
          hashTreeRoot state.latestBlockHeader = .ok root)))) post := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨-, -, slotsOk⟩ := slotsOk
  have parent := (processBlock_parentRoot blockOk).2.2
  have frame := frame_processBlock blockOk
  refine ((ChainRoots.of_advanceSlots window _ holds slotsOk).congr frame.slot
    (processBlock_blockRoots blockOk) frame.currentJustified frame.previousJustified
    frame.finalized).mono ?_
  rintro slot root - - (held | ⟨later, rooted | zero⟩)
  · exact .inl held
  · exact .inr ⟨later, .inl (Except.ok.inj (rooted.symm.trans parent))⟩
  · exact .inr ⟨later, .inr zero⟩

/-- A step of a chain keeps the agreement, if the chain holds the root that a slot records.

A block step changes no root and no checkpoint.

The buffer of roots must cover two epochs. -/
theorem ChainRoots.of_chainStep
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {forked after : ForkedBeaconState preset} (holds : ChainRoots anchor chain forked.state)
    (step : ChainStep config checks forked after)
    (recorded : ∀ (slot : Slot) (root : Root), forked.state.slot ≤ slot →
      getBlockRootAtSlot after.state slot = .ok root → chain slot root) :
    ChainRoots anchor chain after.state := by
  cases step with
  | slot computed => exact ChainRoots.of_advanceSlotAcross window holds computed recorded
  | block engine signed validateResult applied =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
    have frame := frame_processBlock blockOk
    exact holds.congr frame.slot (processBlock_blockRoots blockOk) frame.currentJustified
      frame.previousJustified frame.finalized

end Transition

/-! ## One run -/

/-- The states of a run, from the first to the last. -/
def Run.states {first : ForkedBeaconState preset} :
    {last : ForkedBeaconState preset} → Run config checks first last →
      List (ForkedBeaconState preset)
  | _, .nil => [first]
  | last, .snoc pre _ => pre.states ++ [last]

/-- A state of a run records a root at a slot. -/
def Run.Records {first last : ForkedBeaconState preset} (run : Run config checks first last)
    (slot : Slot) (root : Root) : Prop :=
  ∃ forked ∈ run.states, getBlockRootAtSlot forked.state slot = .ok root

/-- The last state of a run is one of its states. -/
private theorem Run.last_mem {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : last ∈ run.states := by
  cases run with
  | nil => exact List.mem_singleton_self _
  | snoc pre _ => exact List.mem_append_right _ (List.mem_singleton_self _)

/-- A step keeps the slot or moves it on by one. -/
private theorem Step.slot_cases {middle last : ForkedBeaconState preset}
    (step : Step config checks middle last) :
    last.state.slot.toNat = middle.state.slot.toNat + 1 ∨ last.state.slot = middle.state.slot := by
  cases step with
  | slot computed => exact .inl (advanceSlotAcross_cases computed).1
  | block engine signed due applied =>
    exact .inr (processBlock_slot (applySignedBlock_ok applied).2.1)

/-- Each state of a run is at or below the slot of the last state. -/
private theorem Run.slot_le_last {first last : ForkedBeaconState preset}
    (run : Run config checks first last) :
    ∀ forked ∈ run.states, forked.state.slot.toNat ≤ last.state.slot.toNat := by
  induction run with
  | nil =>
    intro forked mem
    rw [Run.states, List.mem_singleton] at mem
    rw [mem]
  | snoc pre step ih =>
    intro forked mem
    rcases List.mem_append.mp mem with mem | mem
    · have := ih forked mem
      rcases step.slot_cases with succ | same
      · omega
      · rw [same]
        exact this
    · rw [List.mem_singleton.mp mem]

/-- A root that a step makes readable was readable before it, or sits at the slot before it.

In the second case the step is a slot step. -/
private theorem Step.read_cases {middle last : ForkedBeaconState preset}
    (step : Step config checks middle last) {slot : Slot} {root : Root}
    (read : getBlockRootAtSlot last.state slot = .ok root) :
    (slot < middle.state.slot ∧ getBlockRootAtSlot middle.state slot = .ok root) ∨
      (slot = middle.state.slot ∧
        last.state.slot.toNat = middle.state.slot.toNat + 1) := by
  cases step with
  | slot computed =>
    obtain ⟨succ, -, cases, -⟩ := advanceSlotAcross_cases computed
    rcases cases read with old | ⟨same, -⟩
    · exact .inl old
    · exact .inr ⟨same, succ⟩
  | block engine signed due applied =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
    rw [getBlockRootAtSlot_congr (processBlock_slot blockOk) (processBlock_blockRoots blockOk)]
      at read
    exact .inl ⟨(getBlockRootAtSlot_read read).1, read⟩

/-- A root that a run records was recorded before its last step, or is new at the slot before it.

A new root sits at the slot of the state before a slot step, and the last state records it. -/
private theorem Run.records_snoc {first middle last : ForkedBeaconState preset}
    (pre : Run config checks first middle) (step : Step config checks middle last)
    {slot : Slot} {root : Root} (read : (pre.snoc step).Records slot root) :
    pre.Records slot root ∨ (slot = middle.state.slot ∧
      getBlockRootAtSlot last.state slot = .ok root ∧
      last.state.slot.toNat = middle.state.slot.toNat + 1) := by
  obtain ⟨forked, mem, got⟩ := read
  rcases List.mem_append.mp mem with mem | mem
  · exact .inl ⟨forked, mem, got⟩
  · rw [List.mem_singleton.mp mem] at got
    rcases step.read_cases got with ⟨-, old⟩ | ⟨same, succ⟩
    · exact .inl ⟨middle, pre.last_mem, old⟩
    · exact .inr ⟨same, got, succ⟩

/-- The last state of a run keeps the invariant of the first. -/
private theorem Run.invariant {first last : ForkedBeaconState preset}
    (holds : Invariant first.state) (run : Run config checks first last) :
    Invariant last.state := by
  induction run with
  | nil => exact holds
  | snoc pre step ih =>
    cases step with
    | slot computed => exact (advanceSlotAcross_invariant ih computed).1
    | block engine signed due applied =>
      exact (frame_processBlock (applySignedBlock_ok applied).2.1).invariant ih

/-- The last state of a run agrees with the roots that the run records, above its first slot.

The first state needs the invariant of valid blocks, and the buffer must cover two epochs. -/
theorem ChainRoots.of_run
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {first last : ForkedBeaconState preset} (holds : Invariant first.state)
    (run : Run config checks first last) :
    ChainRoots first.state.slot run.Records last.state := by
  induction run with
  | nil => exact ChainRoots.of_invariant holds _
  | snoc pre step ih =>
    refine ChainRoots.of_chainStep window (ih.mono ?_) step.chainStep ?_
    · rintro slot root - - ⟨forked, mem, read⟩
      exact ⟨forked, List.mem_append_left _ mem, read⟩
    · rintro slot root - read
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), read⟩

/-- Ordered root links order the roots that a run records, the earlier slot first.

The links of each state of the run must be in order for a map from roots.

Each root is recorded by a state of the run, at a slot from the first slot of the run on.

A slot step links its new root to the root of the slot before, so the order crosses states.

The buffer of roots must cover two epochs, and an epoch must have at least one slot. -/
theorem Run.le_of_records {β : Type*} [Preorder β] {block : Root → β}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {first last : ForkedBeaconState preset} (run : Run config checks first last)
    (links : ∀ forked ∈ run.states, ∀ link ∈ rootLinks forked.state, block link.1 ≤ block link.2)
    {older newer : Slot} {olderRoot newerRoot : Root} (above : first.state.slot ≤ older)
    (le : older ≤ newer) (olderRead : run.Records older olderRoot)
    (newerRead : run.Records newer newerRoot) :
    block olderRoot ≤ block newerRoot := by
  induction run generalizing older newer olderRoot newerRoot with
  | nil =>
    obtain ⟨forked, mem, read⟩ := olderRead
    rw [Run.states, List.mem_singleton] at mem
    subst mem
    exact absurd above (UInt64.not_le.mpr (getBlockRootAtSlot_read read).1)
  | @snoc middle last pre step ih =>
    have preLinks : ∀ forked ∈ pre.states, ∀ link ∈ rootLinks forked.state,
        block link.1 ≤ block link.2 := fun forked mem => links forked (List.mem_append_left _ mem)
    have bounded := pre.slot_le_last
    -- A root that the run before records is below the slot of the middle state.
    have early : ∀ {slot : Slot} {root : Root}, pre.Records slot root →
        slot.toNat < middle.state.slot.toNat := by
      rintro slot root ⟨forked, mem, read⟩
      have := UInt64.lt_iff_toNat_lt.mp (getBlockRootAtSlot_read read).1
      have := bounded forked mem
      omega
    have olderLe := UInt64.le_iff_toNat_le.mp le
    rcases pre.records_snoc step olderRead with olderPre | ⟨olderSame, olderLast, succ⟩ <;>
      rcases pre.records_snoc step newerRead with newerPre | ⟨newerSame, newerLast, newerSucc⟩
    · exact ih preLinks above le olderPre newerPre
    · -- The newer root is the new root of the slot step.
      have below := early olderPre
      have positiveSlot : 1 ≤ middle.state.slot := UInt64.le_iff_toNat_le.mpr (by simp; omega)
      have previous : (middle.state.slot - 1).toNat = middle.state.slot.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ positiveSlot]
        simp
      obtain ⟨-, fits, -, -⟩ := getBlockRootAtSlot_ok_iff.mp newerLast
      have twoRoots : 2 ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by omega
      have newerNat := congrArg UInt64.toNat newerSame
      obtain ⟨root, read⟩ := getBlockRootAtSlot_exists (state := last.state)
        (slot := middle.state.slot - 1) (by omega) (by omega) (by omega) (by omega)
      -- The root of the slot before is one that the middle state records.
      have kept : pre.Records (middle.state.slot - 1) root := by
        rcases step.read_cases read with ⟨-, old⟩ | ⟨same, -⟩
        · exact ⟨middle, pre.last_mem, old⟩
        · have := congrArg UInt64.toNat same
          omega
      have prior := ih preLinks above (UInt64.le_iff_toNat_le.mpr (by omega)) olderPre kept
      refine prior.trans (links last (List.mem_append_right _ (List.mem_singleton_self _))
        (root, newerRoot) (.inl ⟨middle.state.slot - 1, read, ?_⟩))
      rw [UInt64.sub_add_cancel, ← newerSame]
      exact newerLast
    · have := early newerPre
      have := congrArg UInt64.toNat olderSame
      omega
    · rw [olderSame, ← newerSame, newerLast] at olderLast
      cases olderLast
      exact le_rfl

/-- Along a run, the finalized block is at or before the current justified block.

The order is that of a map from roots that orders the links of each state of the run.

The finalized epoch must start after the first slot of the run.

The first state needs the invariant of valid blocks, and the buffer must cover two epochs. -/
theorem Run.finalized_le_currentJustified {β : Type*} [Preorder β] {block : Root → β}
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {first last : ForkedBeaconState preset} (holds : Invariant first.state)
    (run : Run config checks first last)
    (links : ∀ forked ∈ run.states, ∀ link ∈ rootLinks forked.state, block link.1 ≤ block link.2)
    (after : first.state.slot.toNat <
      last.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    block last.state.finalizedCheckpoint.root ≤
      block last.state.currentJustifiedCheckpoint.root := by
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
    · rw [zero] at after
      omega
    · exact positive
  have chained := ChainRoots.of_run window holds run
  have ordered := (run.invariant holds).ordered
  unfold CheckpointsOrdered at ordered
  rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le] at ordered
  obtain ⟨finalizedBefore, finalizedRead⟩ := chained.checkpoints _ (by simp) after
  have scaled := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (ordered.1.trans ordered.2)
  obtain ⟨currentBefore, currentRead⟩ :=
    chained.checkpoints last.state.currentJustifiedCheckpoint (by simp) (by omega)
  have bound := last.state.slot.toNat_lt
  have finalizedNat := toNat_epoch_mul (preset := preset)
    (epoch := last.state.finalizedCheckpoint.epoch) (by omega)
  have currentNat := toNat_epoch_mul (preset := preset)
    (epoch := last.state.currentJustifiedCheckpoint.epoch) (by omega)
  refine run.le_of_records positive window links ?_ ?_ finalizedRead currentRead
  · exact UInt64.le_iff_toNat_le.mpr (by omega)
  · exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- Each state of a run comes after the first state and before the last one, by chain steps. -/
private theorem Run.chainSteps_of_mem {first last : ForkedBeaconState preset}
    (run : Run config checks first last) :
    ∀ forked ∈ run.states, Relation.ReflTransGen (ChainStep config checks) first forked ∧
      Relation.ReflTransGen (ChainStep config checks) forked last := by
  induction run with
  | nil =>
    intro forked member
    rw [List.mem_singleton.mp member]
    exact ⟨.refl, .refl⟩
  | snoc pre step ih =>
    intro forked member
    rcases List.mem_append.mp member with older | newest
    · obtain ⟨before, after⟩ := ih forked older
      exact ⟨before, after.tail step.chainStep⟩
    · rw [List.mem_singleton.mp newest]
      exact ⟨(pre.chainSteps).tail step.chainStep, .refl⟩

/-- Along a run, the finalized block is at or before the current justified block.

The other case is a state that hashes to the zero root, between the first and the last state.

It is between them by chain steps, not necessarily a state of the run.

The map from roots orders the parent root of each block step before the root of its block.

The step is on any path of chain steps from the first state to the last one.

The root of its block takes the root of the state after the step as its state root.

The map must also order the pairs of the first state, and the pair that its first slot adds.

The first state is at slot zero, or has its latest header at its slot.

Or it records the root of that header at the slot before it.

The finalized epoch must start after the first slot of the run.

The first state needs the invariant of valid blocks, and the buffer must cover two epochs. -/
theorem Run.zeroPreimage_or_finalized_le_currentJustified {β : Type*} [Preorder β]
    {block : Root → β} [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {first last : ForkedBeaconState preset} (holds : Invariant first.state)
    (run : Run config checks first last)
    (recorded : first.state.slot = 0 ∨ first.state.latestBlockHeader.slot = first.state.slot ∨
      ∃ root,
        readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok root ∧
          hashTreeRoot first.state.latestBlockHeader = .ok root)
    (start : ∀ link ∈ rootLinks first.state, block link.1 ≤ block link.2)
    (opening : ∀ before stateRoot root : Root,
      (if first.state.slot = 0 then before = Vector.replicate 32 0 else
        readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok before) →
      hashTreeRoot first.state = .ok stateRoot →
      hashTreeRoot (if first.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
        { first.state.latestBlockHeader with stateRoot := stateRoot }
      else first.state.latestBlockHeader) = .ok root → block before ≤ block root)
    (ordered : ∀ (fork : Fork) (engine : ExecutionEngine preset fork)
      (pre post : BeaconState preset fork) (signed : SignedBeaconBlock preset fork)
      (validateResult : Bool) (stateRoot root : Root),
      Relation.ReflTransGen (ChainStep config checks) first ⟨fork, pre⟩ →
      applySignedBlock config checks engine pre signed validateResult = .ok post →
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, post⟩ last →
      hashTreeRoot post = .ok stateRoot →
      hashTreeRoot { signed.message with stateRoot := stateRoot } = .ok root →
      block signed.message.parentRoot ≤ block root)
    (after : first.state.slot.toNat <
      last.state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (∃ forked : ForkedBeaconState preset,
      Relation.ReflTransGen (ChainStep config checks) first forked ∧
      Relation.ReflTransGen (ChainStep config checks) forked last ∧
      hashTreeRoot forked.state = .ok (Vector.replicate 32 0)) ∨
    block last.state.finalizedCheckpoint.root ≤
      block last.state.currentJustifiedCheckpoint.root := by
  by_cases zero : ∃ forked : ForkedBeaconState preset,
      Relation.ReflTransGen (ChainStep config checks) first forked ∧
      Relation.ReflTransGen (ChainStep config checks) forked last ∧
      hashTreeRoot forked.state = .ok (Vector.replicate 32 0)
  · exact .inl zero
  refine .inr (run.finalized_le_currentJustified window holds ?_ after)
  intro middle member
  obtain ⟨toMiddle, fromMiddle⟩ := run.chainSteps_of_mem middle member
  -- The run up to this state has no zero preimage either, so its links are in order.
  rcases zeroPreimage_or_rootLinks_le_of_chainSteps toMiddle recorded start opening
      (fun fork engine pre post signed validateResult stateRoot root before applied rest =>
        ordered fork engine pre post signed validateResult stateRoot root before applied
          (rest.trans fromMiddle)) with
    ⟨forked, toForked, fromForked, hashed⟩ | links
  · exact absurd ⟨forked, toForked, fromForked.trans fromMiddle, hashed⟩ zero
  · exact links

end EthLib.Consensus
