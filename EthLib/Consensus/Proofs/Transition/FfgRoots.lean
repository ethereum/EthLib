module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.FfgSlack
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Proofs: the justified roots of a chain come before the roots it records later

A state records the root of the latest block at each recent slot.

At two consecutive slots it records the same root, or a block and its child.

The parent root of a block is the root recorded at the slot before it, by the check of its header.

No theorem here states that.

Without a collision of header roots, these pairs order the roots by ancestry.

Each step of a chain keeps each justified checkpoint below the roots recorded from its epoch on.

The order is that of any map from roots to blocks that keeps each such pair in order.

The genesis checkpoints have the zero root, which comes before the root recorded at slot zero.

Justification then compares the block of each justified checkpoint with the block of a recent epoch.

Casper FFG §2 ignores a vote whose source is not an ancestor of its target.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {β : Type*} [Preorder β]
  {block : Root → β}

/-- The current justified checkpoint when the flag is set, and the previous one otherwise. -/
def recentJustified {fork : Fork} (state : BeaconState preset fork) (current : Bool) :
    Checkpoint :=
  if current then state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint

/-- The pairs of roots that a state records at two consecutive slots.

The zero root also comes before the root that the state records at slot zero. -/
def rootLinks {fork : Fork} (state : BeaconState preset fork) : Set (Root × Root) :=
  {link | (∃ slot : Slot, getBlockRootAtSlot state slot = .ok link.1 ∧
      getBlockRootAtSlot state (slot + 1) = .ok link.2) ∨
    (link.1 = Vector.replicate 32 0 ∧ getBlockRootAtSlot state 0 = .ok link.2)}

/-- The roots, ordered by the links that each state reachable from a first state records.

The order holds the links of every branch from that state, so two branches share it.

So it also holds every collision of header roots among reachable headers, which exist by counting.

It is ancestry only up to those collisions, so it does not serve a safety theorem for two chains.

Such a theorem needs the order of the states of the given runs, with a named collision search. -/
def ChainRoot (_config : Config) (_checks : SignatureChecks) (_first : ForkedBeaconState preset) :
    Type :=
  Root

/-- Two roots are in order when links of reached states lead from the older to the newer one. -/
instance ChainRoot.instPreorder (first : ForkedBeaconState preset) :
    Preorder (ChainRoot config checks first) where
  le older newer := Relation.ReflTransGen (fun older newer => ∃ forked,
    Relation.ReflTransGen (ChainStep config checks) first forked ∧
      (older, newer) ∈ rootLinks forked.state) older newer
  le_refl _ := .refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

/-- Each root as a root of the chains from a first state. -/
def toChainRoot (config : Config) (checks : SignatureChecks) (first : ForkedBeaconState preset)
    (root : Root) : ChainRoot config checks first :=
  root

/-- Each justified checkpoint is below the roots the state records from the first slot of its epoch.

The order is that of the blocks of a map from roots.

The recent epoch of the current justified checkpoint is the current epoch.

That of the previous justified checkpoint is the previous epoch.

The epoch of the checkpoint is at most its recent epoch.

Its first slot is below the slot of the state, unless it is the genesis checkpoint. -/
structure RootsAbove {fork : Fork} (block : Root → β) (state : BeaconState preset fork) :
    Prop where
  /-- The epoch of each justified checkpoint is at most its recent epoch. -/
  epoch : ∀ current : Bool, (recentJustified state current).epoch ≤
    (if current then getCurrentEpoch state else getPreviousEpoch state)
  /-- The first slot of each justified checkpoint is below the slot of the state.

  The genesis checkpoint, of epoch zero and of the zero root, is the exception. -/
  started : ∀ current : Bool,
    (recentJustified state current).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat ∨
      ((recentJustified state current).epoch = 0 ∧
        (recentJustified state current).root = Vector.replicate 32 0)
  /-- The block of each justified checkpoint is below that of each root recorded from its epoch on.
  -/
  below : ∀ (current : Bool) (slot : Slot) (root : Root),
    (recentJustified state current).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat →
      getBlockRootAtSlot state slot = .ok root →
        block (recentJustified state current).root ≤ block root

/-- Ordered links order the roots that a state records at two slots, the earlier one first. -/
private theorem le_of_rootLinks {fork : Fork} {state : BeaconState preset fork}
    (links : ∀ link ∈ rootLinks state, block link.1 ≤ block link.2) {low : Slot} {lowRoot : Root}
    (lowRead : getBlockRootAtSlot state low = .ok lowRoot) :
    ∀ (distance : Nat) {high : Slot} {highRoot : Root}, high.toNat = low.toNat + distance →
      getBlockRootAtSlot state high = .ok highRoot → block lowRoot ≤ block highRoot
  | 0, high, highRoot, sum, highRead => by
    have same : high = low := UInt64.toNat_inj.mp (by omega)
    rw [same, lowRead] at highRead
    cases highRead
    exact le_rfl
  | distance + 1, high, highRoot, sum, highRead => by
    have positive : 1 ≤ high := UInt64.le_iff_toNat_le.mpr (by simp; omega)
    have previous : (high - 1).toNat = low.toNat + distance := by
      rw [UInt64.toNat_sub_of_le _ _ positive]
      simp
      omega
    obtain ⟨root, read⟩ := getBlockRootAtSlot_between lowRead highRead (middle := high - 1)
      (by omega) (by omega)
    have prior := le_of_rootLinks links lowRead distance previous read
    refine prior.trans (links (root, highRoot) (.inl ⟨high - 1, read, ?_⟩))
    rw [UInt64.sub_add_cancel]
    exact highRead

/-- Ordered links order the roots that a state records for two epochs, the earlier one first. -/
theorem le_of_rootLinks_getBlockRoot {fork : Fork} {state : BeaconState preset fork}
    (links : ∀ link ∈ rootLinks state, block link.1 ≤ block link.2) {older newer : Epoch}
    {olderRoot newerRoot : Root} (le : older ≤ newer)
    (olderRead : getBlockRoot state older = .ok olderRoot)
    (newerRead : getBlockRoot state newer = .ok newerRoot) :
    block olderRoot ≤ block newerRoot := by
  obtain ⟨low, lowOk, lowRead⟩ := getBlockRoot_ok_iff.mp olderRead
  obtain ⟨high, highOk, highRead⟩ := getBlockRoot_ok_iff.mp newerRead
  have lowEq := (mulChecked_ok_iff.mp lowOk).2
  have highEq := (mulChecked_ok_iff.mp highOk).2
  have scaled := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (UInt64.le_iff_toNat_le.mp le)
  exact le_of_rootLinks links lowRead (high.toNat - low.toNat) (by omega) highRead

/-- The block of each justified checkpoint is below the block of each epoch from its own on. -/
theorem RootsAbove.le_of_epoch_le {fork : Fork} {state : BeaconState preset fork}
    (holds : RootsAbove block state) (current : Bool) {epoch : Epoch} {root : Root}
    (le : (recentJustified state current).epoch ≤ epoch)
    (read : getBlockRoot state epoch = .ok root) :
    block (recentJustified state current).root ≤ block root := by
  obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp read
  refine holds.below current start root ?_ read
  rw [(mulChecked_ok_iff.mp startOk).2]
  exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp le)

/-- The block of each justified checkpoint is below the block of its recent epoch. -/
theorem RootsAbove.le_of_getBlockRoot {fork : Fork} {state : BeaconState preset fork}
    (holds : RootsAbove block state) (current : Bool) (root : Root)
    (read : getBlockRoot state
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok root) :
    block (if current then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint).root ≤ block root :=
  holds.le_of_epoch_le current (holds.epoch current) read

/-- The genesis state built from deposits has each justified checkpoint below its later roots. -/
theorem RootsAbove.of_initializeBeaconStateFromEth1 {fork : Fork}
    {state : BeaconState preset fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    RootsAbove block state := by
  obtain ⟨slot, previous, current⟩ := initializeBeaconStateFromEth1_checkpoints computed
  refine ⟨fun current => ?_, fun current => ?_, fun _ _ _ _ read => ?_⟩
  · cases current <;> simp [recentJustified, previous, current, GENESIS_EPOCH]
  · cases current <;> simp [recentJustified, previous, current, GENESIS_EPOCH]
  · have before := UInt64.lt_iff_toNat_lt.mp (getBlockRootAtSlot_read read).1
    rw [slot] at before
    simp [GENESIS_SLOT] at before

/-- Two states with the same slot and buffer of roots have the same links. -/
private theorem rootLinks_congr {fork post : Fork} {state : BeaconState preset fork}
    {other : BeaconState preset post} (slot : other.slot = state.slot)
    (roots : other.blockRoots = state.blockRoots) : rootLinks other = rootLinks state := by
  simp only [rootLinks, getBlockRootAtSlot_congr slot roots]

/-- A state with the same slot, roots and justified checkpoints as another has its properties. -/
private theorem RootsAbove.congr {fork post : Fork} {state : BeaconState preset fork}
    {other : BeaconState preset post} (slot : other.slot = state.slot)
    (roots : other.blockRoots = state.blockRoots)
    (previous : other.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (current : other.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint)
    (holds : RootsAbove block state) : RootsAbove block other := by
  have recent : ∀ flag, recentJustified other flag = recentJustified state flag := by
    intro flag
    simp only [recentJustified, previous, current]
  have currentEq : getCurrentEpoch other = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  have previousEq : getPreviousEpoch other = getPreviousEpoch state := by
    simp only [getPreviousEpoch, currentEq]
  refine ⟨fun current => ?_, fun current => ?_, fun current index root bound read => ?_⟩
  · rw [recent, currentEq, previousEq]
    exact holds.epoch current
  · rw [recent, slot]
    exact holds.started current
  · rw [recent] at bound ⊢
    rw [getBlockRootAtSlot_congr slot roots] at read
    exact holds.below current index root bound read

/-- One slot keeps each justified checkpoint below the roots recorded from its epoch on.

The map from roots to blocks must keep in order the links of the state after the slot.

An epoch must have at least one slot, and the buffer of roots must cover two epochs. -/
private theorem RootsAbove.of_advanceSlot (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {fork : Fork} {state after : BeaconState preset fork} (holds : RootsAbove block state)
    (links : ∀ link ∈ rootLinks after, block link.1 ≤ block link.2)
    (computed : advanceSlot config checks state = .ok after) :
    RootsAbove block after := by
  have sum := advanceSlot_slot computed
  have currentLe : (getCurrentEpoch state).toNat ≤ (getCurrentEpoch after).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, sum]
    exact Nat.div_le_div_right (Nat.le_succ _)
  have previousLe : (getPreviousEpoch state).toNat ≤ (getPreviousEpoch after).toNat := by
    rw [getPreviousEpoch_toNat, getPreviousEpoch_toNat]
    omega
  have startLe : (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      state.slot.toNat := by
    rw [getCurrentEpoch_toNat]
    exact Nat.div_mul_le_self _ _
  have forward : ∀ {index : Slot} {root : Root}, getBlockRootAtSlot state index = .ok root →
      state.slot.toNat < index.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat →
        getBlockRootAtSlot after index = .ok root :=
    fun read recent => getBlockRootAtSlot_advanceSlot computed read recent
  -- A checkpoint below the roots of the state stays below those of the next slot.
  have kept : ∀ checkpoint : Checkpoint,
      (checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat ∨
        (checkpoint.epoch = 0 ∧ checkpoint.root = Vector.replicate 32 0)) →
      (∀ (slot : Slot) (root : Root), checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        slot.toNat → getBlockRootAtSlot state slot = .ok root →
          block checkpoint.root ≤ block root) →
      ∀ (slot : Slot) (root : Root), checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        slot.toNat → getBlockRootAtSlot after slot = .ok root →
          block checkpoint.root ≤ block root := by
    intro checkpoint started below slot root bound read
    obtain ⟨lt, fits, within, -⟩ := getBlockRootAtSlot_ok_iff.mp read
    have nonempty : 0 < preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by omega
    by_cases older : slot.toNat < state.slot.toNat
    · -- An older slot keeps its root.
      obtain ⟨prior, priorRead⟩ :=
        getBlockRootAtSlot_exists (state := state) older fits (by omega) nonempty
      have moved := forward priorRead (by omega)
      rw [read] at moved
      rw [Except.ok.inj moved]
      exact below slot prior bound priorRead
    have same : slot = state.slot := UInt64.toNat_inj.mp (by omega)
    by_cases zero : state.slot.toNat = 0
    · -- At genesis, the checkpoint has the zero root, linked to the root of slot zero.
      rcases started with early | ⟨-, genesis⟩
      · omega
      rw [genesis]
      have slotZero : slot = 0 := UInt64.toNat_inj.mp (by simp; omega)
      rw [slotZero] at read
      exact links (Vector.replicate 32 0, root) (.inr ⟨rfl, read⟩)
    -- The new root is linked to the root of the slot before.
    have one : 1 ≤ state.slot := UInt64.le_iff_toNat_le.mpr (by simp; omega)
    have pred : (state.slot - 1).toNat = state.slot.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ one]
      simp
    obtain ⟨prior, priorRead⟩ := getBlockRootAtSlot_exists (state := state)
      (slot := state.slot - 1) (by omega) (by omega) (by omega) nonempty
    have priorBound : checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        (state.slot - 1).toNat := by
      rcases started with early | ⟨genesis, -⟩
      · omega
      · rw [genesis]
        simp
    have moved := forward priorRead (by omega)
    refine (below _ prior priorBound priorRead).trans
      (links (prior, root) (.inl ⟨state.slot - 1, moved, ?_⟩))
    rw [UInt64.sub_add_cancel, ← same]
    exact read
  -- A checkpoint of a recent epoch is below the roots that the next slot records from it on.
  have fresh : ∀ checkpoint : Checkpoint,
      (checkpoint.epoch = getPreviousEpoch state ∨ checkpoint.epoch = getCurrentEpoch state) →
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root →
      ∀ (slot : Slot) (root : Root), checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        slot.toNat → getBlockRootAtSlot after slot = .ok root →
          block checkpoint.root ≤ block root := by
    intro checkpoint near rootOk slot root bound read
    unfold getBlockRoot at rootOk
    simp only [bind_ok_iff, liftArith, mapError_ok_iff] at rootOk
    obtain ⟨start, startOk, startRead⟩ := rootOk
    have startEq := (mulChecked_ok_iff.mp startOk).2
    have recent := slot_lt_epoch_add_historical positive window (state := state) near.symm
    have startAfter := forward startRead (by rw [startEq]; exact recent)
    exact le_of_rootLinks links startAfter (slot.toNat - start.toNat) (by omega) read
  -- A justified checkpoint of the state keeps its facts at the next slot, below a later epoch.
  have carried : ∀ (flag : Bool) (bound : Nat),
      (if flag then getCurrentEpoch state else getPreviousEpoch state).toNat ≤ bound →
      (recentJustified state flag).epoch.toNat ≤ bound ∧
        ((recentJustified state flag).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat <
            after.slot.toNat ∨
          ((recentJustified state flag).epoch = 0 ∧
            (recentJustified state flag).root = Vector.replicate 32 0)) ∧
        ∀ (slot : Slot) (root : Root),
          (recentJustified state flag).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat →
            getBlockRootAtSlot after slot = .ok root →
              block (recentJustified state flag).root ≤ block root := by
    intro flag bound le
    have epoch := UInt64.le_iff_toNat_le.mp (holds.epoch flag)
    have started := holds.started flag
    exact ⟨by omega, started.imp_left (by omega), kept _ started (holds.below flag)⟩
  have currentFacts : after.currentJustifiedCheckpoint.epoch.toNat ≤
        (getCurrentEpoch after).toNat ∧
      (after.currentJustifiedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat <
          after.slot.toNat ∨
        (after.currentJustifiedCheckpoint.epoch = 0 ∧
          after.currentJustifiedCheckpoint.root = Vector.replicate 32 0)) ∧
      ∀ (slot : Slot) (root : Root),
        after.currentJustifiedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
          slot.toNat → getBlockRootAtSlot after slot = .ok root →
            block after.currentJustifiedCheckpoint.root ≤ block root := by
    by_cases same : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
    · rw [same]
      exact carried true _ currentLe
    · obtain ⟨near, rootOk⟩ := advanceSlot_getBlockRoot_currentJustified_of_ne window computed same
      have nearLe : after.currentJustifiedCheckpoint.epoch.toNat ≤
          (getCurrentEpoch state).toNat := by
        rcases near with epoch | epoch <;> rw [epoch]
        exact UInt64.le_iff_toNat_le.mp (getPreviousEpoch_le state)
      have startBelow := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat nearLe
      exact ⟨by omega, .inl (by omega), fresh _ near rootOk⟩
  have previousFacts : after.previousJustifiedCheckpoint.epoch.toNat ≤
        (getPreviousEpoch after).toNat ∧
      (after.previousJustifiedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat <
          after.slot.toNat ∨
        (after.previousJustifiedCheckpoint.epoch = 0 ∧
          after.previousJustifiedCheckpoint.root = Vector.replicate 32 0)) ∧
      ∀ (slot : Slot) (root : Root),
        after.previousJustifiedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
          slot.toNat → getBlockRootAtSlot after slot = .ok root →
            block after.previousJustifiedCheckpoint.root ≤ block root := by
    rcases advanceSlot_previousJustified computed with same | ⟨same, epochs⟩
    · rw [same]
      exact carried false _ previousLe
    · rw [same]
      exact carried true _ epochs.ge
  refine ⟨fun flag => ?_, fun flag => ?_, fun flag => ?_⟩ <;> cases flag <;>
    simp only [recentJustified, Bool.false_eq_true, ↓reduceIte]
  · exact UInt64.le_iff_toNat_le.mpr previousFacts.1
  · exact UInt64.le_iff_toNat_le.mpr currentFacts.1
  · exact previousFacts.2.1
  · exact currentFacts.2.1
  · exact previousFacts.2.2
  · exact currentFacts.2.2

/-- One step of a chain keeps each justified checkpoint below the roots recorded from its epoch on.

The map from roots to blocks must keep in order the links of the state after the step.

An epoch must have at least one slot, and the buffer of roots must cover two epochs. -/
theorem RootsAbove.of_chainStep (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {forked after : ForkedBeaconState preset} (holds : RootsAbove block forked.state)
    (links : ∀ link ∈ rootLinks after.state, block link.1 ≤ block link.2)
    (step : ChainStep config checks forked after) :
    RootsAbove block after.state := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    -- The upgrades keep the slot, the roots and both justified checkpoints.
    have slot := processUpgrades_slot upgraded
    have roots := processUpgrades_blockRoots upgraded
    obtain ⟨previous, current⟩ := processUpgrades_justified upgraded
    rw [rootLinks_congr slot roots] at links
    exact (RootsAbove.of_advanceSlot positive window holds links advancedOk).congr slot roots
      previous current
  | block engine signed validateResult applied =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
    have frame := frame_processBlock blockOk
    exact holds.congr frame.slot (processBlock_blockRoots blockOk) frame.previousJustified
      frame.currentJustified

end EthLib.Consensus
