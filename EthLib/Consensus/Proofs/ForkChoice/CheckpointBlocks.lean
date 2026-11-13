module

public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.Transition.ChainRoots

/-!
# Proofs: the checkpoints of each block state name ancestors of that block

The chain of a known block holds, at each slot, the root of its latest ancestor up to that slot.

In a reachable store, the state of each known block agrees with that chain from the anchor slot on.

The anchor state agrees with every chain from its own slot on.

The state of a new block comes from the state of its parent, which the block extends.

So each checkpoint of a block state with an epoch after the anchor epoch names an ancestor.

That ancestor is the latest one at or before the first slot of the epoch, and the store knows it.

The same holds after justification and finalization, which the store runs to pull up each new tip.

So each checkpoint of the store is that of the anchor, or names a known block.

The one exception is an anchor state that hashes to the zero root.

Its first slot then leaves the latest header of the anchor state as it was.

Each store checkpoint besides the anchor one keeps its field from a block state or its pull-up.

The justified ones are current justified checkpoints there, and the finalized ones are finalized.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Fork}

/-- Justification and finalization keep the agreement of a state with a chain.

They keep the slot and the roots, and justify only a root that the state records. -/
theorem ChainRoots.of_processJustificationAndFinalization {anchor : Slot}
    {chain : Slot → Root → Prop} {state after : BeaconState preset fork}
    (holds : ChainRoots anchor chain state)
    (computed : processJustificationAndFinalization state = .ok after) :
    ChainRoots anchor chain after := by
  have slot := processJustificationAndFinalization_slot computed
  have roots := (processJustificationAndFinalization_keeps computed).2.1
  have reads := getBlockRootAtSlot_congr slot roots
  refine ⟨slot ▸ holds.above, fun index root above read =>
    holds.window index root above (by rw [← reads]; exact read), ?_⟩
  intro checkpoint mem late
  rw [slot]
  -- The previous justified and the finalized checkpoints come from the state before.
  have old : checkpoint ∈ [state.currentJustifiedCheckpoint, state.previousJustifiedCheckpoint,
      state.finalizedCheckpoint] ∨
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root := by
    rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
    · exact .inl mem
    obtain ⟨previous, -, finalized, -⟩ := weighJustificationAndFinalization_checkpoints weighed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
    rcases mem with rfl | rfl | rfl
    · rcases processJustificationAndFinalization_currentJustified computed with same | ⟨-, rooted⟩
      · exact .inl (.inl same)
      · exact .inr rooted
    · exact .inl (.inl previous)
    · rcases finalized with same | same | same
      · exact .inl (.inr (.inr same))
      · exact .inl (.inr (.inl same))
      · exact .inl (.inl same)
  rcases old with old | rooted
  · exact holds.checkpoints checkpoint old late
  · -- A new checkpoint names the root that the state records at its start.
    obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp rooted
    obtain ⟨fits, startEq⟩ := mulChecked_ok_iff.mp startOk
    have startIs : start = checkpoint.epoch * preset.SLOTS_PER_EPOCH :=
      UInt64.toNat_inj.mp (by rw [UInt64.toNat_mul, Nat.mod_eq_of_lt fits]; exact startEq)
    have before := UInt64.lt_iff_toNat_lt.mp (getBlockRootAtSlot_read read).1
    refine ⟨by omega, ?_⟩
    rw [← startIs]
    exact holds.window start _ (UInt64.le_iff_toNat_le.mpr (by omega)) read

namespace Store

/-- The chain of a block: at each slot, the root of its latest ancestor up to that slot. -/
def ancestorRoots (store : Store preset fork) (root : Root) (slot : Slot) (ancestor : Root) :
    Prop :=
  ∃ node, store.getAncestor ⟨root, .pending⟩ slot = .ok node ∧ node.root = ancestor

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- Below the slot of a block, its chain holds the chain of its parent. -/
theorem Store.ancestorRoots_of_parent {root : Root}
    {block parent : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) {slot : Slot} {ancestor : Root}
    (below : slot < block.slot) (held : store.ancestorRoots block.parentRoot slot ancestor) :
    store.ancestorRoots root slot ancestor := by
  obtain ⟨node, walk, rooted⟩ := held
  have same := Store.getAncestor_root (store := store) ⟨block.parentRoot, .pending⟩
    (parentPayloadStatus block parent) slot
  rw [walk] at same
  rw [Store.ancestorRoots, Store.getAncestor_step (node := ⟨root, .pending⟩) found
    (UInt64.not_le.mpr below) parentFound lower]
  revert same
  cases store.getAncestor ⟨block.parentRoot, parentPayloadStatus block parent⟩ slot with
  | error => simp [Functor.map, Except.map]
  | ok other =>
    intro same
    simp only [Functor.map, Except.map, Except.ok.injEq] at same
    exact ⟨other, rfl, same ▸ rooted⟩

/-- Take the slots from the slot of the parent of a block to the slot before the block.

At each of them, the chain of the block holds its parent root. -/
private theorem Store.ancestorRoots_parentRoot {root : Root}
    {block parent : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) {slot : Slot} (above : parent.slot ≤ slot)
    (below : slot < block.slot) : store.ancestorRoots root slot block.parentRoot :=
  Store.ancestorRoots_of_parent found parentFound lower below
    ⟨_, Store.getAncestor_of_le parentFound above, rfl⟩

/-- In a reachable store, take a block other than the anchor, whose state hashes to the zero root.

Its latest header then has the root of that block. -/
private theorem Store.Reachable.header_of_zero
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block) (stateFound : store.blockStates[root]? = some state)
    (notAnchor : block ≠ anchorBlock)
    (zero : hashTreeRoot state = .ok (Vector.replicate 32 0)) :
    hashTreeRoot state.latestBlockHeader = .ok root := by
  obtain ⟨kept, keptFound, -, fromParent⟩ := reachable.blockStatesFromParents found
  rw [stateFound, Option.some.injEq] at keptFound
  subst keptFound
  obtain ⟨parentState, checks, engine, signed, -, message, parentFound, transition⟩ :=
    fromParent notAnchor
  obtain ⟨advanced, -, -, -, blockOk, rootOk⟩ := stateTransition_ok transition
  have stateRoot := Except.ok.inj ((rootOk rfl).symm.trans zero)
  obtain ⟨bodyRoot, bodyRooted, header⟩ := latestBlockHeader_processBlock blockOk
  have rooted := BeaconBlock.hashTreeRoot_header bodyRooted
  rw [header, ← stateRoot, rooted, message]
  exact reachable.root found

/-- In a reachable store, the state of each known block agrees with the chain of that block.

The agreement starts at the slot of the anchor state.

The other case is an anchor state that hashes to the zero root.

The anchor state needs the invariant of valid blocks, and the anchor block must not be after it.

The buffer of roots must cover two epochs. -/
theorem Store.Reachable.chainRoots (anchor : Invariant anchorState)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {state : BeaconState preset fork} (found : store.blockStates[root]? = some state) :
    ChainRoots anchorState.slot (store.ancestorRoots root) state ∨
      hashTreeRoot anchorState = .ok (Vector.replicate 32 0) := by
  by_cases zeroAnchor : hashTreeRoot anchorState = .ok (Vector.replicate 32 0)
  · exact .inr zeroAnchor
  refine .inl ?_
  -- Strong induction on the slot of the block.
  suffices main : ∀ (n : Nat) (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), block.slot.toNat = n →
      store.blocks[root]? = some block → store.blockStates[root]? = some state →
      ChainRoots anchorState.slot (store.ancestorRoots root) state by
    obtain ⟨block, known⟩ := reachable.known_of_blockState found
    exact main _ root block state rfl known found
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro root block state slotIs known stateFound
  obtain ⟨kept, keptFound, isAnchor, notAnchor⟩ := reachable.blockStatesFromParents known
  rw [stateFound, Option.some.injEq] at keptFound
  subst keptFound
  by_cases same : block = anchorBlock
  · rw [isAnchor same]
    exact ChainRoots.of_invariant anchor _
  obtain ⟨parentState, checks, engine, signed, -, message, parentStateFound, transition⟩ :=
    notAnchor same
  obtain ⟨parent, parentKnown⟩ := reachable.known_of_blockState parentStateFound
  have parentLe :=
    Store.Reachable.slot_le_of_blockState anchorSlot reachable parentKnown parentStateFound
  obtain ⟨earlier, atSlot⟩ := stateTransition_slot transition
  rw [message] at earlier atSlot
  have lower : parent.slot < block.slot := UInt64.lt_of_le_of_lt parentLe earlier
  have parentHolds := ih parent.slot.toNat (slotIs ▸ UInt64.lt_iff_toNat_lt.mp lower) _ parent
    parentState rfl parentKnown parentStateFound
  refine (ChainRoots.of_stateTransition window parentHolds transition).mono ?_
  rintro slot ancestor - below (held | ⟨later, rooted | ⟨zero, rooted⟩⟩)
  · rw [atSlot] at below
    exact Store.ancestorRoots_of_parent known parentKnown lower below held
  · rw [atSlot] at below
    rw [rooted, message]
    exact Store.ancestorRoots_parentRoot known parentKnown lower
      (UInt64.le_trans parentLe later) below
  · -- A parent state that hashes to zero is not the anchor state, so its header names the parent.
    rw [atSlot] at below
    have parentNotAnchor : parent ≠ anchorBlock := by
      intro isAnchorParent
      obtain ⟨kept, keptFound, isAnchor', -⟩ := reachable.blockStatesFromParents parentKnown
      rw [parentStateFound, Option.some.injEq] at keptFound
      subst keptFound
      rw [isAnchor' isAnchorParent] at zero
      exact zeroAnchor zero
    have header :=
      Store.Reachable.header_of_zero reachable parentKnown parentStateFound parentNotAnchor zero
    rw [header] at rooted
    cases rooted
    exact Store.ancestorRoots_parentRoot known parentKnown lower
      (UInt64.le_trans parentLe later) below

/-- A state that agrees with the chain of a block from the anchor slot on names its ancestors.

Each of its checkpoints after the anchor epoch has the checkpoint block of that block as root.

The store knows it.

An epoch must have at least one slot. -/
private theorem Store.getCheckpointBlock_of_chainRoots
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {root : Root} {state : BeaconState preset fork}
    (holds : ChainRoots anchorState.slot (store.ancestorRoots root) state) {checkpoint : Checkpoint}
    (member : checkpoint ∈ [state.currentJustifiedCheckpoint, state.previousJustifiedCheckpoint,
      state.finalizedCheckpoint])
    (later : getCurrentEpoch anchorState < checkpoint.epoch) :
    store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∧
      store.blocks.contains checkpoint.root := by
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  rw [getCurrentEpoch_toNat] at laterNat
  have above : anchorState.slot.toNat <
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    Nat.lt_mul_of_div_lt laterNat positive
  obtain ⟨before, node, walk, rooted⟩ := holds.checkpoints checkpoint member above
  have fits : checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    have := state.slot.toNat_lt
    omega
  have start : computeStartSlotAtEpoch preset checkpoint.epoch =
      .ok (checkpoint.epoch * preset.SLOTS_PER_EPOCH) :=
    computeStartSlotAtEpoch_ok_iff.mpr ⟨fits, by rw [UInt64.toNat_mul, Nat.mod_eq_of_lt fits]⟩
  refine ⟨?_, ?_⟩
  · simp only [Store.getCheckpointBlock, start, walk, rooted, Except.mapError, bind,
      Except.bind, pure, Except.pure]
  · obtain ⟨block, found, -⟩ := Store.getAncestor_le walk
    rw [← rooted, Std.TreeMap.contains_eq_isSome_getElem?, found]
    rfl

/-- In a reachable store, a checkpoint of a block state after the anchor epoch names an ancestor.

The ancestor is the checkpoint block of the block at the epoch of the checkpoint.

The store knows it.

The checkpoint is one of the three of the state, or of that state after justification.

The other case is an anchor state that hashes to the zero root.

The anchor state needs the invariant of valid blocks, and the anchor block must not be after it.

An epoch must have at least one slot, and the buffer of roots must cover two epochs. -/
theorem Store.Reachable.getCheckpointBlock_of_blockState (anchor : Invariant anchorState)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {state : BeaconState preset fork} (found : store.blockStates[root]? = some state)
    {checkpoint : Checkpoint}
    (member : checkpoint ∈ [state.currentJustifiedCheckpoint, state.previousJustifiedCheckpoint,
        state.finalizedCheckpoint] ∨
      ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
        checkpoint ∈ [pulled.currentJustifiedCheckpoint, pulled.previousJustifiedCheckpoint,
          pulled.finalizedCheckpoint])
    (later : getCurrentEpoch anchorState < checkpoint.epoch) :
    (store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∧
        store.blocks.contains checkpoint.root) ∨
      hashTreeRoot anchorState = .ok (Vector.replicate 32 0) := by
  rcases reachable.chainRoots anchor anchorSlot window found with holds | zero
  · rcases member with member | ⟨pulled, pulledOk, member⟩
    · exact .inl (Store.getCheckpointBlock_of_chainRoots positive holds member later)
    · exact .inl (Store.getCheckpointBlock_of_chainRoots positive
        (holds.of_processJustificationAndFinalization pulledOk) member later)
  · exact .inr zero

/-! ## The checkpoints of a store come from its block states -/

namespace Store

/-- A checkpoint that a field reads in a block state, or in that state after justification. -/
private def FromState (store : Store preset fork) (field : BeaconState preset fork → Checkpoint)
    (checkpoint : Checkpoint) : Prop :=
  ∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
    (checkpoint = field state ∨
      ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = field pulled)

/-- The anchor checkpoint, or a later checkpoint that a field reads in a block state. -/
private def Traced (store : Store preset fork) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) (field : BeaconState preset fork → Checkpoint)
    (checkpoint : Checkpoint) : Prop :=
  (checkpoint.epoch = getCurrentEpoch anchorState ∧
      hashTreeRoot anchorBlock = .ok checkpoint.root) ∨
    (getCurrentEpoch anchorState < checkpoint.epoch ∧ store.FromState field checkpoint)

/-- A store whose four checkpoints are each the anchor checkpoint or come from a block state.

The two justified checkpoints come from the current justified checkpoint of a state.

The two finalized checkpoints come from the finalized checkpoint of a state.

Each unrealized justification has the anchor epoch.

Otherwise it is the current justified checkpoint of its block state after justification. -/
private structure Tracked (store : Store preset fork) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) : Prop where
  justified : store.Traced anchorState anchorBlock (·.currentJustifiedCheckpoint)
    store.justifiedCheckpoint
  finalized : store.Traced anchorState anchorBlock (·.finalizedCheckpoint)
    store.finalizedCheckpoint
  unrealizedJustified : store.Traced anchorState anchorBlock (·.currentJustifiedCheckpoint)
    store.unrealizedJustifiedCheckpoint
  unrealizedFinalized : store.Traced anchorState anchorBlock (·.finalizedCheckpoint)
    store.unrealizedFinalizedCheckpoint
  justifications : ∀ (root : Root) (checkpoint : Checkpoint),
    store.unrealizedJustifications[root]? = some checkpoint →
      checkpoint.epoch = getCurrentEpoch anchorState ∨
        ∃ state pulled, store.blockStates[root]? = some state ∧
          processJustificationAndFinalization state = .ok pulled ∧
          checkpoint = pulled.currentJustifiedCheckpoint

variable {after : Store preset fork}

/-- A checkpoint of a block state stays one when the store keeps every block state. -/
private theorem FromState.mono {field : BeaconState preset fork → Checkpoint}
    {checkpoint : Checkpoint}
    (grow : ∀ {root : Root} {state : BeaconState preset fork},
      store.blockStates[root]? = some state → after.blockStates[root]? = some state)
    (source : store.FromState field checkpoint) : after.FromState field checkpoint := by
  obtain ⟨root, state, found, member⟩ := source
  exact ⟨root, state, grow found, member⟩

/-- A traced checkpoint stays traced when the store keeps every block state. -/
private theorem Traced.mono {field : BeaconState preset fork → Checkpoint}
    {checkpoint : Checkpoint}
    (grow : ∀ {root : Root} {state : BeaconState preset fork},
      store.blockStates[root]? = some state → after.blockStates[root]? = some state)
    (traced : store.Traced anchorState anchorBlock field checkpoint) :
    after.Traced anchorState anchorBlock field checkpoint := by
  rcases traced with anchored | ⟨later, root, state, found, member⟩
  · exact .inl anchored
  · exact .inr ⟨later, root, state, grow found, member⟩

/-- A traced checkpoint is at or after the anchor epoch. -/
private theorem Traced.epoch_le {field : BeaconState preset fork → Checkpoint}
    {checkpoint : Checkpoint} (traced : store.Traced anchorState anchorBlock field checkpoint) :
    getCurrentEpoch anchorState ≤ checkpoint.epoch := by
  rcases traced with ⟨same, -⟩ | ⟨later, -⟩
  · rw [same]
    exact UInt64.le_refl _
  · exact UInt64.le_of_lt later

/-- A checkpoint that replaces a traced one at a later epoch is traced.

It must be a checkpoint that is traced or comes from a block state. -/
private theorem Traced.adopt {field : BeaconState preset fork → Checkpoint} {old new : Checkpoint}
    (traced : store.Traced anchorState anchorBlock field old)
    (candidate : store.Traced anchorState anchorBlock field new ∨ store.FromState field new)
    (later : old.epoch < new.epoch) : store.Traced anchorState anchorBlock field new := by
  rcases candidate with traced' | source
  · exact traced'
  · exact .inr ⟨UInt64.lt_of_le_of_lt traced.epoch_le later, source⟩

/-- A store with the same checkpoints and justifications, and more block states, is tracked. -/
private theorem Tracked.of_grow (tracked : store.Tracked anchorState anchorBlock)
    (justified : after.justifiedCheckpoint = store.justifiedCheckpoint)
    (finalized : after.finalizedCheckpoint = store.finalizedCheckpoint)
    (unrealizedJustified :
      after.unrealizedJustifiedCheckpoint = store.unrealizedJustifiedCheckpoint)
    (unrealizedFinalized :
      after.unrealizedFinalizedCheckpoint = store.unrealizedFinalizedCheckpoint)
    (justifications : after.unrealizedJustifications = store.unrealizedJustifications)
    (grow : ∀ {root : Root} {state : BeaconState preset fork},
      store.blockStates[root]? = some state → after.blockStates[root]? = some state) :
    after.Tracked anchorState anchorBlock := by
  refine ⟨justified ▸ tracked.justified.mono grow, finalized ▸ tracked.finalized.mono grow,
    unrealizedJustified ▸ tracked.unrealizedJustified.mono grow,
    unrealizedFinalized ▸ tracked.unrealizedFinalized.mono grow, ?_⟩
  intro root checkpoint found
  rw [justifications] at found
  rcases tracked.justifications root checkpoint found with same | ⟨state, pulled, kept, rest⟩
  · exact .inl same
  · exact .inr ⟨state, pulled, grow kept, rest⟩

/-- Replacing the checkpoints at later epochs keeps the store tracked.

Each new one must be a checkpoint that is traced or comes from a block state. -/
private theorem Tracked.updateCheckpoints {justified finalized : Checkpoint}
    (tracked : store.Tracked anchorState anchorBlock)
    (justifiedSource :
      store.Traced anchorState anchorBlock (·.currentJustifiedCheckpoint) justified ∨
        store.FromState (·.currentJustifiedCheckpoint) justified)
    (finalizedSource : store.Traced anchorState anchorBlock (·.finalizedCheckpoint) finalized ∨
      store.FromState (·.finalizedCheckpoint) finalized) :
    (store.updateCheckpoints justified finalized).Tracked anchorState anchorBlock := by
  unfold Store.updateCheckpoints
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte]
  · exact ⟨tracked.justified.adopt justifiedSource j, tracked.finalized.adopt finalizedSource f,
      tracked.unrealizedJustified, tracked.unrealizedFinalized, tracked.justifications⟩
  · exact ⟨tracked.justified.adopt justifiedSource j, tracked.finalized,
      tracked.unrealizedJustified, tracked.unrealizedFinalized, tracked.justifications⟩
  · exact ⟨tracked.justified, tracked.finalized.adopt finalizedSource f,
      tracked.unrealizedJustified, tracked.unrealizedFinalized, tracked.justifications⟩
  · exact tracked

/-- Replacing the unrealized checkpoints at later epochs keeps the store tracked.

Each new one must be a checkpoint that is traced or comes from a block state. -/
private theorem Tracked.updateUnrealizedCheckpoints {justified finalized : Checkpoint}
    (tracked : store.Tracked anchorState anchorBlock)
    (justifiedSource :
      store.Traced anchorState anchorBlock (·.currentJustifiedCheckpoint) justified ∨
        store.FromState (·.currentJustifiedCheckpoint) justified)
    (finalizedSource : store.Traced anchorState anchorBlock (·.finalizedCheckpoint) finalized ∨
      store.FromState (·.finalizedCheckpoint) finalized) :
    (store.updateUnrealizedCheckpoints justified finalized).Tracked anchorState anchorBlock := by
  unfold Store.updateUnrealizedCheckpoints
  by_cases j : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte]
  · exact ⟨tracked.justified, tracked.finalized,
      tracked.unrealizedJustified.adopt justifiedSource j,
      tracked.unrealizedFinalized.adopt finalizedSource f, tracked.justifications⟩
  · exact ⟨tracked.justified, tracked.finalized,
      tracked.unrealizedJustified.adopt justifiedSource j, tracked.unrealizedFinalized,
      tracked.justifications⟩
  · exact ⟨tracked.justified, tracked.finalized, tracked.unrealizedJustified,
      tracked.unrealizedFinalized.adopt finalizedSource f, tracked.justifications⟩
  · exact tracked

/-- Adopting the unrealized checkpoints keeps the store tracked. -/
private theorem Tracked.updateCheckpoints_unrealized
    (tracked : store.Tracked anchorState anchorBlock) :
    (store.updateCheckpoints store.unrealizedJustifiedCheckpoint
      store.unrealizedFinalizedCheckpoint).Tracked anchorState anchorBlock :=
  tracked.updateCheckpoints (.inl tracked.unrealizedJustified) (.inl tracked.unrealizedFinalized)

/-- A store with the same checkpoints, justifications and block states is tracked. -/
private theorem Tracked.of_eq (tracked : store.Tracked anchorState anchorBlock)
    (justified : after.justifiedCheckpoint = store.justifiedCheckpoint)
    (finalized : after.finalizedCheckpoint = store.finalizedCheckpoint)
    (unrealizedJustified :
      after.unrealizedJustifiedCheckpoint = store.unrealizedJustifiedCheckpoint)
    (unrealizedFinalized :
      after.unrealizedFinalizedCheckpoint = store.unrealizedFinalizedCheckpoint)
    (justifications : after.unrealizedJustifications = store.unrealizedJustifications)
    (states : after.blockStates = store.blockStates) :
    after.Tracked anchorState anchorBlock :=
  tracked.of_grow justified finalized unrealizedJustified unrealizedFinalized justifications
    (fun found => states ▸ found)

/-- Recording the unrealized justification of a block keeps the store tracked.

It must be the current justified checkpoint of the block state after justification. -/
private theorem Tracked.insertJustification (tracked : store.Tracked anchorState anchorBlock)
    {root : Root} {state counted : BeaconState preset fork}
    (found : store.blockStates[root]? = some state)
    (counting : processJustificationAndFinalization state = .ok counted) :
    ({ store with unrealizedJustifications :=
        store.unrealizedJustifications.insert root counted.currentJustifiedCheckpoint } :
      Store preset fork).Tracked anchorState anchorBlock := by
  refine ⟨tracked.justified, tracked.finalized, tracked.unrealizedJustified,
    tracked.unrealizedFinalized, ?_⟩
  intro key checkpoint keyFound
  dsimp only at keyFound
  rw [getElem?_insert_root] at keyFound
  by_cases same : root = key
  · simp only [same, ↓reduceIte, Option.some.injEq] at keyFound
    subst same
    exact .inr ⟨state, counted, found, counting, keyFound.symm⟩
  · simp only [same, ↓reduceIte] at keyFound
    exact tracked.justifications key checkpoint keyFound

/-- The tip pulled up to the end of its epoch keeps the store tracked. -/
private theorem Tracked.computePulledUpTip {config : Config} {root : Root}
    (tracked : store.Tracked anchorState anchorBlock)
    (pulled : store.computePulledUpTip config root = .ok after) :
    after.Tracked anchorState anchorBlock := by
  obtain ⟨-, -, states, -, state, counted, found, counting, moved, which, ⟨justified, finalized,
    unrealizedJustified, unrealizedFinalized⟩, justifications⟩ := computePulledUpTip_frame pulled
  -- The new checkpoints come from the state of the block after justification.
  have source (field : BeaconState preset fork → Checkpoint) {kept : Store preset fork}
      (same : kept.blockStates = store.blockStates) : kept.FromState field (field counted) :=
    ⟨root, state, by rw [same]; exact found, .inr ⟨counted, counting, rfl⟩⟩
  have unrealized :=
    tracked.updateUnrealizedCheckpoints (.inr (source _ rfl)) (.inr (source _ rfl))
  have movedStates : moved.blockStates = store.blockStates := by
    rcases which with rfl | rfl <;> simp
  have movedTracked : moved.Tracked anchorState anchorBlock := by
    rcases which with rfl | rfl
    · exact unrealized
    · exact unrealized.updateCheckpoints (.inr (source _ (by simp))) (.inr (source _ (by simp)))
  have movedJustifications : moved.unrealizedJustifications = store.unrealizedJustifications := by
    rcases which with rfl | rfl <;>
      simp [updateCheckpoints_unrealizedJustifications,
        updateUnrealizedCheckpoints_unrealizedJustifications]
  -- The pull-up records the current justified checkpoint of that state for the block.
  exact (movedTracked.insertJustification (by rw [movedStates]; exact found) counting).of_eq
    justified finalized unrealizedJustified unrealizedFinalized
    (by rw [justifications, movedJustifications]) (states.trans movedStates.symm)

/-- A tick within a slot keeps the store tracked. -/
private theorem Tracked.onTickPerSlot {config : Config} {timeMs : UInt64}
    (tracked : store.Tracked anchorState anchorBlock)
    (ticked : store.onTickPerSlot config timeMs = .ok after) :
    after.Tracked anchorState anchorBlock := by
  obtain ⟨-, -, -, -, states, moved, which, ⟨justified, finalized, unrealizedJustified,
    unrealizedFinalized⟩, justifications⟩ := onTickPerSlot_frame ticked
  rcases which with rfl | rfl
  · exact tracked.of_eq justified finalized unrealizedJustified unrealizedFinalized
      justifications states
  · exact tracked.updateCheckpoints_unrealized.of_eq justified finalized unrealizedJustified
      unrealizedFinalized (by rw [justifications, updateCheckpoints_unrealizedJustifications])
      (by rw [states, updateCheckpoints_blockStates])

/-- The catch-up loop keeps the store tracked. -/
private theorem Tracked.catchUp {config : Config} {tickSlot : Slot} {start : Store preset fork}
    (tracked : start.Tracked anchorState anchorBlock)
    (caught : Store.catchUp config start tickSlot = .ok after) :
    after.Tracked anchorState anchorBlock :=
  catchUp_preserves (P := fun s => s.Tracked anchorState anchorBlock)
    (fun tracked tick => tracked.onTickPerSlot tick) tracked caught

/-- A tick keeps the store tracked. -/
private theorem Tracked.onTick {config : Config} {timeMs : UInt64}
    (tracked : store.Tracked anchorState anchorBlock)
    (ticked : store.onTick config timeMs = .ok after) : after.Tracked anchorState anchorBlock := by
  obtain ⟨_, caught, -, caughtUp, ticked⟩ := onTick_ok ticked
  exact (tracked.catchUp caughtUp).onTickPerSlot ticked

end Store

/-- A new store holds one unrealized justification: the anchor checkpoint, for the anchor block. -/
private theorem getForkchoiceStore_unrealizedJustifications {config : Config}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    ∃ anchorRoot, hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.unrealizedJustifications = (∅ : Std.TreeMap Root Checkpoint).insert anchorRoot
        ⟨getCurrentEpoch anchorState, anchorRoot⟩ := by
  unfold getForkchoiceStore at made
  cases stateRoot : hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at made
    split at made
    · simp [throw, throwThe, MonadExceptOf.throw] at made
    · cases blockRoot : hashTreeRoot anchorBlock with
      | error e => simp [blockRoot] at made
      | ok anchorRoot =>
        simp only [blockRoot] at made
        cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
            anchorState.slot with
        | error e => simp [time] at made
        | ok timeMs =>
          simp only [time, pure, Except.pure, Except.ok.injEq] at made
          subst made
          exact ⟨anchorRoot, rfl, rfl⟩

namespace Store

variable {after : Store preset fork}

/-- An attestation keeps the store tracked. -/
private theorem Tracked.onAttestation {config : Config} {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool}
    (tracked : store.Tracked anchorState anchorBlock)
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.Tracked anchorState anchorBlock := by
  obtain ⟨-, -, states, ⟨justified, finalized, unrealizedJustified, unrealizedFinalized⟩,
    justifications⟩ := onAttestation_frame attested
  exact tracked.of_eq justified finalized unrealizedJustified unrealizedFinalized justifications
    states

/-- An attester slashing keeps the store tracked. -/
private theorem Tracked.onAttesterSlashing {config : Config} {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} (tracked : store.Tracked anchorState anchorBlock)
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    after.Tracked anchorState anchorBlock := by
  obtain ⟨-, -, states, ⟨justified, finalized, unrealizedJustified, unrealizedFinalized⟩,
    justifications⟩ := onAttesterSlashing_frame slashed
  exact tracked.of_eq justified finalized unrealizedJustified unrealizedFinalized justifications
    states

/-- A new block keeps the store tracked. -/
private theorem Tracked.onBlock {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (tracked : store.Tracked anchorState anchorBlock)
    (added : store.onBlock config checks sources signed = .ok after) :
    after.Tracked anchorState anchorBlock := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      exact tracked
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
    have unknown : store.blocks[blockRoot]? = none := by
      rw [Std.TreeMap.contains_eq_isSome_getElem?] at known
      simpa using known
    have fresh := reachable.blockState_eq_none unknown
    -- The new block adds a state at a fresh root, so every old state stays.
    have inserted : ({ store with
        blocks := store.blocks.insert blockRoot signed.message
        blockStates := store.blockStates.insert blockRoot state } : Store preset fork).Tracked
        anchorState anchorBlock := by
      refine tracked.of_grow rfl rfl rfl rfl rfl ?_
      intro key kept keptFound
      dsimp only
      rw [getElem?_insert_root]
      by_cases same : blockRoot = key
      · subst same
        rw [fresh] at keptFound
        cases keptFound
      · simp only [same, ↓reduceIte]
        exact keptFound
    obtain ⟨-, -, recordedStates, -, ⟨justified, finalized, unrealizedJustified,
      unrealizedFinalized⟩, justifications⟩ := recordBlockTimeliness_frame record
    have recordedTracked : recorded.Tracked anchorState anchorBlock :=
      inserted.of_eq justified finalized unrealizedJustified unrealizedFinalized justifications
        recordedStates
    obtain ⟨-, -, boostedStates, -, ⟨justified, finalized, unrealizedJustified,
      unrealizedFinalized⟩, justifications⟩ := updateProposerBoostRoot_frame boost
    have boostedTracked : boosted.Tracked anchorState anchorBlock :=
      recordedTracked.of_eq justified finalized unrealizedJustified unrealizedFinalized
        justifications boostedStates
    have stateFound : boosted.blockStates[blockRoot]? = some state := by
      rw [boostedStates, recordedStates]
      exact (getElem?_insert_root).trans (by simp)
    have source (field : BeaconState preset fork → Checkpoint) :
        boosted.FromState field (field state) :=
      ⟨blockRoot, state, stateFound, .inl rfl⟩
    exact (boostedTracked.updateCheckpoints (.inr (source (·.currentJustifiedCheckpoint)))
      (.inr (source (·.finalizedCheckpoint)))).computePulledUpTip added

end Store

/-- A reachable store is tracked: each checkpoint is the anchor one, or from a block state. -/
private theorem Store.Reachable.tracked
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.Tracked anchorState anchorBlock := by
  induction reachable with
  | @anchor st made =>
    obtain ⟨anchorRoot, hashed, -, -, justified, finalized, unrealizedJustified,
      unrealizedFinalized⟩ := getForkchoiceStore_anchor made
    obtain ⟨anchorRoot', hashed', justifications⟩ :=
      getForkchoiceStore_unrealizedJustifications made
    have anchored : ∀ (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint),
        checkpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ →
        st.Traced anchorState anchorBlock field checkpoint := by
      rintro field checkpoint rfl
      exact .inl ⟨rfl, hashed⟩
    refine ⟨anchored _ _ justified, anchored _ _ finalized, anchored _ _ unrealizedJustified,
      anchored _ _ unrealizedFinalized, ?_⟩
    intro root checkpoint found
    rw [justifications, getElem?_insert_root] at found
    by_cases same : anchorRoot' = root
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      exact .inl (by rw [← found])
    · simp [same] at found
  | tick _ ticked ih => exact ih.onTick ticked
  | block previous added ih => exact ih.onBlock previous added
  | attestation _ attested ih => exact ih.onAttestation attested
  | attesterSlashing _ slashed ih => exact ih.onAttesterSlashing slashed
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih.of_eq rfl rfl rfl rfl rfl rfl
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih.of_eq rfl rfl rfl rfl rfl rfl
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok _ accepted
    exact ih.of_eq rfl rfl rfl rfl rfl rfl

/-- In a reachable store, the unrealized justification of a block names an ancestor of it.

Its epoch must be after the anchor epoch.

The ancestor is the checkpoint block of the block at the epoch of the checkpoint, and is known.

The other case is an anchor state that hashes to the zero root.

The anchor state needs the invariant of valid blocks, and the anchor block must not be after it.

An epoch must have at least one slot, and the buffer of roots must cover two epochs. -/
theorem Store.Reachable.getCheckpointBlock_of_unrealizedJustification
    (anchor : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {checkpoint : Checkpoint} (found : store.unrealizedJustifications[root]? = some checkpoint)
    (later : getCurrentEpoch anchorState < checkpoint.epoch) :
    (store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∧
        store.blocks.contains checkpoint.root) ∨
      hashTreeRoot anchorState = .ok (Vector.replicate 32 0) := by
  rcases reachable.tracked.justifications root checkpoint found with same |
    ⟨state, pulled, stateFound, pulledOk, rfl⟩
  · rw [same] at later
    exact absurd later (UInt64.lt_irrefl _)
  · exact reachable.getCheckpointBlock_of_blockState anchor anchorSlot positive window stateFound
      (.inr ⟨pulled, pulledOk, by simp⟩) later

/-- Each of the four checkpoints of a reachable store is the anchor checkpoint, or names a block.

The anchor checkpoint has the epoch of the anchor state and the root of the anchor block.

The store knows that block.

Any other checkpoint has a later epoch, and the store knows its root.

The other case is an anchor state that hashes to the zero root.

The anchor state needs the invariant of valid blocks, and the anchor block must not be after it.

An epoch must have at least one slot, and the buffer of roots must cover two epochs. -/
theorem Store.Reachable.checkpoints_known (anchor : Invariant anchorState)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (reachable : Store.Reachable config anchorState anchorBlock store) {checkpoint : Checkpoint}
    (member : checkpoint ∈ [store.justifiedCheckpoint, store.finalizedCheckpoint,
      store.unrealizedJustifiedCheckpoint, store.unrealizedFinalizedCheckpoint]) :
    (checkpoint.epoch = getCurrentEpoch anchorState ∧
        hashTreeRoot anchorBlock = .ok checkpoint.root ∧ store.blocks.contains checkpoint.root) ∨
      (getCurrentEpoch anchorState < checkpoint.epoch ∧ store.blocks.contains checkpoint.root) ∨
      hashTreeRoot anchorState = .ok (Vector.replicate 32 0) := by
  have tracked := reachable.tracked
  -- Each checkpoint of the store is traced through a field that is one of the three of a state.
  have traced : ∃ field : BeaconState preset fork → Checkpoint,
      (∀ state : BeaconState preset fork, field state ∈ [state.currentJustifiedCheckpoint,
        state.previousJustifiedCheckpoint, state.finalizedCheckpoint]) ∧
      store.Traced anchorState anchorBlock field checkpoint := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, tracked.justified⟩
    · exact ⟨_, by simp, tracked.finalized⟩
    · exact ⟨_, by simp, tracked.unrealizedJustified⟩
    · exact ⟨_, by simp, tracked.unrealizedFinalized⟩
  obtain ⟨field, listed, traced⟩ := traced
  rcases traced with ⟨epoch, hashed⟩ | ⟨later, root, state, stateFound, source⟩
  · -- The store knows the anchor block at its own root.
    obtain ⟨anchorRoot, anchorHashed, anchorFound⟩ := reachable.anchor_known
    rw [hashed, Except.ok.injEq] at anchorHashed
    rw [← anchorHashed] at anchorFound
    refine .inl ⟨epoch, hashed, ?_⟩
    rw [Std.TreeMap.contains_eq_isSome_getElem?, anchorFound]
    rfl
  have member : checkpoint ∈ [state.currentJustifiedCheckpoint,
        state.previousJustifiedCheckpoint, state.finalizedCheckpoint] ∨
      ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
        checkpoint ∈ [pulled.currentJustifiedCheckpoint, pulled.previousJustifiedCheckpoint,
          pulled.finalizedCheckpoint] := by
    rcases source with rfl | ⟨pulled, pulledOk, rfl⟩
    · exact .inl (listed state)
    · exact .inr ⟨pulled, pulledOk, listed pulled⟩
  rcases reachable.getCheckpointBlock_of_blockState anchor anchorSlot positive window stateFound
      member later with ⟨-, known⟩ | zero
  · exact .inr (.inl ⟨later, known⟩)
  · exact .inr (.inr zero)

/-! ## The field that gives each checkpoint of a store -/

/-- A traced checkpoint is the anchor checkpoint, or the field of a block state or of its pull-up.

The anchor checkpoint has the epoch of the anchor state and the root of the anchor block. -/
private theorem Store.Traced.origin {field : BeaconState preset fork → Checkpoint}
    {checkpoint : Checkpoint} (traced : store.Traced anchorState anchorBlock field checkpoint) :
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = field state) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = field pulled := by
  rcases traced with ⟨epoch, hashed⟩ | ⟨-, root, state, found, same | ⟨pulled, pulledOk, same⟩⟩
  · exact .inl ⟨checkpoint.root, hashed, by rw [← epoch]⟩
  · exact .inr (.inl ⟨root, state, found, same⟩)
  · exact .inr (.inr ⟨root, state, pulled, found, pulledOk, same⟩)

/-- The justified checkpoints of a reachable store, realized or not, each come from one place.

The first is the anchor: the epoch of the anchor state and the root of the anchor block.

The second is the current justified checkpoint of a held state.

The third is that checkpoint after justification and finalization on a held state.

The origin gives the whole checkpoint, its epoch and root, and bounds no epoch. -/
theorem Store.Reachable.justified_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∀ checkpoint, (checkpoint = store.justifiedCheckpoint ∨
      checkpoint = store.unrealizedJustifiedCheckpoint) →
      (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
        checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = state.currentJustifiedCheckpoint) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = pulled.currentJustifiedCheckpoint := by
  rintro checkpoint (rfl | rfl)
  exacts [reachable.tracked.justified.origin, reachable.tracked.unrealizedJustified.origin]

/-- The finalized checkpoints of a reachable store, realized or not, each come from one place.

The first is the anchor: the epoch of the anchor state and the root of the anchor block.

The second is the finalized checkpoint of a held state.

The third is that checkpoint after justification and finalization on a held state.

The origin gives the whole checkpoint, its epoch and root, and bounds no epoch. -/
theorem Store.Reachable.finalized_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∀ checkpoint, (checkpoint = store.finalizedCheckpoint ∨
      checkpoint = store.unrealizedFinalizedCheckpoint) →
      (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
        checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = state.finalizedCheckpoint) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = pulled.finalizedCheckpoint := by
  rintro checkpoint (rfl | rfl)
  exacts [reachable.tracked.finalized.origin, reachable.tracked.unrealizedFinalized.origin]

end EthLib.Consensus
