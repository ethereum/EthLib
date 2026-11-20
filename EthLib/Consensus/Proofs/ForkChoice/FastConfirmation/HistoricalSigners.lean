module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedVotes
public import EthLib.Consensus.Proofs.DirectSafety.Provenance

/-!
# Honest signers of later justified checkpoints

A store's justified checkpoint after the anchor was set by one count of votes.

The count passed only if two thirds of the active stake voted for it.

When Byzantine stake is below two thirds there, an honest validator was among the voters.

Its vote was in a block that the store holds, and the store reads it with a valid signature.

So the vote is a statement of a sent message, which the network model ties to its signer.

The count reads the active stake above the floor of one increment, from the stake floors.

The anchor's latest header must be the anchor block's, with a zero state root.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A state where a store counts votes has active stake above one and a half increments.

The count is after the first two epochs.

A pull-up counts in a held state, where the terminal floor bounds the stake of the keys.

An epoch step on the way to a held child counts in an epoch call of the run to that child.

There the run floor bounds it.

Distinct keys make the stake of the keys that of the indices. -/
private theorem counted_stake_large {anchor : Store preset fork} {g : ForkedBeaconState preset}
    {horizon : Epoch} {last : Nat}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (absent : AnchorParentAbsent (e := e) last) (heldEarly : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bound : (e.world k).time ≤ last)
    {root : Root} {base counted : BeaconState preset fork}
    (held : ((e.world k).state w).blockStates[root]? = some base)
    (shape : counted = base ∨
      ∃ (state : BeaconState preset fork) (childRoot : Root) (child : BeaconBlock preset fork),
        ((e.world k).state w).blocks[childRoot]? = some child ∧ child.parentRoot = root ∧
        state.slot < child.slot ∧
        (state = base ∨ ∃ slot, processSlots config checks base slot = .ok state) ∧
        (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
        processSlot state = .ok counted)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch counted)
    (upper : (getCurrentEpoch counted).toNat ≤ horizon.toNat + 1) :
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt counted index.toNat)
        (getActiveValidatorIndices counted (getCurrentEpoch counted)).toFinset := by
  have reached := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) k w honest
  have early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      ((e.world k).state w).blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    fun next scheduled root state found =>
      heldEarly w honest k bound next scheduled root state found
  rcases shape with rfl | ⟨state, childRoot, child, childFound, parent, before, path, boundary,
    countedOk⟩
  · -- A pull-up: the terminal floor, with distinct keys.
    have floor := terminal w honest k bound root counted held upper later
    rw [stake_activeKeys_eq (reached.pubkeysDistinct_of_blockState (UInt64.le_of_eq anchorSlot)
      (absent w honest k bound) early pre genesis held)] at floor
    exact floor
  · -- An epoch step: the run floor at the epoch call.
    exact reached.countedRun_enoughStake (UInt64.le_of_eq anchorSlot) (absent w honest k bound)
      early pre (enough w honest k bound) genesis held childFound parent before path boundary
      countedOk later upper

/-- A store's justified checkpoint after an epoch has a signer from a set that the count can't miss.

The count passed, so a validator among the quorum voters of that set voted for the checkpoint.

The set misses the count when the quorum voters outside it hold less than two thirds of the total.

That bound is the premise `fewCounted`, for each state that the store counts in.

The vote was cast in a block that the store holds, below the counting state, and the block was sent.

The anchor's latest header must be the anchor block's, with a zero state root. -/
theorem Execution.justifiedSigned_at [DecidablePred (· ∈ J)] {anchor : Store preset fork}
    {g : ForkedBeaconState preset} {epoch horizon : Epoch} {last : Nat}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    (delay : preset.InclusionDelayPositive)
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) last)
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    (afterAnchor : getCurrentEpoch anchorState ≤ epoch)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} {slot : Slot}
    (high : (e.world k).time ≤ last)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (later : epoch < ((e.world k).state w).justifiedCheckpoint.epoch)
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (fewCounted : ∀ (root : Root) (base state : BeaconState preset fork) (total : Gwei),
      ((e.world k).state w).blockStates[root]? = some base →
      (state = base ∨ ∃ (slot : Slot) (childRoot : Root) (child : BeaconBlock preset fork),
        ((e.world k).state w).blocks[childRoot]? = some child ∧ child.parentRoot = root ∧
        slot ≤ child.slot ∧ processSlots config checks base slot = .ok state) →
      ((e.world k).state w).getCheckpointBlock root
        ((e.world k).state w).justifiedCheckpoint.epoch =
          .ok ((e.world k).state w).justifiedCheckpoint.root →
      epoch < getCurrentEpoch state →
      ((e.world k).state w).justifiedCheckpoint.epoch ≤ getCurrentEpoch state →
      (getCurrentEpoch state).toNat ≤
        ((e.world k).state w).justifiedCheckpoint.epoch.toNat + 1 →
      (getCurrentEpoch state).toNat ≤ horizon.toNat →
      getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
        2 * total.toNat) :
    ∃ v, p v ∧ ∃ i, (e.world i).time ≤ (e.world k).time ∧ ∃ m ∈ (e.world i).sent, ∃ data,
      (v, data) ∈ statements config checks anchorState anchorBlock m ∧
      data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < slot := by
  have reached := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) k w honest
  obtain ⟨sound, anchorEarly, -⟩ := DirectSafety.run_justified_separated pre genesis
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots; omega
  have apart := parameters.lookahead
  -- The checkpoint is after the anchor's epoch, so one count set it.
  have afterNat := UInt64.lt_iff_toNat_lt.mp later
  have anchorNat := UInt64.le_iff_toNat_le.mp afterAnchor
  obtain ⟨root, base, counted, pulled, held, shape, pulledOk, pulledC, changed⟩ :=
    reached.justified_counted sound (UInt64.lt_iff_toNat_lt.mpr (by omega))
  -- The count moved the checkpoint, to the counting state's current or previous epoch.
  have moved : pulled.currentJustifiedCheckpoint ≠ counted.currentJustifiedCheckpoint :=
    fun same => changed (same.symm.trans pulledC)
  obtain ⟨⟨countedLater, countedEpoch⟩, rootRead⟩ : (GENESIS_EPOCH + 1 < getCurrentEpoch counted ∧
      (getCurrentEpoch counted).toNat ≤
        ((e.world k).state w).justifiedCheckpoint.epoch.toNat + 1 ∧
      ((e.world k).state w).justifiedCheckpoint.epoch.toNat ≤
        (getCurrentEpoch counted).toNat) ∧
      getBlockRoot counted ((e.world k).state w).justifiedCheckpoint.epoch =
        .ok ((e.world k).state w).justifiedCheckpoint.root := by
    rcases processJustificationAndFinalization_reads pulledOk with ⟨-, same⟩ |
      ⟨late, _, _, _, _, _, _, _, _, _, _, weighed⟩
    · exact (moved (same ▸ rfl)).elim
    rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, -⟩ |
      ⟨current, -, -, -, -, -, epochEq, rootOk⟩
    · exact (moved same).elim
    have rootRead : getBlockRoot counted ((e.world k).state w).justifiedCheckpoint.epoch =
        .ok ((e.world k).state w).justifiedCheckpoint.root := by
      rw [← pulledC]
      exact rootOk
    refine ⟨?_, rootRead⟩
    rw [← pulledC, epochEq]
    refine ⟨late, ?_⟩
    cases current
    · simp only [Bool.false_eq_true, ↓reduceIte, getPreviousEpoch_toNat]
      have := UInt64.lt_iff_toNat_lt.mp late
      simp only [GENESIS_EPOCH] at this
      omega
    · simp
  -- The store's epoch bounds the checkpoint, and the horizon bounds the store's epoch.
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have checkpointBound := (reached.forwardReachable.justified_epoch_le_current sound slots
    (UInt64.le_of_eq anchorSlot) epochOk).1
  have horizonBound := bounded w honest k _ high epochOk
  have upper : (getCurrentEpoch counted).toNat ≤ horizon.toNat + 1 := by
    have := UInt64.le_iff_toNat_le.mp checkpointBound
    have := UInt64.le_iff_toNat_le.mp horizonBound
    omega
  -- The participation of the counting state is backed by early or held votes.
  obtain ⟨anchorPending, anchorFlags⟩ :=
    DirectSafety.inherited_participation pre Run.nil parameters genesis
  obtain ⟨baseFlags, basePending, baseEarly⟩ := reached.held_participation
    (UInt64.le_of_eq anchorSlot) positive window apart anchorFlags anchorPending anchorEarly held
  -- The counting state is the held state, or one cached slot of a state on its way to a child.
  have shapeCopy := shape
  obtain ⟨state, path, cached, sameSlot⟩ : ∃ state,
      (state = base ∨ ∃ slot, processSlots config checks base slot = .ok state) ∧
        (counted = base ∨ processSlot state = .ok counted) ∧ state.slot = counted.slot := by
    rcases shapeCopy with rfl | ⟨state, -, -, -, -, -, path, -, countedOk⟩
    · exact ⟨counted, .inl rfl, .inl rfl, rfl⟩
    · exact ⟨state, path, .inr countedOk, (processSlot_slot countedOk).symm⟩
  -- The slots and the cached slot keep the backing.
  have backed : TargetFlagsVoted ({vote | vote.2.target.epoch ≤ getCurrentEpoch anchorState} ∪
        ((e.world k).state w).votesBelow config checks root) counted ∧
      PendingVoted ({vote | vote.2.target.epoch ≤ getCurrentEpoch anchorState} ∪
        ((e.world k).state w).votesBelow config checks root) counted := by
    rcases shape with rfl | ⟨state, -, -, -, -, -, path, -, countedOk⟩
    · exact ⟨baseFlags, basePending⟩
    · obtain ⟨stateFlags, statePending, -⟩ : TargetFlagsVoted _ state ∧ PendingVoted _ state ∧
          JustifiedEarly state := by
        rcases path with rfl | ⟨_, slotsOk⟩
        · exact ⟨baseFlags, basePending, baseEarly⟩
        · exact votedParticipation_processSlots positive window apart baseFlags basePending
            baseEarly slotsOk
      exact ⟨stateFlags.of_processSlot positive window countedOk,
        statePending.of_processSlot countedOk⟩
  -- Byzantine stake is below two thirds where the count ran.
  have epochLt : epoch < getCurrentEpoch counted := by
    have := countedEpoch.2
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  have justifiedLe : ((e.world k).state w).justifiedCheckpoint.epoch ≤ getCurrentEpoch counted :=
    UInt64.le_iff_toNat_le.mpr countedEpoch.2
  have justifiedAfter : getCurrentEpoch anchorState <
      ((e.world k).state w).justifiedCheckpoint.epoch :=
    UInt64.lt_iff_toNat_lt.mpr (by omega)
  -- The store walks from the counting root to the justified checkpoint, less than a buffer back.
  obtain ⟨reachedSlot, path'⟩ : ∃ reachedSlot,
      state = base ∨ processSlots config checks base reachedSlot = .ok state := by
    rcases path with same | ⟨reachedSlot, slotsOk⟩
    · exact ⟨0, .inl same⟩
    · exact ⟨reachedSlot, .inr slotsOk⟩
  have walk : ((e.world k).state w).getCheckpointBlock root
      ((e.world k).state w).justifiedCheckpoint.epoch =
        .ok ((e.world k).state w).justifiedCheckpoint.root :=
    (reached.counted_history anchorSlot anchorHeader anchorZero
      (roots w honest k high) held path' cached
      (fun _ start startOk => by
        have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
        have epochLe := countedEpoch.1
        rw [getCurrentEpoch_toNat] at epochLe
        have slotLt := Nat.lt_div_mul_add (a := counted.slot.toNat) positive
        have spread := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochLe
        rw [Nat.add_mul, Nat.one_mul] at spread
        rw [startNat, sameSlot]
        omega)
      rootRead
      (fun start startOk => by
        have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
        have epochLt := UInt64.lt_iff_toNat_lt.mp justifiedAfter
        rw [getCurrentEpoch_toNat] at epochLt
        have slotLt := Nat.lt_div_mul_add (a := anchorState.slot.toNat) positive
        have spread :=
          Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (Nat.succ_le_of_lt epochLt)
        rw [Nat.succ_mul] at spread
        exact UInt64.le_iff_toNat_le.mpr (by rw [startNat]; omega))).2
  -- No state of the count is after the horizon, since the store's epoch is not.
  have stateBound := reached.forwardReachable.blockState_epoch_le_current slots
    (UInt64.le_of_eq anchorSlot) epochOk
  have insideHeld : ∀ {r : Root} {s : BeaconState preset fork},
      ((e.world k).state w).blockStates[r]? = some s → (getCurrentEpoch s).toNat ≤ horizon.toNat :=
    fun found => Nat.le_trans (UInt64.le_iff_toNat_le.mp (stateBound _ _ found))
      (UInt64.le_iff_toNat_le.mp horizonBound)
  have few : ∀ total, getTotalActiveBalance counted = .ok total →
      3 * stake (fun index => balanceAt counted index.toNat)
        {v ∈ quorumVoters counted | ¬p v} < 2 * total.toNat := by
    intro total totalOk
    rcases shape with rfl | ⟨state, childRoot, child, childFound, parent, before, path, -,
      countedOk⟩
    · exact fewCounted root counted counted total held (.inl rfl) walk epochLt justifiedLe
        countedEpoch.1 (insideHeld held) totalOk
    · -- Caching a slot keeps the registry, the balances and the slot that the count reads.
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok countedOk
      obtain ⟨childState, childStored, -⟩ := reached.reachable.blockStatesFromParents childFound
      have childSlot := reached.reachable.blockState_slot_eq anchorSlot childFound childStored
      rcases path with rfl | ⟨reachedSlot, slotsOk⟩
      · exact fewCounted root state state total held (.inl rfl) walk epochLt justifiedLe
          countedEpoch.1 (insideHeld held) totalOk
      · have slotLe : reachedSlot ≤ child.slot := by
          rw [← (processSlots_slot slotsOk).2]
          exact UInt64.le_of_lt before
        refine fewCounted root base state total held
          (.inr ⟨reachedSlot, childRoot, child, childFound, parent, slotLe, slotsOk⟩) walk
          epochLt justifiedLe countedEpoch.1 ?_ totalOk
        have epochLe : getCurrentEpoch state ≤ getCurrentEpoch childState := by
          have : state.slot ≤ childState.slot := by
            rw [childSlot, (processSlots_slot slotsOk).2]
            exact slotLe
          rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
          exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp this)
        exact Nat.le_trans (UInt64.le_iff_toNat_le.mp epochLe) (insideHeld childStored)
  -- The count's active stake is above one and a half increments.
  have large := counted_stake_large anchored start anchorSlot genesis pre absent heldEarly enough
    terminal honest high held shape countedLater upper
  -- So an honest quorum voter voted for the checkpoint.
  obtain ⟨current, vote, member, voter, link, target⟩ :=
    processJustificationAndFinalization_exists_voter p backed.1 backed.2 large few pulledOk
      moved
  rw [pulledC] at target
  have voteEpoch : getCurrentEpoch anchorState < vote.2.target.epoch := by
    rw [target]
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  rcases member with earlier | below
  · exact absurd earlier (UInt64.not_le.mpr voteEpoch)
  have voteWalk : ((e.world k).state w).getCheckpointBlock root vote.2.target.epoch =
      .ok vote.2.target.root := by
    rw [target]
    exact walk
  -- The vote is a statement of a message sent by now, of a slot before the store's slot.
  obtain ⟨m, sent, signed, before⟩ := e.exists_sent_of_votesBelow anchored start anchorSlot slots
    positive apart delay honest (absent w honest k high) below voteWalk slotOk
  exact ⟨vote.1, voter, k, le_rfl, m, sent, vote.2, signed, target, before⟩

/-- Each up-to-date honest store's justified checkpoint after an epoch has an honest signer.

The epoch is at or after the anchor's.

Byzantine stake is below two thirds wherever an honest store counts votes for a later target.

The checkpoint was set by one count of votes, in a state the store holds or on the way from one.

The count passed, so an honest validator among the quorum voters voted for the checkpoint.

Its vote was cast in a block the store holds, below the counting state.

The store reads that block's attestation with a valid signature, and the block was sent.

The anchor state ends a run from a deposited genesis, and the stake floors bound the active stake.

The anchor's latest header must be the anchor block's, with a zero state root.

The genesis state has one, since its latest header is that of the genesis block.

So has the state after the anchor block, since `process_block` stores a zero state root.

The anchor store checks neither, and without them a justified root may be one no store holds. -/
theorem Execution.justifiedHonestlySigned [DecidablePred (· ∈ J)] {anchor : Store preset fork}
    {g : ForkedBeaconState preset} {epoch horizon : Epoch} {first last : Nat}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    (delay : preset.InclusionDelayPositive)
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) last)
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    (afterAnchor : getCurrentEpoch anchorState ≤ epoch)
    (byzantine : ByzantineCountedStake (e := e) epoch first last) :
    JustifiedHonestlySigned (e := e) epoch first last := by
  intro w honest k slot low high upToDate slotOk later
  exact Execution.justifiedSigned_at anchored start anchorSlot anchorHeader anchorZero slots
    parameters delay genesis pre roots absent heldEarly bounded enough terminal afterAnchor honest
    high slotOk later (· ∈ J)
    fun root base state total held shape _ epochLt _ _ _ totalOk =>
      byzantine w honest k state total low high upToDate
        ⟨root, base, held, shape.imp id fun ⟨slot, childRoot, child, found, parent, le, ok⟩ =>
          ⟨checks, slot, childRoot, child, found, parent, le, ok⟩⟩ epochLt totalOk

end EthLib.Consensus.Models.Network
