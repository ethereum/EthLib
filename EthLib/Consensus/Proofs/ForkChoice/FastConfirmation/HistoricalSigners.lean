module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalCoverage
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
  obtain ⟨countedLater, countedEpoch⟩ : GENESIS_EPOCH + 1 < getCurrentEpoch counted ∧
      (getCurrentEpoch counted).toNat ≤
        ((e.world k).state w).justifiedCheckpoint.epoch.toNat + 1 ∧
      ((e.world k).state w).justifiedCheckpoint.epoch.toNat ≤
        (getCurrentEpoch counted).toNat := by
    rcases processJustificationAndFinalization_reads pulledOk with ⟨-, same⟩ |
      ⟨late, _, _, _, _, _, _, _, _, _, _, weighed⟩
    · exact (moved (same ▸ rfl)).elim
    rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, -⟩ |
      ⟨current, -, -, -, -, -, epochEq, -⟩
    · exact (moved same).elim
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
  have few : ∀ total, getTotalActiveBalance counted = .ok total →
      3 * stake (fun index => balanceAt counted index.toNat)
        {v ∈ quorumVoters counted | ¬v ∈ J} < 2 * total.toNat := by
    intro total totalOk
    rcases shape with rfl | ⟨state, childRoot, child, childFound, parent, before, path, -,
      countedOk⟩
    · exact byzantine w honest k counted total low high upToDate ⟨root, counted, held, .inl rfl⟩
        epochLt totalOk
    · -- Caching a slot keeps the registry, the balances and the slot that the count reads.
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok countedOk
      have counts : CountedState ((e.world k).state w) config state := by
        refine ⟨root, base, held, ?_⟩
        rcases path with rfl | ⟨reached, slotsOk⟩
        · exact .inl rfl
        · refine .inr ⟨checks, reached, childRoot, child, childFound, parent, ?_, slotsOk⟩
          rw [← (processSlots_slot slotsOk).2]
          exact UInt64.le_of_lt before
      exact byzantine w honest k state total low high upToDate counts epochLt totalOk
  -- The count's active stake is above one and a half increments.
  have large := counted_stake_large anchored start anchorSlot genesis pre absent heldEarly enough
    terminal honest high held shape countedLater upper
  -- So an honest quorum voter voted for the checkpoint.
  obtain ⟨current, vote, member, voter, link, target⟩ :=
    processJustificationAndFinalization_exists_voter (· ∈ J) backed.1 backed.2 large few pulledOk
      moved
  rw [pulledC] at target
  have voteEpoch : getCurrentEpoch anchorState < vote.2.target.epoch := by
    rw [target]
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  rcases member with earlier | below
  · exact absurd earlier (UInt64.not_le.mpr voteEpoch)
  -- The store walks from the counting root to the vote's target, read less than a buffer back.
  obtain ⟨reachedSlot, path'⟩ : ∃ reachedSlot,
      state = base ∨ processSlots config checks base reachedSlot = .ok state := by
    rcases path with same | ⟨reachedSlot, slotsOk⟩
    · exact ⟨0, .inl same⟩
    · exact ⟨reachedSlot, .inr slotsOk⟩
  have walk := (reached.counted_history anchorSlot anchorHeader anchorZero
    (roots w honest k high) held path' cached
    (fun _ start startOk => by
      have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
      have epochLe := countedEpoch.1
      rw [← target, getCurrentEpoch_toNat] at epochLe
      have slotLt := Nat.lt_div_mul_add (a := counted.slot.toNat) positive
      have spread := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochLe
      rw [Nat.add_mul, Nat.one_mul] at spread
      rw [startNat, sameSlot]
      omega)
    link.2.2.2
    (fun start startOk => by
      have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
      have epochLt := UInt64.lt_iff_toNat_lt.mp voteEpoch
      rw [getCurrentEpoch_toNat] at epochLt
      have slotLt := Nat.lt_div_mul_add (a := anchorState.slot.toNat) positive
      have spread := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (Nat.succ_le_of_lt epochLt)
      rw [Nat.succ_mul] at spread
      exact UInt64.le_iff_toNat_le.mpr (by rw [startNat]; omega))).2
  -- The vote is a statement of a message sent by now, of a slot before the store's slot.
  obtain ⟨m, sent, signed, before⟩ := e.exists_sent_of_votesBelow anchored start anchorSlot slots
    positive apart delay honest (absent w honest k high) below walk slotOk
  exact ⟨vote.1, voter, k, le_rfl, m, sent, vote.2, signed, target, before⟩

/-- A guarded historical margin keeps the block on every honest head chain until the horizon.

It is the signed-justification headline with its honest signer derived.

The signer follows from Byzantine stake below two thirds in each state that counts later votes.

So the late half of the root's viability needs no honest signer as a premise.

It rests on that bound, the stake floors, the inclusion delay and conditions on the anchor.

The anchor's latest header must be the anchor block's, with a zero state root. -/
theorem Execution.honestHeadsCover_of_byzantine_bound [DecidablePred (· ∈ J)] {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    {n : ℕ} {block : BeaconBlock preset fork}
    (newVoters : NewlyActiveVotersInHeadWindow (e := e) block.parentRoot (e.world n).time time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {parent : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {boost maximum : Gwei}
    (headNode : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    {checkpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    (boostOk : computeProposerScore config source = .ok boost)
    (firstOk : addChecked parent.slot 1 = .ok first) (lastOk : subChecked slot 1 = .ok last)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head first
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei} (registry : source.RegistryWithinLimit)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head source root =
      .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head source root =
      .ok adversary)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (callerTime : (e.world n).time ≤ time) (sourceReads : SourceWindowReads (e := e) n time source)
    (drift : WindowMarginDrift (e := e) n time source shift)
    {finish : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first finish)
    {x : ValidatorIndex} (reference : x ∈ J) {m : ℕ} (referenceTime : time ≤ (e.world m).time)
    (referenceUpToDate : UpToDate config checks sources (e.world m).time ((e.world m).view x)
      ((e.world m).state x))
    {referenceSlot : Slot}
    (referenceSlotOk : ((e.world m).state x).getCurrentSlot config = .ok referenceSlot)
    (finishOk : subChecked referenceSlot 1 = .ok finish)
    {horizon : Epoch}
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (headDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (near : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    (absent : AnchorParentAbsent (e := e) time)
    (parentCovers : HonestHeadsCover (e := e) block.parentRoot (e.world n).time (time + 1))
    (fit : config.CommitteeWindowsFit preset)
    (consistent : EarlyJustifiedConsistent (e := e) root callerEpoch (e.world n).time time)
    (leaf : RootKeepsViableLeaf (e := e) root (e.world n).time time)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (delay : preset.InclusionDelayPositive)
    (byzantine : ByzantineCountedStake (e := e) callerEpoch (e.world n).time time)
    (exits : ReceiverWindowExitsNear (e := e) (computeEpochAtSlot preset parent.slot) source first
      (e.world n).time time)
    (late : LateDutyMajority (e := e) (computeEpochAtSlot preset parent.slot)
      (e.world n).time time) :
    HonestHeadsCover (e := e) root (e.world n).time (time + 1) ∨
      (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨
      HistoricalDirectSafetyEvidence (e := e) pre time := by
  -- The anchor state is held at the caller, so the caller's epoch is not before the anchor's.
  have reached := e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) n u caller
  obtain ⟨anchorRoot, -, anchorHeld⟩ := reached.reachable.anchor_known
  obtain ⟨anchorKept, stateHeld, isAnchor, -⟩ :=
    reached.reachable.blockStatesFromParents anchorHeld
  rw [isAnchor rfl] at stateHeld
  have afterAnchor := reached.forwardReachable.blockState_epoch_le_current slots
    (UInt64.le_of_eq anchorSlot) callerEpochOk anchorRoot anchorState stateHeld
  exact Execution.honestHeadsCover_of_signed_justification
    sync slots minLookahead maxLookahead ring preGloas admitted half votes fits prompt
    windows newVoters anchored sound anchorSlot anchorBoundary start caller callerUpToDate headNode
    slotOk beginOk timeEq blockOk parentOk sourceOk boostOk firstOk lastOk beforeOk maximumOk
    parentParticipantsOk registry aligned increment supportOk discountOk adversaryOk margin
    callerTime sourceReads drift reserve reference referenceTime referenceUpToDate
    referenceSlotOk finishOk bounded roots unslashed ceiling scoreFits parameters
    genesis pre heldEarly enough terminal headDescends historicalBelow callerEpochOk
    historicalEpochOk near epochStartOk epochStartTimeOk historyCovers absent parentCovers fit
    consistent leaf
    (Execution.justifiedHonestlySigned anchored start anchorSlot anchorHeader anchorZero slots
        parameters delay genesis pre roots absent heldEarly bounded enough terminal afterAnchor
        byzantine)
    exits late

end EthLib.Consensus.Models.Network
