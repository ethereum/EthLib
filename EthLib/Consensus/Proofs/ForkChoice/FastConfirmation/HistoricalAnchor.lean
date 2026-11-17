module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin

/-!
# Historical-anchor head ancestry

The source-window theorem supplies a surplus or explicit evidence.

The surplus and the approved drift give ancestry on the receiver's head chain.
-/

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A guarded historical margin gives head ancestry, a block collision or direct-safety evidence.

The receiver's head descends from the block at the receiver's time.

The voters below the parent lie in the head's window by the window-membership premise.

This extends the coverage of earlier honest heads, assumed from the call up to that time.

The direct-safety evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key.

The stake ceiling of `2 * 10^17` Gwei is `2 * 10^8` ETH, above mainnet's active stake.

The proof needs only a ceiling below `2^64` Gwei, so that the checked total cannot overflow. -/
public theorem Execution.isAncestor_getHead_of_window_membership [DecidablePred (· ∈ J)] {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    (membership : VotersInHeadWindow (e := e) time) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {block parent : BeaconBlock preset fork}
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
    {receiverLast : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first receiverLast) {horizon : Epoch}
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (rootCovers : HonestHeadsCover (e := e) root (e.world n).time time)
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
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finality : ReceiverFinalityCovers (e := e) w k root block)
    {receiverHead : ForkChoiceNode} {state : BeaconState preset fork}
    {current : Slot} {receiverEpoch : Epoch} {score : Gwei}
    {window participants : Std.TreeSet ValidatorIndex}
    (receiverHeadOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (receiverParent : ((e.world k).state w).isAncestor receiverHead
      ⟨block.parentRoot, .pending⟩ = .ok true)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (receiverNear : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (receiverLastOk : subChecked current 1 = .ok receiverLast)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      receiverLast = .ok window)
    (scoreOk : computeProposerScore config state = .ok score)
    (participantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      beforeBlock = .ok participants)
    (exit : WindowExitBound (config := config) ((e.world k).state w) source receiverHead.root
      first receiverLast)
    (absent : AnchorParentAbsent (e := e) time) {nodes : List ForkChoiceNode}
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (route : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    (((e.world k).state w).isAncestor receiverHead ⟨root, .pending⟩ = .ok true ∨
      ∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨ HistoricalDirectSafetyEvidence (e := e) pre time := by
  have sourceResult := e.source_surplus_or_historical_evidence sync slots positive minLookahead
    maxLookahead ring preGloas admitted half votes fits prompt windows anchored sound
    anchorSlot anchorBoundary start caller callerUpToDate headNode slotOk beginOk timeEq blockOk
    parentOk sourceOk boostOk firstOk lastOk beforeOk maximumOk parentParticipantsOk registry
    aligned increment supportOk discountOk adversaryOk margin callerTime sourceReads reserve
    bounded roots unslashed ceiling parameters genesis pre heldEarly enough terminal
    rootCovers headDescends historicalBelow callerEpochOk historicalEpochOk near epochStartOk
    epochStartTimeOk historyCovers receiver atTime upToDate known finality receiverHeadOk
    receiverParent stateOk currentOk receiverEpochOk receiverNear receiverLastOk windowOk
    participantsOk exit absent
  have applyHead (headRoute) := ancestor_head_of_window_membership anchored start membership
    receiver (by rw [atTime]) (UInt64.le_of_eq anchorSlot) preGloas absent receiverHeadOk stateOk
    tree known caller callerTime (by rw [atTime]; exact callerTime) drift
    (Store.block_ok_iff.mp parentOk) currentOk receiverEpochOk receiverNear firstOk receiverLastOk
    windowOk participantsOk beforeOk headRoute scoreOk
  rcases sourceResult with justified | surplus | collision | evidence
  · exact .inl (applyHead (.inl justified))
  · rcases route with justified | viable
    · exact .inl (applyHead (.inl justified))
    · exact .inl (applyHead (.inr ⟨viable, receiverParent, surplus⟩))
  · exact .inl (.inr collision)
  · exact .inr evidence

/-- A guarded historical margin gives head ancestry, a block collision or direct-safety evidence.

The receiver's head descends from the block at the receiver's time.

This extends the coverage of earlier honest heads, assumed from the call up to that time.

The direct-safety evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key.

The stake ceiling of `2 * 10^17` Gwei is `2 * 10^8` ETH, above mainnet's active stake.

The proof needs only a ceiling below `2^64` Gwei, so that the checked total cannot overflow. -/
public theorem Execution.isAncestor_getHead_of_historical_anchor [DecidablePred (· ∈ J)] {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    (history : VoteCommitteeCommonHistory (e := e) time) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {block parent : BeaconBlock preset fork}
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
    {receiverLast : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first receiverLast) {horizon : Epoch}
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (rootCovers : HonestHeadsCover (e := e) root (e.world n).time time)
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
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finality : ReceiverFinalityCovers (e := e) w k root block)
    {receiverHead : ForkChoiceNode} {state : BeaconState preset fork}
    {current : Slot} {receiverEpoch : Epoch} {score : Gwei}
    {window participants : Std.TreeSet ValidatorIndex}
    (receiverHeadOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (receiverParent : ((e.world k).state w).isAncestor receiverHead
      ⟨block.parentRoot, .pending⟩ = .ok true)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (receiverNear : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (receiverLastOk : subChecked current 1 = .ok receiverLast)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      receiverLast = .ok window)
    (scoreOk : computeProposerScore config state = .ok score)
    (participantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root first
      beforeBlock = .ok participants)
    (exit : WindowExitBound (config := config) ((e.world k).state w) source receiverHead.root
      first receiverLast)
    (absent : AnchorParentAbsent (e := e) time) {nodes : List ForkChoiceNode}
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (route : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    (((e.world k).state w).isAncestor receiverHead ⟨root, .pending⟩ = .ok true ∨
      ∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨ HistoricalDirectSafetyEvidence (e := e) pre time :=
  Execution.isAncestor_getHead_of_window_membership sync slots positive minLookahead maxLookahead
    ring preGloas admitted half votes fits prompt windows
    (Execution.votersInHeadWindow_of_commonHistory time anchored start
      (UInt64.le_of_eq anchorSlot) minLookahead maxLookahead ring history)
    anchored sound anchorSlot anchorBoundary start caller callerUpToDate headNode slotOk beginOk
    timeEq blockOk parentOk sourceOk boostOk firstOk lastOk beforeOk maximumOk parentParticipantsOk
    registry aligned increment supportOk discountOk adversaryOk margin callerTime sourceReads drift
    reserve bounded roots unslashed ceiling parameters genesis pre heldEarly enough terminal
    rootCovers headDescends historicalBelow callerEpochOk historicalEpochOk near epochStartOk
    epochStartTimeOk historyCovers receiver atTime upToDate known finality receiverHeadOk
    receiverParent stateOk currentOk receiverEpochOk receiverNear receiverLastOk windowOk scoreOk
    participantsOk exit absent tree route

end EthLib.Consensus.Models.Network
