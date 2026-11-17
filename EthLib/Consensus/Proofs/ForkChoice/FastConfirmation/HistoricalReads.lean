module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements

/-!
# Receiver reads for historical-anchor transport

Residual compatibility and the finality companion supply receiver reads or explicit evidence.

These reads do not establish the source surplus or the historical-anchor endpoint.
-/

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

public theorem compatibility_of_residual {horizon : Epoch} {last : Nat}
    (residual : ResidualFinalizedCheckpointCompatibility (e := e) horizon last)
    (family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ last →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root) :
    FinalizedCheckpointCompatibility (e := e) horizon last := by
  intro a honestA b honestB i j timeI timeJ checkpoint selected ordered bounded
  by_cases sameStore : a = b ∧ i ≤ j ∧ checkpoint = ((e.world j).state b).justifiedCheckpoint
  · obtain ⟨rfl, later, rfl⟩ := sameStore
    exact family a honestA i j later timeJ
  · exact residual a honestA b honestB i j timeI timeJ checkpoint selected sameStore ordered bounded

/-- The finality companion supplies the finalized-prefix family or explicit evidence. -/
public theorem Execution.finalizedFamily_or_historical_evidence {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS)
    {horizon : Epoch} {last : Nat}
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat} (inTime : (e.world n).time ≤ last) :
    (∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ last →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root) ∨
    HistoricalFinalityEvidence (e := e) pre last := by
  have forward w (member : w ∈ J) k := e.forwardReachableWith
    (fun a ha => (anchored a ha) ▸ Store.ForwardReachableWith.anchor anchorStore) k w member
  -- An honest held copy of the anchor supplies the nonzero root required by the companion.
  obtain ⟨root, _, anchorFound⟩ := (forward u honest n).reachable.anchor_known
  have nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0 :=
    roots u honest n inTime root anchorBlock anchorFound
  have justifiedBound w (member : w ∈ J) k (time : (e.world k).time ≤ last) :
      ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon := by
    obtain ⟨current, currentOk, _, _⟩ := (forward w member k).forwardReachable.slots_le_current
      slots (UInt64.le_of_eq anchorSlot)
    have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset current) := by
      simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
    exact UInt64.le_trans
      ((forward w member k).forwardReachable.justified_epoch_le_current sound slots
        (UInt64.le_of_eq anchorSlot) epochOk).1
      (bounded w member k _ time epochOk)
  exact e.finalized_prefix_or_accountable anchorStore anchored parameters genesis pre
    anchorSlot boundary nonzero absent justifiedBound early enough terminal

private theorem compatibility_or_historical_evidence {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS)
    {horizon : Epoch} {last : Nat}
    (residual : ResidualFinalizedCheckpointCompatibility (e := e) horizon last)
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat} (inTime : (e.world n).time ≤ last) :
    FinalizedCheckpointCompatibility (e := e) horizon last ∨
      HistoricalFinalityEvidence (e := e) pre last := by
  rcases e.finalizedFamily_or_historical_evidence anchorStore anchored sound anchorSlot boundary
      slots bounded roots absent parameters genesis pre early enough terminal honest inTime with
    family | evidence
  · exact .inl (compatibility_of_residual residual family)
  · exact .inr evidence

private theorem receiver_reads_or_historical_evidence {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (slots : 0 < config.SLOT_DURATION_MS)
    (early : fork < .glamsterdam) {horizon : Epoch} {time : Nat}
    (residual : ResidualFinalizedCheckpointCompatibility (e := e) horizon time)
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (supply : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (absent : AnchorParentAbsent (e := e) time)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : Nat}
    (later : (e.world n).time ≤ time) (atTime : (e.world k).time = time)
    (updated : UpToDate config checks sources (e.world k).time
      ((e.world k).view w) ((e.world k).state w))
    {head : ForkChoiceNode} {state source : BeaconState preset fork} {callerHead root : Root}
    {block parent : BeaconBlock preset fork} {slot current first last beforeBlock finish : Slot}
    {epoch : Epoch} {window participants : Std.TreeSet ValidatorIndex} {maximum : Gwei}
    (blockOk : ((e.world n).state u).block root = .ok block)
    (known : ((e.world k).state w).blocks[root]? = some block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    (above : ((e.world k).state w).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (callerSlot : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (callerLast : subChecked slot 1 = .ok last)
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (stateOk : ((e.world k).state w).checkpointState
      ((e.world k).state w).justifiedCheckpoint = .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (lastOk : subChecked current 1 = .ok finish)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first finish =
      .ok window)
    (participantsOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first
      beforeBlock = .ok participants)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots callerHead source
      first last = .ok maximum)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100) :
    ((∃ receiverMaximum discount,
      ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state
        first last = .ok receiverMaximum ∧
      ((e.world k).state w).computeEmptySlotSupportDiscount config head.root state
        root = .ok discount) ∨
    ∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
      ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
        some evidence) ∨ HistoricalFinalityEvidence (e := e) pre time := by
  rcases compatibility_or_historical_evidence anchorStore anchored sound anchorSlot boundary
      slots residual bounded roots absent parameters genesis pre heldEarly enough terminal
      caller later with compatible | evidence
  · exact .inl (receiver_reads_of_historical_observations anchorStore anchored sound anchorSlot
      boundary positive slots early compatible bounded supply absent caller receiver later atTime
      updated blockOk known parentOk above firstOk beforeOk callerSlot callerLast headOk stateOk
      currentOk epochOk lastOk windowOk participantsOk maximumOk half)
  · exact .inr evidence

end EthLib.Consensus.Models.Network
