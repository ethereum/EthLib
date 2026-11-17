module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport

/-!
# Finalized-prefix family for historical-anchor transport

The finality companion supplies the finalized-prefix family or explicit evidence.

Source surplus reads the family only within one store.

It needs each receiver's own finalized checkpoint on the chain of its own justified checkpoint.
-/

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Each honest store's justified checkpoint reads back its earlier finalized checkpoints.

Otherwise two runs from the anchor give direct-safety evidence.

That evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key. -/
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
    HistoricalDirectSafetyEvidence (e := e) pre last := by
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

/-- An honest held copy of the anchor block has a nonzero state root. -/
private theorem Execution.anchor_stateRoot_nonzero {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) {last : Nat}
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat} (inTime : (e.world n).time ≤ last) :
    anchorBlock.stateRoot ≠ Vector.replicate 32 0 := by
  obtain ⟨root, _, anchorFound⟩ := (e.forwardReachableWith
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachableWith.anchor anchorStore) n u
      honest).reachable.anchor_known
  exact roots u honest n inTime root anchorBlock anchorFound

/-- Honest justified checkpoints agree at each epoch up to the horizon, or evidence holds.

Otherwise two honest stores hold different justified checkpoints of one epoch.

Runs from the anchor to held states of both have views that hold the two checkpoints.

That evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key. -/
public theorem Execution.selectedCheckpointsAgree_or_evidence {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    {horizon : Epoch} {last : Nat}
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last) :
    SelectedCheckpointsAgree (e := e) horizon last ∨
      CrossStoreJustifiedEvidence (e := e) pre last := by
  classical
  by_cases agree : SelectedCheckpointsAgree (e := e) horizon last
  · exact .inl agree
  simp only [SelectedCheckpointsAgree, not_forall] at agree
  obtain ⟨a, honestA, b, honestB, i, j, timeA, timeB, first, second, selectedFirst,
    selectedSecond, epoch, inHorizon, different⟩ := agree
  have nonzero := e.anchor_stateRoot_nonzero anchorStore anchored roots honestA timeA
  rcases e.justified_eq_or_accountable anchorStore anchored parameters genesis pre
      anchorSlot nonzero absent early enough terminal honestA honestB timeA timeB selectedFirst
      selectedSecond epoch inHorizon with same | evidence
  · exact absurd same different
  · exact .inr ⟨a, honestA, b, honestB, i, j, timeA, timeB, first, second, selectedFirst,
      selectedSecond, epoch, different, evidence⟩

end EthLib.Consensus.Models.Network
