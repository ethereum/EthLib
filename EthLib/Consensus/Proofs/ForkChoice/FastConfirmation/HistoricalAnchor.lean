module

import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads

/-!
# Composition for historical-anchor transport

The private head composition takes the source-window result as an input.

It does not establish that source result or the historical-anchor endpoint.
-/

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Compose an assumed source result without discharging the source-window obligation. -/
private theorem compose_source_window [DecidablePred (· ∈ J)]
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {last n call : Nat} {u caller : ValidatorIndex}
    (history : VoteCommitteeCommonHistory (e := e) last) (honest : u ∈ J)
    (time : (e.world n).time ≤ last)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) (before : fork < .glamsterdam)
    (absent : AnchorParentAbsent (e := e) last)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {head : ForkChoiceNode} {state source : BeaconState preset fork} {shift : Nat}
    {root : Root} {block parent : BeaconBlock preset fork}
    {current first finish shortLast : Slot} {epoch : Epoch}
    {members participants : Std.TreeSet ValidatorIndex} {nodes : List ForkChoiceNode}
    (headRead : ((e.world n).state u).getHead config = .ok head)
    (stateRead : ((e.world n).state u).checkpointState
      ((e.world n).state u).justifiedCheckpoint = .ok state)
    (tree : ((e.world n).state u).getFilteredNodeTree config = .ok nodes)
    (found : ((e.world n).state u).blocks[root]? = some block)
    (callerHonest : caller ∈ J) (callerTime : (e.world call).time ≤ last)
    (later : (e.world call).time ≤ (e.world n).time)
    (drift : WindowMarginDrift (e := e) call last source shift)
    (callerParent : ((e.world call).state caller).block block.parentRoot = .ok parent)
    (slotRead : ((e.world n).state u).getCurrentSlot config = .ok current)
    (epochRead : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (horizon : epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked current 1 = .ok finish)
    (window : ((e.world n).state u).getCommitteesBetweenSlots head.root first finish =
      .ok members)
    (shortWindow : ((e.world n).state u).getCommitteesBetweenSlots head.root first shortLast =
      .ok participants)
    (shortLastOk : subChecked block.slot 1 = .ok shortLast)
    (viability : ((e.world n).state u).isAncestor
        ⟨((e.world n).state u).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    (parentSafe : ((e.world n).state u).isAncestor head
      ⟨block.parentRoot, .pending⟩ = .ok true)
    {score : Gwei} (scoreOk : computeProposerScore config state = .ok score)
    {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (sourceResult :
      ((e.world n).state u).isAncestor
        ⟨((e.world n).state u).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (∃ maximum sourceMaximum sourceScore,
        ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root state first finish =
          .ok maximum ∧
        ((e.world n).state u).computeCommitteeWeightBetweenSlots head.root source first finish =
          .ok sourceMaximum ∧
        computeProposerScore config source = .ok sourceScore ∧
        sourceMaximum.toNat + sourceScore.toNat + shift <
          2 * stake (fun v =>
            if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
            then balanceAt source v.toNat else 0)
            {v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩ | v ∈ J} +
          stake (fun v =>
            if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
            then balanceAt source v.toNat else 0)
            {v ∈ ((e.world n).state u).parentVotersOf source participants block parent | v ∈ J}) ∨
      (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ last ∧ (e.world j).time ≤ last ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨ HistoricalFinalityEvidence (e := e) pre last) :
    (((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true ∨
      ∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ last ∧ (e.world j).time ≤ last ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨ HistoricalFinalityEvidence (e := e) pre last := by
  have applyHead (route) := ancestor_head_of_window_margin anchorStore anchored history honest
    time anchorSlot before absent minLookahead maxLookahead ring headRead stateRead tree found
    callerHonest callerTime later drift (Store.block_ok_iff.mp callerParent) slotRead epochRead
    horizon firstOk lastOk window shortWindow shortLastOk route scoreOk
  rcases sourceResult with justified | surplus | collision | finalityEvidence
  · exact .inl (applyHead (.inl justified))
  · rcases viability with justified | viable
    · exact .inl (applyHead (.inl justified))
    · exact .inl (applyHead (.inr ⟨viable, parentSafe, surplus⟩))
  · exact .inl (.inr collision)
  · exact .inr finalityEvidence

end EthLib.Consensus.Models.Network
