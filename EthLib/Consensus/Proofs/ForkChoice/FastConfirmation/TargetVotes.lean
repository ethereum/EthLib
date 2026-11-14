module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties

/-!
# Honest count and an accepted checkpoint test

An assumed honest count supplies a concrete set of voters for the current target.

When the no-conflict test accepts its numerical branch, that set exceeds a third of the balance.

Honest count remains a hypothesis, as in the aggregate safety argument.

This module does not establish the count from a Byzantine-stake bound or prove LMD support.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- The assumed honest count for a head, measured in its pulled-up state.

Each counted honest validator is active.

It either signs the target or lies outside the past committee set.

Three times their stake covers three times the computed support plus `margin`. -/
def HonestTargetVotes
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (margin : ℕ) (u : ValidatorIndex) (n : ℕ) (head : Root) : Prop :=
  ∀ state support target slot epochStart lastSlot participants,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    ((e.world n).state u).computeHonestFfgSupportForCurrentTarget config head = .ok support →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok epochStart →
    subChecked slot 1 = .ok lastSlot →
    ((e.world n).state u).getCommitteesBetweenSlots head epochStart lastSlot = .ok participants →
    ∃ voters : Finset ValidatorIndex,
      (∀ v ∈ voters, v ∈ J ∧
        v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ∧
        (SignsTarget e v target (e.world n).time ∨ v ∉ participants)) ∧
      3 * support.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters

/-- Instantiating honest count with successful support reads supplies its concrete voters. -/
private theorem quorum_of_count {u : ValidatorIndex} {n margin : ℕ}
    {head : Root} (count : HonestTargetVotes e margin u n head)
    {state : BeaconState preset fork} {support : Gwei}
    (stateOk : ((e.world n).state u).getPulledUpHeadState config head = .ok state)
    (supportOk : ((e.world n).state u).computeHonestFfgSupportForCurrentTarget config head =
      .ok support) :
    ∃ target slot first last participants, ∃ voters : Finset ValidatorIndex,
      ((e.world n).state u).getCurrentTarget config head = .ok target ∧
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch ∧
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first ∧
      subChecked slot 1 = .ok last ∧
      ((e.world n).state u).getCommitteesBetweenSlots head first last = .ok participants ∧
      ((e.world n).state u).getCheckpointBlock head target.epoch = .ok target.root ∧
      (∀ v ∈ voters, v ∈ J ∧
        v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ∧
        (SignsTarget e v target (e.world n).time ∨ v ∉ participants)) ∧
      3 * support.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters := by
  have supportRead := supportOk
  simp only [Store.computeHonestFfgSupportForCurrentTarget, bind_ok_iff, mapError_ok_iff]
    at supportRead
  obtain ⟨slot, slotOk, readState, stateRead, total, totalOk, score, scoreOk, first, firstOk,
    last, lastOk, weight, weightOk, rest⟩ := supportRead
  have stateEq := Except.ok.inj (stateRead.symm.trans stateOk)
  subst readState
  have targetScore := scoreOk
  unfold Store.getCurrentTargetScore at targetScore
  obtain ⟨target, targetOk, _⟩ := bind_ok_iff.mp targetScore
  obtain ⟨_, _, _, _, _, _, adversary, adversaryOk, _⟩ := rest
  obtain ⟨_, _, _, _, _, equivocationOk, _⟩ :=
    Store.computeAdversarialWeight_steps adversaryOk
  unfold Store.getEquivocationScore at equivocationOk
  obtain ⟨participants, participantsOk, _⟩ := bind_ok_iff.mp equivocationOk
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have targetRead := targetOk
  simp only [Store.getCurrentTarget, epochOk, Store.getCheckpointForBlock, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at targetRead
  obtain ⟨_, rfl, root, checkpointOk, rfl⟩ := targetRead
  obtain ⟨voters, members, bound⟩ := count state support
    ⟨computeEpochAtSlot preset slot, root⟩ slot first last participants
    stateOk supportOk targetOk slotOk firstOk lastOk participantsOk
  exact ⟨_, slot, first, last, participants, voters, targetOk,
    slotOk, epochOk, firstOk, lastOk, participantsOk, checkpointOk, members, bound⟩

/-- An accepted no-conflict test names the unrealized target or a concrete honest quorum.

Honest count is assumed, not established by the Boolean test.

In the numerical branch, three times the voters' stake exceeds total balance plus `margin`. -/
theorem quorum_of_no_conflicting_checkpoint {u : ValidatorIndex} {n margin : ℕ}
    {head : Root} (count : HonestTargetVotes e margin u n head)
    (checked : ((e.world n).state u).willNoConflictingCheckpointBeJustified config head =
      .ok true) :
    ((e.world n).state u).getCurrentTarget config head =
        .ok ((e.world n).state u).unrealizedJustifiedCheckpoint ∨
      ∃ state total target slot first last participants, ∃ voters : Finset ValidatorIndex,
        ((e.world n).state u).getPulledUpHeadState config head = .ok state ∧
        getTotalActiveBalance state = .ok total ∧
        ((e.world n).state u).getCurrentTarget config head = .ok target ∧
        ((e.world n).state u).getCurrentSlot config = .ok slot ∧
        ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch ∧
        computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first ∧
        subChecked slot 1 = .ok last ∧
        ((e.world n).state u).getCommitteesBetweenSlots head first last = .ok participants ∧
        ((e.world n).state u).getCheckpointBlock head target.epoch = .ok target.root ∧
        (∀ v ∈ voters, v ∈ J ∧
          v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ∧
          (SignsTarget e v target (e.world n).time ∨ v ∉ participants)) ∧
        total.toNat + margin < 3 * stake (fun v => balanceAt state v.toNat) voters := by
  obtain ⟨target, targetOk, _⟩ := bind_ok_iff.mp checked
  rcases (Store.willNoConflictingCheckpointBeJustified_eq_ok_true_iff targetOk).mp checked with
    same | ⟨state, total, support, thrice, stateOk, totalOk, supportOk, productOk, lt⟩
  · exact .inl (same ▸ targetOk)
  · obtain ⟨target', slot, first, last, participants, voters, targetOk', slotOk, epochOk,
      firstOk, lastOk, participantsOk, checkpointOk, members, bound⟩ :=
      quorum_of_count count stateOk supportOk
    have productNat := (mulChecked_ok_iff.mp productOk).2
    have less := UInt64.lt_iff_toNat_lt.mp lt
    refine .inr ⟨state, total, target', slot, first, last, participants, voters,
      stateOk, totalOk, targetOk', slotOk, epochOk, firstOk, lastOk, participantsOk,
      checkpointOk, members, ?_⟩
    simp only [UInt64.toNat_ofNat] at productNat
    omega

end EthLib.Consensus.Models.Network
