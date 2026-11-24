module

public import EthLib.Consensus.Proofs.LivenessBlock
public import EthLib.Consensus.Proofs.LivenessVotes
public import EthLib.Consensus.Proofs.SlotCommitteeStake
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.PlausibleLivenessSteps
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.Chain
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.FfgSlotSteps

/-!
# Proofs: plausible liveness of the beacon chain, from Altair until Gloas

Take a state reached from a genesis state, in some epoch.

Honest validators with two thirds of the stake and a margin can extend the chain from it.

This is Theorem 2 of Casper FFG on the beacon chain.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Models Serialization.Ssz DirectSafety DirectSafety.Apriori

variable {preset : Preset} {config : Config}

/-- The conditions on a state of the continuation. -/
structure ContinuationConditions (config : Config) (honest : Finset ValidatorIndex)
    (key : ValidatorIndex → Signatures.SecretKey) (proposals : Set Slot) (gap : Nat)
    (w : ForkedBeaconState preset) : Prop where
  /-- The state is before Gloas. -/
  beforeGloas : w.fork < .glamsterdam
  /-- The slot step from the state succeeds. -/
  slot : ∃ next, advanceSlotAcross config .bls w = .ok next
  /-- The active validators times the committees of the current epoch fit in 64 bits. -/
  shuffleRoom : (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).length *
    ((getCommitteeCountPerSlot w.state (getCurrentEpoch w.state)).toNat *
      preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64
  /-- The committees of each slot of the current epoch have values. -/
  committees : ∀ slot : Slot, computeEpochAtSlot preset slot = getCurrentEpoch w.state →
    ∃ committees : List (Array ValidatorIndex), (List.range
        (getCommitteeCountPerSlot w.state (getCurrentEpoch w.state)).toNat).mapM
      (fun position => getBeaconCommittee w.state slot position.toUInt64) = .ok committees
  /-- At a slot of a proposal after the latest block header, the proposer is honest.

  There the state meets the conditions of its honest proposal, for some budget. -/
  propose : w.state.slot ∈ proposals → w.state.latestBlockHeader.slot < w.state.slot →
    ∃ (budget scoreBound : Nat) (proposer : ValidatorIndex),
      getBeaconProposerIndex w.state = .ok proposer ∧ proposer ∈ honest ∧
        ProposalConditions config honest key budget scoreBound gap w.state proposer

/-- An honest continuation through a later epoch, from its first state, reaches its last slot.

An honest run from `x` reaches the first state, at the first slot of an epoch after that of `x`.

That epoch is at most two after that of `x`, and the first state has no upgrade due.

Its slot is after its latest block header.

The run gathers the votes of all slots of the epoch but the last. -/
private theorem exists_epochStage
    [∀ fork, LawfulSszType (BeaconState preset fork)]
    [∀ fork, LawfulSszType (BeaconBlockBody preset fork)]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (parameters : DirectSafety.Parameters preset) (roots : preset.RootsReachPreviousEpoch)
    (periodFits :
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (incrementLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.largestEffectiveBalance)
    (inclusion : preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤ 1)
    (committeesPositive : 0 < preset.MAX_COMMITTEES_PER_SLOT)
    {x s : ForkedBeaconState preset} (altair : .altair ≤ x.fork)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {proposals : Set Slot} {gap : Nat}
    (covered : ∀ slot : Slot,
      (getCurrentEpoch x.state).toNat < (computeEpochAtSlot preset slot).toNat →
      (computeEpochAtSlot preset slot).toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
      (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 →
      ∃ proposal ∈ proposals, slot < proposal ∧
        computeEpochAtSlot preset proposal = computeEpochAtSlot preset slot ∧
        proposal.toNat ≤ slot.toNat + gap)
    (continuation : ∀ (w : ForkedBeaconState preset) (run : Run config .bls x w),
      run.Honest config honest key → run.BlocksAt proposals →
      (getCurrentEpoch w.state).toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
        ContinuationConditions config honest key proposals gap w)
    (pre : Run config .bls x s) (honestPre : pre.Honest config honest key)
    (blocksPre : pre.BlocksAt proposals)
    (low : (getCurrentEpoch x.state).toNat < (getCurrentEpoch s.state).toNat)
    (high : (getCurrentEpoch s.state).toNat ≤ (getCurrentEpoch x.state).toNat + 2)
    (first : s.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0)
    (fresh : s.state.latestBlockHeader.slot < s.state.slot)
    (notDue : upgradeDue config s = false) :
    ∃ (z : ForkedBeaconState preset) (run : Run config .bls s z),
      run.Honest config honest key ∧ run.BlocksAt proposals ∧ z.fork = s.fork ∧
      getCurrentEpoch z.state = getCurrentEpoch s.state ∧
      (z.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
      z.state.latestBlockHeader.slot ≤ z.state.slot ∧
      z.state.currentJustifiedCheckpoint = s.state.currentJustifiedCheckpoint ∧
      z.state.justificationBits = s.state.justificationBits ∧
      VotesGathered honest z.state := by
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := roots.twoSlots
    omega
  have altairS : .altair ≤ s.fork := Nat.le_trans altair (fork_le_of_chainSteps pre.chainSteps)
  -- The conditions of the continuation give the slot steps and the honest blocks of the epoch.
  refine exists_epochContinuation (gap := gap) positive parameters.lookahead altairS first fresh
    ?_ ?_ ?_
  · -- Each slot step of the epoch is a slot step of a continuation from `x`.
    intro w run honestRun blocksRun same
    exact (continuation w (pre.append run) (honestPre.append honestRun)
      (blocksPre.append blocksRun) (by rw [same]; exact high)).slot
  · intro slot epoch notLast
    have epochNat := congrArg UInt64.toNat epoch
    obtain ⟨proposal, member, after, sameEpoch, within⟩ :=
      covered slot (by omega) (by omega) notLast
    exact ⟨proposal, member, after, sameEpoch.trans epoch, within⟩
  · -- At a slot of a proposal the honest proposer builds its block, with no upgrade due.
    intro fork w run honestRun blocksRun same proposed fresh'
    have conditions := continuation ⟨fork, w⟩ (pre.append run) (honestPre.append honestRun)
      (blocksPre.append blocksRun) (by change (getCurrentEpoch w).toNat ≤ _; rw [same]; exact high)
    obtain ⟨budget, scoreBound, proposer, proposerOk, honestProposer, proposal⟩ :=
      conditions.propose proposed fresh'
    have altairW : .altair ≤ fork :=
      Nat.le_trans altair (fork_le_of_chainSteps (pre.append run).chainSteps)
    exact exists_honestBlock_gathersVotes altairW conditions.beforeGloas parameters.lookahead
      periodFits roots increment scaled incrementLe inclusion committeesPositive
      proposerOk honestProposer fresh' (run.notDue_of_fresh notDue fresh') proposal

/-- Plausible liveness of the beacon chain, from Altair until Gloas.

A run from a genesis state `g` reaches `x`, from Altair, in an epoch `e` past the first.

The preset meets the parameters of accountable safety and of the honest block.

The seed lookahead reaches two epochs.

The guard of the a priori drift holds at `x` through `e + 2`.

The honest validators are active at `x` in `e`, `e + 1` and `e + 2`, and not slashed.

In `e + 1` and `e + 2`, take any set of at most one slot's share of the active validators.

Without it, three times their stake at `x` covers twice the active stake plus the margin.

Each of them signed no slashable pair among old votes.

Each of their old votes has a source at most the justified epoch at `x`, a target at most `e`.

Every slot of `e + 1` and `e + 2` but the last of each has a proposal after it in its epoch.

That proposal is within the gap.

Take an honest run from `x` with blocks only at the slots of proposals.

Each of its states up to `e + 2` meets the conditions of the continuation.

These conditions include that the state is before Gloas.

Then a run from `x` by honest steps finalizes `e + 1`, above the current justified epoch at `x`.

Its votes are votes of honest validators, and no honest validator becomes slashable. -/
theorem plausible_liveness_beacon
    [∀ fork, LawfulSszType (BeaconState preset fork)]
    [∀ fork, LawfulSszType (BeaconBlockBody preset fork)]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (roots : preset.RootsReachPreviousEpoch)
    (periodFits :
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (incrementLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.largestEffectiveBalance)
    (inclusion : preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤ 1)
    (committeesPositive : 0 < preset.MAX_COMMITTEES_PER_SLOT)
    -- A seed lookahead of two epochs fixes the activity of `e + 1` and `e + 2` at `x`.
    (lookahead : 2 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {g x : ForkedBeaconState preset} (shared : Run config .bls g x)
    (genesis : Genesis (config := config) (checks := .bls) g)
    (altair : .altair ≤ x.fork) (late : 1 ≤ (getCurrentEpoch x.state).toNat)
    (guard : aprioriGuardAt config x ((getCurrentEpoch x.state).toNat + 1))
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (active : ∀ i ∈ honest, ∀ epoch : Epoch,
      epoch.toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
      (getCurrentEpoch x.state).toNat ≤ epoch.toNat →
        i ∈ getActiveValidatorIndices x.state epoch)
    (unslashed : ∀ i ∈ honest,
      (x.state.validators.data[i.toNat]?).map (·.slashed) = some false)
    (margin : ∀ epoch : Epoch, (getCurrentEpoch x.state).toNat < epoch.toNat →
      epoch.toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
      ∀ excluded ⊆ (getActiveValidatorIndices x.state epoch).toFinset,
        excluded.card ≤ (getActiveValidatorIndices x.state epoch).length /
          preset.SLOTS_PER_EPOCH.toNat + 1 →
        2 * stake (fun i => balanceAt x.state i.toNat)
            (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset +
          stakeMargin config x ((getCurrentEpoch x.state).toNat + 1) ≤
        3 * stake (fun i => balanceAt x.state i.toNat) (honest \ excluded))
    {old : Set (ValidatorIndex × AttestationData)}
    (safe : ∀ i ∈ honest, ¬SlashableIn old i)
    (fresh : ∀ i ∈ honest, ∀ data, (i, data) ∈ old →
      data.source.epoch ≤ x.state.currentJustifiedCheckpoint.epoch ∧
        data.target.epoch ≤ getCurrentEpoch x.state)
    {proposals : Set Slot} {gap : Nat}
    (covered : ∀ slot : Slot,
      (getCurrentEpoch x.state).toNat < (computeEpochAtSlot preset slot).toNat →
      (computeEpochAtSlot preset slot).toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
      (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 →
      ∃ proposal ∈ proposals, slot < proposal ∧
        computeEpochAtSlot preset proposal = computeEpochAtSlot preset slot ∧
        proposal.toNat ≤ slot.toNat + gap)
    (continuation : ∀ (w : ForkedBeaconState preset) (run : Run config .bls x w),
      run.Honest config honest key → run.BlocksAt proposals →
      (getCurrentEpoch w.state).toNat ≤ (getCurrentEpoch x.state).toNat + 2 →
        ContinuationConditions config honest key proposals gap w) :
    ∃ (y : ForkedBeaconState preset) (run : Run config .bls x y),
      run.Honest config honest key ∧ (∀ vote ∈ run.votes, vote.1 ∈ honest) ∧
      y.state.finalizedCheckpoint.epoch.toNat = (getCurrentEpoch x.state).toNat + 1 ∧
      x.state.currentJustifiedCheckpoint.epoch < y.state.finalizedCheckpoint.epoch ∧
      ∀ i ∈ honest, ¬SlashableIn (old ∪ run.votes) i := by
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := roots.twoSlots
    omega
  have invariantX := Run.invariant (Genesis.invariant genesis) shared
  -- The extension runs to the end of the epoch, then through two more epochs.
  --
  -- Empty slots lead from `x` to the first slot of the next epoch.
  obtain ⟨s1, r1, honest1, none1, epoch1, first1, fresh1⟩ :=
    exists_slotsContinuation (honest := honest) (key := key) positive
      (headerSlot_le_of_run genesis shared) fun w run none same =>
        (continuation w run (run.honest_of_blockCount none) (run.blocksAt_of_blockCount none)
          (by rw [same]; omega)).slot
  have blocks1 : r1.BlocksAt proposals := r1.blocksAt_of_blockCount none1
  have notDue1 : upgradeDue config s1 = false := by
    refine r1.notDue_of_moved (fun same => ?_) fresh1
    have := congrArg UInt64.toNat same
    omega
  -- In each of the two epochs, honest proposers carry the honest votes of every slot but the last.
  --
  -- The first epoch of the continuation gathers its votes.
  obtain ⟨z1, q1, honestQ1, blocksQ1, forkZ1, epochZ1, lastZ1, behindZ1, justifiedZ1, bitsZ1,
      gatheredZ1⟩ :=
    exists_epochStage parameters roots periodFits increment scaled incrementLe inclusion
      committeesPositive altair covered continuation r1 honest1 blocks1 (by omega)
      (by omega) first1 fresh1 notDue1
  have epochZ1Nat : (getCurrentEpoch z1.state).toNat = (getCurrentEpoch x.state).toNat + 1 := by
    rw [epochZ1, epoch1]
  have conditions1 := continuation z1 (r1.append q1) (honest1.append honestQ1)
    (blocks1.append blocksQ1) (by omega)
  -- The slot step out of its last slot starts the second epoch.
  obtain ⟨s2, ok1⟩ := conditions1.slot
  obtain ⟨header2, moved2⟩ := headerSlot_of_advanceSlotAcross ok1
  have fresh2 : s2.state.latestBlockHeader.slot < s2.state.slot := by
    rw [header2, UInt64.lt_iff_toNat_lt, moved2]
    have := UInt64.le_iff_toNat_le.mp behindZ1
    omega
  have first2 : s2.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
    rw [moved2]
    exact lastZ1
  have epoch2 : (getCurrentEpoch s2.state).toNat = (getCurrentEpoch x.state).toNat + 2 := by
    rw [getCurrentEpoch_toNat, moved2, Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero lastZ1),
      ← getCurrentEpoch_toNat, epochZ1Nat]
  have honest2 : (r1.append (q1.snoc (.slot ok1))).Honest config honest key :=
    honest1.append (Run.Honest.snoc (step := .slot ok1) honestQ1 trivial)
  have blocks2 : (r1.append (q1.snoc (.slot ok1))).BlocksAt proposals :=
    blocks1.append (blocksQ1.snoc (step := .slot ok1) trivial)
  -- The second epoch of the continuation gathers its votes.
  obtain ⟨z2, q2, honestQ2, blocksQ2, forkZ2, epochZ2, lastZ2, behindZ2, justifiedZ2, bitsZ2,
      gatheredZ2⟩ :=
    exists_epochStage parameters roots periodFits increment scaled incrementLe inclusion
      committeesPositive altair covered continuation (r1.append (q1.snoc (.slot ok1)))
      honest2 blocks2 (by omega) (by omega) first2 fresh2 ((Step.slot ok1).notDue_of_fresh fresh2)
  have epochZ2Nat : (getCurrentEpoch z2.state).toNat = (getCurrentEpoch x.state).toNat + 2 := by
    rw [epochZ2, epoch2]
  let tail := (q1.snoc (.slot ok1)).append q2
  have honestTail : tail.Honest config honest key :=
    Run.Honest.append (Run.Honest.snoc (step := .slot ok1) honestQ1 trivial) honestQ2
  have honest3 : (r1.append tail).Honest config honest key := honest1.append honestTail
  have blocks3 : (r1.append tail).BlocksAt proposals :=
    blocks1.append (Run.BlocksAt.append (blocksQ1.snoc (step := .slot ok1) trivial) blocksQ2)
  have conditions2 := continuation z2 (r1.append tail) honest3 blocks3 (by omega)
  obtain ⟨y, ok2⟩ := conditions2.slot
  -- The tests at the ends of the two epochs count the honest validators outside the last slots.
  have altairZ1 : .altair ≤ z1.fork :=
    Nat.le_trans altair (fork_le_of_chainSteps (r1.append q1).chainSteps)
  have altairZ2 : .altair ≤ z2.fork :=
    Nat.le_trans altair (fork_le_of_chainSteps (r1.append tail).chainSteps)
  -- The margin keeps their stake at two thirds of the active stake at both ends.
  obtain ⟨counted1, counted1Ok, quorum1⟩ :=
    exists_counted_quorum shared (r1.append q1) genesis parameters caps aligned roots lookahead
      guard (honest1.append honestQ1) active unslashed margin altairZ1 conditions1.beforeGloas
      (by omega) (by omega) lastZ1 conditions1.shuffleRoom
      (conditions1.committees z1.state.slot rfl) gatheredZ1
  obtain ⟨counted2, counted2Ok, quorum2⟩ :=
    exists_counted_quorum shared (r1.append tail) genesis parameters caps aligned roots lookahead
      guard honest3 active unslashed margin altairZ2 conditions2.beforeGloas
      (by omega) (by omega) lastZ2 conditions2.shuffleRoom
      (conditions2.committees z2.state.slot rfl) gatheredZ2
  have lateZ1 : GENESIS_EPOCH + 1 < getCurrentEpoch z1.state := by
    rw [UInt64.lt_iff_toNat_lt, epochZ1Nat]
    have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := rfl
    omega
  -- So the two epochs are justified, and the first is finalized.
  obtain ⟨-, finalizedEpoch, -⟩ := advanceSlotAcross_finalizesTwoEpochs altairZ1 altairZ2 ok1
    lastZ1 lateZ1 counted1Ok quorum1
    justifiedZ2 bitsZ2 (by omega) ok2 lastZ2 counted2Ok quorum2
  -- The votes of the run are those of its honest blocks, all after the empty slots.
  have votesOf : ∀ {vote}, vote ∈ ((r1.append tail).snoc (.slot ok2)).votes →
      vote ∈ (r1.append tail).votes ∧ vote ∈ tail.votes := fun member =>
    ⟨Run.mem_votes_of_snocSlot member,
      Run.mem_votes_of_append none1 (Run.mem_votes_of_snocSlot member)⟩
  have invariant1 := Run.invariant invariantX r1
  -- Before each step of the run the active validators times the committees fit in 64 bits.
  have room : ∀ (before after : ForkedBeaconState preset)
      (step : Step config .bls before after), (r1.append tail).Contains step →
      (getActiveValidatorIndices before.state (getCurrentEpoch before.state)).length *
        ((getCommitteeCountPerSlot before.state (getCurrentEpoch before.state)).toNat *
          preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64 := by
    intro before after step member
    obtain ⟨pre, post, split⟩ := (r1.append tail).contains_split step member
    have inside : ∀ {u v : ForkedBeaconState preset} {other : Step config .bls u v},
        pre.Contains other → (r1.append tail).Contains other := by
      intro _ _ other contained
      rw [split]
      exact (Run.contains_append _ post other).mpr (.inl (.earlier contained step))
    have later := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
    exact (continuation before pre (fun other contained => honest3 other (inside contained))
      (fun other contained => blocks3 other (inside contained)) (by omega)).shuffleRoom
  refine ⟨y, (r1.append tail).snoc (.slot ok2), honest3.snoc (step := .slot ok2) trivial,
    fun vote member => (honest3.vote_fresh invariantX (votesOf member).1).1, ?_, ?_, ?_⟩
  · -- The finalized epoch is the first epoch of the continuation.
    rw [finalizedEpoch, epochZ1Nat]
  · -- The finalized epoch is the first epoch of the continuation, past the justified one at `x`.
    have settled := invariantX.settled
    unfold JustifiedSettled at settled
    have previous := getPreviousEpoch_le x.state
    rw [finalizedEpoch, UInt64.lt_iff_toNat_lt, epochZ1Nat]
    have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans settled previous)
    omega
  · -- The honest validators vote once in each epoch, from the justified source of that epoch.
    --
    -- New votes have a fresh source and a target from the first epoch of the continuation on.
    --
    -- So none of them becomes slashable.
    intro i member
    refine not_slashableIn_union_of_fresh (source := x.state.currentJustifiedCheckpoint.epoch)
      (target := getCurrentEpoch s1.state) (safe i member) (fun data old => ?_)
      (fun data new => ?_) (fun data1 data2 one two same => ?_)
      (fun data1 data2 one two before => ?_)
    · obtain ⟨source, target⟩ := fresh i member data old
      refine ⟨source, ?_⟩
      rw [UInt64.lt_iff_toNat_lt, epoch1]
      have := UInt64.le_iff_toNat_le.mp target
      omega
    · exact ⟨(honest3.vote_fresh invariantX (votesOf new).1).2.1,
        (honestTail.vote_fresh invariant1 (votesOf new).2).2.2⟩
    · exact honest3.vote_eq parameters.lookahead room (votesOf one).1 (votesOf two).1 same
    · exact honest3.source_le invariantX (votesOf one).1 (votesOf two).1 before

end EthLib.Consensus
