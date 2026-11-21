module

public import EthLib.Consensus.Proofs.HonestBlockInput
public import EthLib.Consensus.Proofs.Transition.TargetVotes
public import EthLib.Consensus.Proofs.Transition.RunKept
public import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.ParticipationFlagsKept
import EthLib.Consensus.Proofs.Transition.RootLinks

/-!
# Proofs: an honest continuation of one epoch gathers the target votes of its slots

Plausible liveness extends the chain with blocks of honest proposers that carry honest votes.

Such a continuation is a run whose blocks are honest, from proposers of the honest set.

The honest validators of a slot vote for the latest block at that slot and the target of its epoch.

Their source is the current justified checkpoint.

After a block at a slot of the epoch, the honest voters of the slots just before it must be flagged.

Every slot of an epoch but the last must have such a block after it in the epoch, within a gap.

With two slots or more in an epoch, the last slot must then have a block of an honest proposer.

Then a run through the epoch gives each honest member of those slots the timely target flag.

The flag holds at the last slot of the epoch, where the justification test reads it.

The run keeps the justified checkpoint and the bits of justification through the epoch.

The blocks of the run and its slot steps are hypotheses of the theorem.

They quantify over the honest runs from the first state of the epoch.

Those runs apply blocks only at the slots of the proposals.

This is one part of the continuation in Theorem 2 of Casper FFG, on the beacon chain from Altair.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## Honest votes and honest runs -/

/-- The vote of an honest validator, as a block carries it on a state.

The validator is honest, and sits in a committee of the slot of the vote.

Before Electra the index of the data names that committee; from Electra it is zero.

The state is before Gloas, where the index also votes on the presence of the payload.

The slot is in the current epoch of the state.

The head is the latest block at that slot or before.

The source is the current justified checkpoint of the state.

The target is the current epoch, with the root of the latest block at its first slot or before.

The head and the target are read on the chain that carries the vote, with no reorganization.

A proposer may also carry other valid votes; this model of an honest block carries only these. -/
structure HonestVote (honest : Finset ValidatorIndex) {fork : Fork}
    (state : BeaconState preset fork) (vote : ValidatorIndex × AttestationData) : Prop where
  /-- The validator is honest. -/
  honest : vote.1 ∈ honest
  /-- The slot of the vote is in the current epoch. -/
  slot : computeEpochAtSlot preset vote.2.slot = getCurrentEpoch state
  /-- The head is the root of the latest block at the slot of the vote or before. -/
  head : getBlockRootAtSlot state vote.2.slot = .ok vote.2.beaconBlockRoot
  /-- The source is the current justified checkpoint. -/
  source : vote.2.source = state.currentJustifiedCheckpoint
  /-- The target epoch is the current epoch. -/
  target : vote.2.target.epoch = getCurrentEpoch state
  /-- The target root is the root of the latest block at the first slot of the epoch or before. -/
  targetRoot : getBlockRoot state (getCurrentEpoch state) = .ok vote.2.target.root
  /-- The validator sits in a committee of the slot, which the index names before Electra. -/
  committee : ∃ (index : CommitteeIndex) (members : Array ValidatorIndex),
    index < getCommitteeCountPerSlot state (getCurrentEpoch state) ∧
      getBeaconCommittee state vote.2.slot index = .ok members ∧ vote.1 ∈ members ∧
      vote.2.index = if .pectra ≤ fork then 0 else index
  /-- The state is before Gloas, where the index also votes on the payload. -/
  beforeGloas : fork < .glamsterdam

/-- A step of an honest continuation: a slot, or the block of an honest proposer.

The block is one that an honest proposer may build, with the key of its proposer.

Each vote that it carries is an honest vote on the state before it.

It carries only honest votes of the epoch of the block, a restriction of the model. -/
def Step.Honest (config : Config) (honest : Finset ValidatorIndex)
    (key : ValidatorIndex → Signatures.SecretKey) {before after : ForkedBeaconState preset} :
    Step config checks before after → Prop
  | .slot _ => True
  | .block _ signed _ _ => signed.message.proposerIndex ∈ honest ∧
      HonestBlock config before.state (key signed.message.proposerIndex) signed.message ∧
      ∀ vote ∈ blockVotes before.state signed.message, HonestVote honest before.state vote

/-- A run whose steps are all steps of an honest continuation. -/
def Run.Honest (config : Config) (honest : Finset ValidatorIndex)
    (key : ValidatorIndex → Signatures.SecretKey) {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : Prop :=
  ∀ {before after : ForkedBeaconState preset} (step : Step config checks before after),
    run.Contains step → step.Honest config honest key

/-- The empty run is honest. -/
theorem Run.Honest.nil {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {first : ForkedBeaconState preset} :
    (Run.nil : Run config checks first first).Honest config honest key := by
  intro _ _ step member
  cases member

/-- A step that applies a block only at a slot of a set: a slot, or a block at such a slot. -/
def Step.BlockAt (proposals : Set Slot) {before after : ForkedBeaconState preset} :
    Step config checks before after → Prop
  | .slot _ => True
  | .block .. => before.state.slot ∈ proposals

/-- A run that applies blocks only at the slots of a set. -/
def Run.BlocksAt (proposals : Set Slot) {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : Prop :=
  ∀ {before after : ForkedBeaconState preset} (step : Step config checks before after),
    run.Contains step → step.BlockAt proposals

/-- An honest run followed by an honest step is honest. -/
theorem Run.Honest.snoc {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {first middle last : ForkedBeaconState preset}
    {run : Run config checks first middle} {step : Step config checks middle last}
    (honestRun : run.Honest config honest key) (honestStep : step.Honest config honest key) :
    (run.snoc step).Honest config honest key := by
  intro _ _ other member
  cases member with
  | last => exact honestStep
  | earlier member => exact honestRun other member

/-- Two honest runs in sequence form an honest run. -/
theorem Run.Honest.append {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {first middle last : ForkedBeaconState preset}
    {pre : Run config checks first middle} {tail : Run config checks middle last}
    (honestPre : pre.Honest config honest key) (honestTail : tail.Honest config honest key) :
    (pre.append tail).Honest config honest key := by
  intro _ _ step member
  rcases (Run.contains_append pre tail step).mp member with member | member
  · exact honestPre step member
  · exact honestTail step member

/-! ## The votes that blocks gather -/

/-- From Altair, the flags that a step from a state gives to the slots shortly before it.

Take a slot of the current epoch before the slot of the state, by at most the gap.

Each honest member of each committee of that slot then holds the timely target flag after it.

Before Altair it says nothing. -/
def GathersVotes (honest : Finset ValidatorIndex) (gap : Nat) {fork : Fork}
    (state after : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (slot : Slot),
    computeEpochAtSlot preset slot = getCurrentEpoch state → slot < state.slot →
    state.slot.toNat ≤ slot.toNat + gap →
    ∀ (index : CommitteeIndex) (members : Array ValidatorIndex),
      index < getCommitteeCountPerSlot state (getCurrentEpoch state) →
      getBeaconCommittee state slot index = .ok members →
      ∀ member ∈ members, member ∈ honest →
        TargetFlagAt (after.currentEpochParticipation altair) member.toNat

/-- The flags of every slot of the current epoch but the last, at a state.

Each honest member of each committee of such a slot holds the timely target flag. -/
def VotesGathered (honest : Finset ValidatorIndex) {fork : Fork}
    (state : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (slot : Slot),
    computeEpochAtSlot preset slot = getCurrentEpoch state →
    (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 →
    ∀ (index : CommitteeIndex) (members : Array ValidatorIndex),
      index < getCommitteeCountPerSlot state (getCurrentEpoch state) →
      getBeaconCommittee state slot index = .ok members →
      ∀ member ∈ members, member ∈ honest →
        TargetFlagAt (state.currentEpochParticipation altair) member.toNat

/-! ## Walks of slot steps -/

/-- The empty run applies no block. -/
private theorem Run.BlocksAt.nil {proposals : Set Slot} {first : ForkedBeaconState preset} :
    (Run.nil : Run config checks first first).BlocksAt proposals := by
  intro _ _ step member
  cases member

/-- A run with blocks only at the proposals, then a step with that property, keeps it. -/
theorem Run.BlocksAt.snoc {proposals : Set Slot}
    {first middle last : ForkedBeaconState preset}
    {run : Run config checks first middle} {step : Step config checks middle last}
    (blocks : run.BlocksAt proposals) (blockAt : step.BlockAt proposals) :
    (run.snoc step).BlocksAt proposals := by
  intro _ _ other member
  cases member with
  | last => exact blockAt
  | earlier member => exact blocks other member

/-- Two runs with blocks only at the proposals, joined, have blocks only there too. -/
theorem Run.BlocksAt.append {proposals : Set Slot} {first middle last : ForkedBeaconState preset}
    {pre : Run config checks first middle} {tail : Run config checks middle last}
    (one : pre.BlocksAt proposals) (two : tail.BlocksAt proposals) :
    (pre.append tail).BlocksAt proposals := by
  intro _ _ step member
  rcases (Run.contains_append pre tail step).mp member with member | member
  · exact one step member
  · exact two step member

/-- The slot after a slot starts the next epoch when it is a multiple of the epoch length.

Otherwise it stays in the same epoch. -/
private theorem succ_div_cases {a p : Nat} :
    ((a + 1) % p = 0 → (a + 1) / p = a / p + 1) ∧ ((a + 1) % p ≠ 0 → (a + 1) / p = a / p) := by
  rw [Nat.succ_div]
  refine ⟨fun boundary => ?_, fun inside => ?_⟩
  · simp only [Nat.dvd_of_mod_eq_zero boundary, ↓reduceIte]
  · have apart : ¬ p ∣ a + 1 := fun divides => inside (Nat.mod_eq_zero_of_dvd divides)
    simp only [apart, ↓reduceIte, Nat.add_zero]

/-- Honest empty slot steps from a state of an epoch reach the first slot of the next epoch.

The induction counts the slots left before that first slot. -/
private theorem exists_slotsWalk {s : ForkedBeaconState preset}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : ∀ (w : ForkedBeaconState preset) (run : Run config checks s w),
      run.blockCount = 0 → getCurrentEpoch w.state = getCurrentEpoch s.state →
        ∃ next, advanceSlotAcross config checks w = .ok next) (n : Nat) :
    ∀ (w : ForkedBeaconState preset) (run : Run config checks s w),
      run.Honest config honest key → run.blockCount = 0 →
      getCurrentEpoch w.state = getCurrentEpoch s.state →
      w.state.latestBlockHeader.slot ≤ w.state.slot →
      ((getCurrentEpoch s.state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat -
        w.state.slot.toNat = n →
    ∃ (z : ForkedBeaconState preset) (run : Run config checks s z),
      run.Honest config honest key ∧ run.blockCount = 0 ∧
      (getCurrentEpoch z.state).toNat = (getCurrentEpoch s.state).toNat + 1 ∧
      z.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
      z.state.latestBlockHeader.slot < z.state.slot := by
  induction n with
  | zero =>
    -- A state of the epoch is before its end, so some slot is always left.
    intro w run _ _ same _ left
    have epochNat := congrArg UInt64.toNat same
    rw [getCurrentEpoch_toNat] at epochNat
    have below := Nat.lt_mul_div_succ w.state.slot.toNat positive
    rw [epochNat, Nat.mul_comm] at below
    omega
  | succ n ih =>
    intro w run honestRun none same behind left
    obtain ⟨next, ok⟩ := slots w run none same
    obtain ⟨moved, -, -, _, -, header⟩ := advanceSlotAcross_cases ok
    -- The slot step keeps the slot of the latest block header and moves the slot on by one.
    have headerSlot : next.state.latestBlockHeader.slot = w.state.latestBlockHeader.slot := by
      rw [header]
      split <;> rfl
    have epochNat := congrArg UInt64.toNat same
    rw [getCurrentEpoch_toNat] at epochNat
    have stepped : (run.snoc (.slot ok)).Honest config honest key :=
      honestRun.snoc (step := .slot ok) trivial
    have fresh : next.state.latestBlockHeader.slot < next.state.slot := by
      rw [headerSlot, UInt64.lt_iff_toNat_lt, moved]
      have := UInt64.le_iff_toNat_le.mp behind
      omega
    by_cases boundary : next.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0
    · refine ⟨next, run.snoc (.slot ok), stepped, none, ?_, boundary, fresh⟩
      rw [getCurrentEpoch_toNat, moved, ← epochNat]
      exact succ_div_cases.1 (moved ▸ boundary)
    · refine ih next (run.snoc (.slot ok)) stepped none ?_ (UInt64.le_of_lt fresh) ?_
      · apply UInt64.toNat_inj.mp
        rw [getCurrentEpoch_toNat, moved, ← epochNat]
        exact succ_div_cases.2 (moved ▸ boundary)
      · rw [moved]
        omega

/-- A slot at or before the last slot of its epoch, in the epoch of a later slot, is before it.

The later slot is the last of its epoch. -/
private theorem lt_succ_of_same_epoch {p v k : Nat} (positive : 0 < k) (same : p / k = v / k)
    (last : (v + 1) % k = 0) : p < v + 1 := by
  have below := Nat.lt_mul_div_succ p positive
  have split := Nat.div_add_mod (v + 1) k
  rw [last, succ_div_cases.1 last, ← same] at split
  omega

/-! ## Walks through one epoch -/

/-- A slot step that stays in its epoch runs no epoch step and no upgrade.

It keeps the fork, the current flags, the justified checkpoint and the bits of justification.

It keeps the slot of the latest block header, moves the slot on by one, and is a run step. -/
private theorem slotStep_inside {fork : Fork} {w : BeaconState preset fork}
    {next : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks ⟨fork, w⟩ = .ok next)
    (inside : (w.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0) :
    ∃ after : BeaconState preset fork, next = ⟨fork, after⟩ ∧
      after.slot.toNat = w.slot.toNat + 1 ∧ RunKept w after ∧
      after.currentEpochParticipation = w.currentEpochParticipation ∧
      after.currentJustifiedCheckpoint = w.currentJustifiedCheckpoint ∧
      after.justificationBits = w.justificationBits ∧
      after.latestBlockHeader.slot = w.latestBlockHeader.slot := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  have runKept := runKept_advanceSlot advancedOk
  obtain ⟨_, -, header⟩ := advanceSlot_latestBlockHeader advancedOk
  obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, advancedEq⟩ :=
    advanceSlot_ok advancedOk
  -- The slot reached is not the first of an epoch, so no epoch step and no upgrade run.
  have notFirst : ¬ nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
    intro zero
    apply inside
    rw [← sum]
    simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat zero
  rcases epochIfLast_cases epochedOk with ⟨first, -⟩ | ⟨-, kept⟩
  · exact absurd first notFirst
  have due : upgradeDue config ⟨fork, advanced⟩ = false := by
    apply upgradeDue_of_not_first
    rw [advancedEq]
    exact notFirst
  have reached := Except.ok.inj ((processUpgrades_of_not_due due).symm.trans upgraded)
  subst reached kept
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  refine ⟨advanced, rfl, by rw [advancedEq]; exact sum, runKept, ?_, ?_, ?_, ?_⟩
  · rw [advancedEq]
  · rw [advancedEq]
  · rw [advancedEq]
  · rw [header]
    split <;> rfl

/-- The facts that a walk through an epoch keeps, from its first state to a later state.

The later state is in the same epoch, with the same checkpoint and bits.

It is reached by steps that keep the registry and the committees.

Take a slot of the epoch with a proposal after it, before a bound and within the gap.

Each honest member of each committee of that slot then holds the timely target flag.

The committees and their count are those of the first state. -/
private def EpochKept (honest : Finset ValidatorIndex) (gap : Nat) (proposals : Set Slot)
    {fork : Fork} (altair : .altair ≤ fork) (start w : BeaconState preset fork) (bound : Nat) :
    Prop :=
  getCurrentEpoch w = getCurrentEpoch start ∧ RunKept start w ∧
    w.currentJustifiedCheckpoint = start.currentJustifiedCheckpoint ∧
    w.justificationBits = start.justificationBits ∧
    ∀ slot : Slot, computeEpochAtSlot preset slot = getCurrentEpoch start →
      (∃ proposal ∈ proposals, slot < proposal ∧ proposal.toNat < bound ∧
        proposal.toNat ≤ slot.toNat + gap) →
      ∀ (index : CommitteeIndex) (members : Array ValidatorIndex),
        index < getCommitteeCountPerSlot start (getCurrentEpoch start) →
        getBeaconCommittee start slot index = .ok members →
        ∀ member ∈ members, member ∈ honest →
          TargetFlagAt (w.currentEpochParticipation altair) member.toNat

/-- A run within the epoch of its first state keeps the committees of that epoch.

It also keeps their count per slot. -/
theorem committees_of_runKept
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {start w : BeaconState preset fork} (run : RunKept start w)
    (same : getCurrentEpoch w = getCurrentEpoch start) :
    CommitteesKept (getCurrentEpoch start) start w ∧
      getCommitteeCountPerSlot w (getCurrentEpoch start) =
        getCommitteeCountPerSlot start (getCurrentEpoch start) :=
  run.committees_count (by omega) (getCurrentEpoch_le_activityFixedEpoch start)
    (by rw [same]; omega)

/-- At a slot of the epoch, the honest block of a proposal, if there is one, keeps the walk.

The state it reaches is at the same slot, with the latest block header at or before it.

The flags then cover each proposal up to that slot. -/
private theorem exists_blockPhase {fork : Fork}
    {start u : BeaconState preset fork}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {proposals : Set Slot} {gap : Nat}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (altair : .altair ≤ fork)
    (propose : ∀ {fork' : Fork} (w : BeaconState preset fork')
      (run : Run config checks ⟨fork, start⟩ ⟨fork', w⟩),
      run.Honest config honest key → run.BlocksAt proposals →
      getCurrentEpoch w = getCurrentEpoch start →
      w.slot ∈ proposals → w.latestBlockHeader.slot < w.slot →
      ∃ (after : BeaconState preset fork') (engine : ExecutionEngine preset fork')
        (signed : SignedBeaconBlock preset fork') (due : upgradeDue config ⟨fork', w⟩ = false)
        (ok : applySignedBlock config checks engine w signed true = .ok after),
        (Step.block engine signed due ok).Honest config honest key ∧
          GathersVotes honest gap w after)
    (run : Run config checks ⟨fork, start⟩ ⟨fork, u⟩) (honestRun : run.Honest config honest key)
    (blocksRun : run.BlocksAt proposals)
    (kept : EpochKept honest gap proposals altair start u u.slot.toNat)
    (fresh : u.latestBlockHeader.slot < u.slot) :
    ∃ (v : BeaconState preset fork) (walked : Run config checks ⟨fork, start⟩ ⟨fork, v⟩),
      walked.Honest config honest key ∧ walked.BlocksAt proposals ∧ v.slot = u.slot ∧
      v.latestBlockHeader.slot ≤ v.slot ∧
      EpochKept honest gap proposals altair start v (u.slot.toNat + 1) := by
  obtain ⟨same, runKept, justified, bits, flags⟩ := kept
  by_cases proposed : u.slot ∈ proposals
  · obtain ⟨after, engine, signed, due, ok, honestStep, gathers⟩ :=
      propose u run honestRun blocksRun same proposed fresh
    have processed := (applySignedBlock_ok ok).2.1
    have frame := frame_processBlock processed
    obtain ⟨atSlot, -, -⟩ := processBlock_parentRoot processed
    obtain ⟨_, -, header⟩ := latestBlockHeader_processBlock processed
    have sameAfter : getCurrentEpoch after = getCurrentEpoch u := by
      simp only [getCurrentEpoch, frame.slot]
    obtain ⟨committees, count⟩ := committees_of_runKept apart runKept same
    refine ⟨after, run.snoc (.block engine signed due ok), honestRun.snoc honestStep,
      blocksRun.snoc (step := .block engine signed due ok) proposed, frame.slot,
      ?_, ⟨sameAfter.trans same, runKept.trans (runKept_processBlock processed),
        frame.currentJustified.trans justified, frame.justificationBits.trans bits, ?_⟩⟩
    · rw [header, frame.slot, atSlot]
      exact UInt64.le_refl _
    intro slot epoch ⟨proposal, member, after', below, within⟩ index members inside committee
      voter mem good
    rcases Nat.lt_or_ge proposal.toNat u.slot.toNat with earlier | atLeast
    · -- An earlier proposal set the flag, and the block keeps it.
      have active := mem_getActiveValidatorIndices_of_getBeaconCommittee committee mem
      have position := Nat.lt_of_lt_of_le (lt_size_of_mem_getActiveValidatorIndices active)
        runKept.grows
      exact TargetFlagAt.of_processBlock processed altair true position
        (flags slot epoch ⟨proposal, member, after', earlier, within⟩ index members inside
          committee voter mem good)
    · -- The proposal is this block, which gathers the votes of the slot.
      have equal : proposal.toNat = u.slot.toNat := by omega
      refine gathers altair slot (epoch.trans same.symm) ?_ (by omega) index members
        (by rw [same, count]; exact inside) (by rw [committees slot index epoch]; exact committee)
        voter mem good
      rw [UInt64.lt_iff_toNat_lt, ← equal]
      exact UInt64.lt_iff_toNat_lt.mp after'
  · refine ⟨u, run, honestRun, blocksRun, rfl, UInt64.le_of_lt fresh,
      ⟨same, runKept, justified, bits, ?_⟩⟩
    intro slot epoch ⟨proposal, member, after', below, within⟩
    -- No proposal sits at this slot, so the proposal is before it.
    have earlier : proposal.toNat < u.slot.toNat := by
      rcases Nat.lt_or_ge proposal.toNat u.slot.toNat with earlier | atLeast
      · exact earlier
      · have equal : proposal = u.slot := UInt64.toNat_inj.mp (by omega)
        exact absurd (equal ▸ member) proposed
    exact flags slot epoch ⟨proposal, member, after', earlier, within⟩

/-- At the last slot of the epoch, the walk has gathered the votes of every other slot.

Each such slot has a proposal after it in the epoch, so before the end of the walk. -/
private theorem votesGathered_of_last {fork : Fork} {start v : BeaconState preset fork}
    {honest : Finset ValidatorIndex} {proposals : Set Slot} {gap : Nat}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (altair : .altair ≤ fork)
    (covered : ∀ slot : Slot, computeEpochAtSlot preset slot = getCurrentEpoch start →
      (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 →
      ∃ proposal ∈ proposals, slot < proposal ∧
        computeEpochAtSlot preset proposal = getCurrentEpoch start ∧
        proposal.toNat ≤ slot.toNat + gap)
    (kept : EpochKept honest gap proposals altair start v (v.slot.toNat + 1))
    (last : (v.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0) :
    VotesGathered honest v := by
  obtain ⟨same, runKept, -, -, flags⟩ := kept
  obtain ⟨committees, count⟩ := committees_of_runKept apart runKept same
  intro _ slot epoch notLast index members inside committee voter mem good
  rw [same] at epoch inside
  rw [count] at inside
  rw [committees slot index epoch] at committee
  obtain ⟨proposal, member, after, inEpoch, gapped⟩ := covered slot epoch notLast
  -- The proposal is in the epoch of the last slot, so it is at most that slot.
  have epochNat : proposal.toNat / preset.SLOTS_PER_EPOCH.toNat =
      v.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    have := congrArg UInt64.toNat (inEpoch.trans same.symm)
    rw [getCurrentEpoch_toNat] at this
    exact (UInt64.toNat_div _ _).symm.trans this
  exact flags slot epoch ⟨proposal, member, after, lt_succ_of_same_epoch positive epochNat last,
    gapped⟩ index members inside committee voter mem good

/-- Honest blocks and slot steps walk from a state of the epoch to its last slot.

At each slot the walk applies the honest block of a proposal, if there is one.

It then takes a slot step, unless the slot is the last of the epoch.

The induction counts the slots left after the current one in the epoch. -/
private theorem exists_epochWalk {fork : Fork}
    {start : BeaconState preset fork}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {proposals : Set Slot} {gap : Nat}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (altair : .altair ≤ fork)
    (slots : ∀ (w : ForkedBeaconState preset) (run : Run config checks ⟨fork, start⟩ w),
      run.Honest config honest key → run.BlocksAt proposals →
      getCurrentEpoch w.state = getCurrentEpoch start →
        ∃ next, advanceSlotAcross config checks w = .ok next)
    (covered : ∀ slot : Slot, computeEpochAtSlot preset slot = getCurrentEpoch start →
      (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 →
      ∃ proposal ∈ proposals, slot < proposal ∧
        computeEpochAtSlot preset proposal = getCurrentEpoch start ∧
        proposal.toNat ≤ slot.toNat + gap)
    (propose : ∀ {fork' : Fork} (w : BeaconState preset fork')
      (run : Run config checks ⟨fork, start⟩ ⟨fork', w⟩),
      run.Honest config honest key → run.BlocksAt proposals →
      getCurrentEpoch w = getCurrentEpoch start →
      w.slot ∈ proposals → w.latestBlockHeader.slot < w.slot →
      ∃ (after : BeaconState preset fork') (engine : ExecutionEngine preset fork')
        (signed : SignedBeaconBlock preset fork') (due : upgradeDue config ⟨fork', w⟩ = false)
        (ok : applySignedBlock config checks engine w signed true = .ok after),
        (Step.block engine signed due ok).Honest config honest key ∧
          GathersVotes honest gap w after) (n : Nat) :
    ∀ (u : BeaconState preset fork) (run : Run config checks ⟨fork, start⟩ ⟨fork, u⟩),
      run.Honest config honest key → run.BlocksAt proposals →
      EpochKept honest gap proposals altair start u u.slot.toNat →
      u.latestBlockHeader.slot < u.slot →
      preset.SLOTS_PER_EPOCH.toNat * ((getCurrentEpoch start).toNat + 1) -
        (u.slot.toNat + 1) = n →
      ∃ (v : BeaconState preset fork) (walked : Run config checks ⟨fork, start⟩ ⟨fork, v⟩),
        walked.Honest config honest key ∧ walked.BlocksAt proposals ∧
        getCurrentEpoch v = getCurrentEpoch start ∧
        (v.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
        v.latestBlockHeader.slot ≤ v.slot ∧
        v.currentJustifiedCheckpoint = start.currentJustifiedCheckpoint ∧
        v.justificationBits = start.justificationBits ∧
        VotesGathered honest v := by
  induction n with
  | zero =>
    intro u run honestRun blocksRun kept fresh left
    obtain ⟨v, walked, honestWalked, blocksWalked, slotEq, behind, keptV⟩ :=
      exists_blockPhase apart altair propose run honestRun blocksRun kept fresh
    rw [← slotEq] at keptV left
    -- No slot is left after this one, so it is the last slot of the epoch.
    have epochNat := congrArg UInt64.toNat keptV.1
    rw [getCurrentEpoch_toNat] at epochNat
    have below := Nat.lt_mul_div_succ v.slot.toNat positive
    rw [epochNat] at below
    have last : (v.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      rw [show v.slot.toNat + 1 =
          preset.SLOTS_PER_EPOCH.toNat * ((getCurrentEpoch start).toNat + 1) by omega,
        Nat.mul_mod_right]
    exact ⟨v, walked, honestWalked, blocksWalked, keptV.1, last, behind, keptV.2.2.1,
      keptV.2.2.2.1, votesGathered_of_last positive apart altair covered keptV last⟩
  | succ n ih =>
    intro u run honestRun blocksRun kept fresh left
    obtain ⟨v, walked, honestWalked, blocksWalked, slotEq, behind, keptV⟩ :=
      exists_blockPhase apart altair propose run honestRun blocksRun kept fresh
    rw [← slotEq] at keptV left
    by_cases last : (v.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0
    · exact ⟨v, walked, honestWalked, blocksWalked, keptV.1, last, behind, keptV.2.2.1,
        keptV.2.2.2.1, votesGathered_of_last positive apart altair covered keptV last⟩
    -- Away from the last slot, the slot step stays in the epoch and keeps the walk.
    obtain ⟨next, ok⟩ := slots ⟨fork, v⟩ walked honestWalked blocksWalked keptV.1
    obtain ⟨after, rfl, moved, runStep, participation, justified, bits, header⟩ :=
      slotStep_inside ok last
    have epochAfter : getCurrentEpoch after = getCurrentEpoch start := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat, moved, succ_div_cases.2 last, ← getCurrentEpoch_toNat, keptV.1]
    refine ih after (walked.snoc (.slot ok)) (honestWalked.snoc (step := .slot ok) trivial)
      (blocksWalked.snoc (step := .slot ok) trivial)
      ⟨epochAfter, keptV.2.1.trans runStep, justified.trans keptV.2.2.1,
        bits.trans keptV.2.2.2.1, ?_⟩ ?_ (by rw [moved]; omega)
    · intro slot epoch proposed
      rw [moved] at proposed
      rw [participation]
      exact keptV.2.2.2.2 slot epoch proposed
    · rw [header, UInt64.lt_iff_toNat_lt, moved]
      have := UInt64.le_iff_toNat_le.mp behind
      omega

/-! ## The continuation -/

/-- Honest slot steps lead from a state to the first slot of the next epoch.

The latest block header of the first state must be at its slot or before.

The run has no block, so it is honest for any honest set.

The state it reaches has a slot after its latest block header.

Each slot step from a state of the epoch, reached by slot steps only, must succeed. -/
theorem exists_slotsContinuation {s : ForkedBeaconState preset}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (behind : s.state.latestBlockHeader.slot ≤ s.state.slot)
    (slots : ∀ (w : ForkedBeaconState preset) (run : Run config checks s w),
      run.blockCount = 0 → getCurrentEpoch w.state = getCurrentEpoch s.state →
        ∃ next, advanceSlotAcross config checks w = .ok next) :
    ∃ (z : ForkedBeaconState preset) (run : Run config checks s z),
      run.Honest config honest key ∧ run.blockCount = 0 ∧
      (getCurrentEpoch z.state).toNat = (getCurrentEpoch s.state).toNat + 1 ∧
      z.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
      z.state.latestBlockHeader.slot < z.state.slot :=
  exists_slotsWalk positive slots _ s .nil Run.Honest.nil rfl rfl behind rfl

/-- An honest continuation through an epoch gathers the target votes of all its slots but the last.

The continuation starts at the first slot of the epoch, from Altair.

The ring of RANDAO mixes spans more than the seed lookahead plus two epochs.

Its first state has a slot after its latest block header.

The conditions below read the states that honest runs from the first state reach in the epoch.

Those runs apply blocks only at the slots of the proposals.

Each slot step from such a state must succeed, also the step out of the last slot.

Each slot of the epoch but the last must have a slot of a proposal after it in the epoch.

That slot must be within the gap.

With two slots or more in an epoch, the last slot is then a slot of a proposal.

At each slot of a proposal, an honest block must pass from such a state.

That block must gather the votes of the slots shortly before it.

The run then reaches the last slot of the epoch, at the same fork, with those votes gathered.

Its latest block header is at that slot or before.

It keeps the current justified checkpoint and the bits of justification. -/
theorem exists_epochContinuation {s : ForkedBeaconState preset}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {proposals : Set Slot} {gap : Nat}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (altair : .altair ≤ s.fork)
    (first : s.state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0)
    (fresh : s.state.latestBlockHeader.slot < s.state.slot)
    (slots : ∀ (w : ForkedBeaconState preset) (run : Run config checks s w),
      run.Honest config honest key → run.BlocksAt proposals →
      getCurrentEpoch w.state = getCurrentEpoch s.state →
        ∃ next, advanceSlotAcross config checks w = .ok next)
    (covered : ∀ slot : Slot, computeEpochAtSlot preset slot = getCurrentEpoch s.state →
      (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 →
      ∃ proposal ∈ proposals, slot < proposal ∧
        computeEpochAtSlot preset proposal = getCurrentEpoch s.state ∧
        proposal.toNat ≤ slot.toNat + gap)
    (propose : ∀ {fork : Fork} (w : BeaconState preset fork) (run : Run config checks s ⟨fork, w⟩),
      run.Honest config honest key → run.BlocksAt proposals →
      getCurrentEpoch w = getCurrentEpoch s.state →
      w.slot ∈ proposals → w.latestBlockHeader.slot < w.slot →
      ∃ (after : BeaconState preset fork) (engine : ExecutionEngine preset fork)
        (signed : SignedBeaconBlock preset fork) (due : upgradeDue config ⟨fork, w⟩ = false)
        (ok : applySignedBlock config checks engine w signed true = .ok after),
        (Step.block engine signed due ok).Honest config honest key ∧
          GathersVotes honest gap w after) :
    ∃ (z : ForkedBeaconState preset) (run : Run config checks s z),
      run.Honest config honest key ∧ run.BlocksAt proposals ∧ z.fork = s.fork ∧
      getCurrentEpoch z.state = getCurrentEpoch s.state ∧
      (z.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
      z.state.latestBlockHeader.slot ≤ z.state.slot ∧
      z.state.currentJustifiedCheckpoint = s.state.currentJustifiedCheckpoint ∧
      z.state.justificationBits = s.state.justificationBits ∧
      VotesGathered honest z.state := by
  obtain ⟨fork, start⟩ := s
  dsimp only at *
  -- At the first slot of the epoch no slot of the epoch is before, so no flag is owed yet.
  have initial : EpochKept honest gap proposals altair start start start.slot.toNat := by
    refine ⟨rfl, RunKept.refl start, rfl, rfl, ?_⟩
    intro slot epoch ⟨proposal, _, after, below, _⟩
    exfalso
    have epochNat : slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        start.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      have := congrArg UInt64.toNat epoch
      rw [getCurrentEpoch_toNat] at this
      exact (UInt64.toNat_div _ _).symm.trans this
    have low := Nat.div_mul_le_self slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have split := Nat.div_add_mod start.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [first, ← epochNat, Nat.mul_comm] at split
    have := UInt64.lt_iff_toNat_lt.mp after
    omega
  obtain ⟨v, walked, honestWalked, blocksWalked, same, last, behind, justified, bits, gathered⟩ :=
    exists_epochWalk positive apart altair slots covered propose _ start
      .nil Run.Honest.nil Run.BlocksAt.nil initial fresh rfl
  exact ⟨⟨fork, v⟩, walked, honestWalked, blocksWalked, rfl, same, last, behind, justified, bits,
    gathered⟩

end EthLib.Consensus
