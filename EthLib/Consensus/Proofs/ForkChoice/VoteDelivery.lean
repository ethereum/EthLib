module

public import EthLib.Consensus.Proofs.ForkChoiceNetworkModel
public import EthLib.Consensus.Proofs.ForkChoice.VoteRecords
public import EthLib.Consensus.Proofs.Time
public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Conditional delivery of accepted votes

Under synchrony, an honest receiver sees an honest vote one delay after it was sent.

An up-to-date receiver that accepts the attestation records its signer's vote.

The receiver retains a vote of at least that rank at every later event.

Acceptance and agreement on the indexed attestation are explicit hypotheses.

The network model and voting time follow [arXiv 2405.00549v4, Sections 2 and 3.1][fcr].

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork}
variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A duty vote names the head used by its voter and a block no later than its duty slot. -/
theorem VoteAt.data_head {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (start : ∀ u ∈ J, e.start u = anchor) {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot}
    {committeeIndex : CommitteeIndex} {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) {due : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok due) (inSlot : due < config.SLOT_DURATION_MS) :
    attestation.data.slot = slot ∧
      attestation.data.target.epoch = computeEpochAtSlot preset slot ∧
      ∃ head block, ((e.world n).state v).getHead config = .ok head ∧
        ((e.world n).state v).blocks[head.root]? = some block ∧
        attestation.data.beaconBlockRoot = head.root ∧ block.slot ≤ slot := by
  obtain ⟨startTime, due', startOk, dueOk', timeEq⟩ := deadline
  rw [dueOk, Except.ok.injEq] at dueOk'
  subst due'
  have current : ((e.world n).state v).getCurrentSlot config = .ok slot := by
    unfold Store.getCurrentSlot
    rw [vote.genesis]
    exact mapError_ok_iff.mpr (computeSlotAtTimeMs_inside startOk
      (vote.upToDate.1.trans timeEq) inSlot)
  have forward := e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) n v honest
  have positive : 0 < config.SLOT_DURATION_MS := by
    have := UInt64.lt_iff_toNat_lt.mp inSlot
    exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
  obtain ⟨currentSlot, currentOk, blocks, states⟩ :=
    forward.slots_le_current positive anchorSlot
  rw [current, Except.ok.injEq] at currentOk
  subst currentSlot
  obtain ⟨head, block, headState, state, headOk, known, stateOk, advanced, made⟩ :=
    vote.honestData
  have stateBound : headState.slot ≤ slot :=
    states head.root headState (Store.blockState_ok_iff.mp stateOk)
  have atSlot : state.slot = slot := by
    unfold lookaheadState at advanced
    split at advanced
    · exact (processSlots_slot (mapError_ok_iff.mp advanced)).2
    · simp only [pure, Except.pure, Except.ok.injEq] at advanced
      subst state
      exact UInt64.le_antisymm stateBound (UInt64.not_lt.mp ‹¬ headState.slot < slot›)
  obtain ⟨-, -, dataSlot, dataRoot, -, epoch⟩ := getAttestationData_eq_ok_iff.mp made
  exact ⟨dataSlot.trans atSlot, by simpa [getCurrentEpoch, atSlot] using epoch,
    head, block, headOk, known, dataRoot, blocks head.root block known⟩

/-- An honest vote names the checkpoint obtained by walking its voter's head. -/
theorem HonestVoteData.target_read {store other : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    -- The anchor starts at an epoch boundary.
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    -- Nonzero state roots prevent repeated header filling.
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {slot : Slot} {committeeIndex : CommitteeIndex} {data : AttestationData}
    (made : HonestVoteData config checks store slot committeeIndex data)
    -- Some store reachable from the same anchor must hold the target block.
    --
    -- The anchor store does not tie the anchor state's latest header to the anchor block.
    --
    -- So a target read from lookahead at the anchor names the anchor only when that block is held.
    (holder : Store.Reachable config anchorState anchorBlock other)
    {targetBlock : BeaconBlock preset fork}
    (known : other.blocks[data.target.root]? = some targetBlock) :
    ∃ head, store.getHead config = .ok head ∧
      store.getCheckpointBlock head.root data.target.epoch = .ok data.target.root := by
  obtain ⟨head, block, headState, state, headOk, found, stored, advanced, dataOk⟩ := made
  refine ⟨head, headOk, ?_⟩
  have stored' := Store.blockState_ok_iff.mp stored
  obtain ⟨-, boundary, -, -, -, epoch⟩ := getAttestationData_eq_ok_iff.mp dataOk
  have headLe : block.slot ≤ state.slot := by
    have le := Store.Reachable.slot_le_of_blockState
      (UInt64.le_of_eq anchorSlot) reachable found stored'
    unfold lookaheadState at advanced
    split at advanced
    · exact UInt64.le_trans le (UInt64.le_of_lt (by
        have bounds := processSlots_slot (mapError_ok_iff.mp advanced)
        exact bounds.2 ▸ bounds.1))
    · simp only [pure, Except.pure, Except.ok.injEq] at advanced
      subst state
      exact le
  have anchorLe : anchorState.slot ≤ state.slot := by
    have le := reachable.anchorSlot_le_of_blockState stored'
    unfold lookaheadState at advanced
    split at advanced
    · have bounds := processSlots_slot (mapError_ok_iff.mp advanced)
      rw [bounds.2]
      exact UInt64.le_trans le (UInt64.le_of_lt bounds.1)
    · simp only [pure, Except.pure, Except.ok.injEq] at advanced
      subst state
      exact le
  let first := state.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH
  have firstOk : computeStartSlotAtEpoch preset data.target.epoch = .ok first := by
    rw [epoch]
    exact computeStartSlotAtEpoch_computeEpochAtSlot state.slot
  unfold Store.getCheckpointBlock
  rw [firstOk]
  simp only [Except.mapError, bind, Except.bind]
  change (·.root) <$> store.getAncestor ⟨head.root, .pending⟩ first = _
  rcases getEpochBoundaryBlockRoot_eq_ok_iff.mp boundary with ⟨onBoundary, targetEq⟩ | ⟨-, read⟩
  · have eq : first = state.slot := div_mul_eq_self_iff.mpr onBoundary
    rw [eq, Store.getAncestor_of_le (node := ⟨head.root, .pending⟩) found headLe]
    simp [targetEq]
  · have read' : getBlockRootAtSlot state first = .ok data.target.root := by
      unfold getBlockRoot at read
      rw [← epoch, firstOk] at read
      exact read
    have firstAfter : anchorState.slot ≤ first :=
      le_computeStartSlotAtEpoch_of_isStartSlotAtEpoch
        (by rw [← anchorSlot]; exact anchorAtBoundary) anchorLe
        (computeStartSlotAtEpoch_computeEpochAtSlot state.slot)
    exact reachable.lookahead_history_ancestor_of_held (UInt64.le_of_eq anchorSlot) nonzero
      holder stored' known advanced read' firstAfter .pending

/-- An honest duty vote names the checkpoint obtained by walking its voted head.

The anchor starts at an epoch boundary; nonzero state roots prevent repeated header filling. -/
theorem VoteAt.data_target {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ u ∈ J, e.start u = anchor) {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot}
    {committeeIndex : CommitteeIndex} {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world n).state v).blocks[root]? = some block →
        block.stateRoot ≠ Vector.replicate 32 0) :
    ((e.world n).state v).getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root := by
  have reachable := e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) n v honest
  -- The voter reads its own attestation, so it holds the target block.
  have known : ∃ targetBlock,
      ((e.world n).state v).blocks[attestation.data.target.root]? = some targetBlock := by
    obtain ⟨withTarget, targetState, storing, reading, -⟩ := vote.reads
    unfold Store.storeTargetCheckpointState at storing
    split at storing
    · simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst withTarget
      obtain ⟨base, _, held, -⟩ := reachable.checkpointStatesFromBlocks
        (Store.checkpointState_ok_iff.mp reading)
      exact reachable.known_of_blockState held
    · simp only [bind_ok_iff] at storing
      obtain ⟨computedState, computed, -⟩ := storing
      unfold Store.computeCheckpointState at computed
      simp only [bind_ok_iff] at computed
      obtain ⟨base, held, -⟩ := computed
      exact reachable.known_of_blockState (Store.blockState_ok_iff.mp held)
  obtain ⟨targetBlock, targetKnown⟩ := known
  obtain ⟨head, headOk, read⟩ := vote.honestData.target_read reachable anchorSlot
    anchorAtBoundary nonzero reachable targetKnown
  -- The vote names the same head.
  obtain ⟨head', _, _, _, headOk', -, -, -, made⟩ := vote.honestData
  rw [headOk, Except.ok.injEq] at headOk'
  subst head'
  rw [(getAttestationData_eq_ok_iff.mp made).2.2.2.1]
  exact read

/-- Processing through a time supplies processing through every earlier time. -/
theorem Prompt.of_le {last later : ℕ} (prompt : Prompt e later) (le : last ≤ later) :
    Prompt e last :=
  fun w honest slot start startOk started bounded =>
    prompt w honest slot start startOk started (bounded.trans le)

/-- A fitting delay leaves time to process a duty vote before the next slot boundary. -/
theorem DelayFits.before_boundary {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot next : Slot} {start following : UInt64} {time : ℕ}
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) :
    time + Δ < following.toNat := by
  obtain ⟨start', due, startOk', dueOk, timeEq⟩ := deadline
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  rw [timeEq]
  exact fits.2 slot next start due following nextOk startOk dueOk followingOk

/-- The start of a later slot is more than one delay after the start of an earlier slot. -/
theorem DelayFits.start_add_lt_of_lt {Δ : ℕ} (slots : 0 < config.SLOT_DURATION_MS)
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot current : Slot} {begin currentBegin : UInt64} (later : slot < current)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (currentOk : computeTimeAtSlotMs config genesisTimeMs current = .ok currentBegin) :
    begin.toNat + Δ < currentBegin.toNat := by
  obtain ⟨nextOk, following, followingOk, followingLe⟩ := nextSlotStart_le_of_slotAtTime
    (computeSlotAtTimeMs_computeTimeAtSlotMs slots currentOk) later
  obtain ⟨due, dueOk⟩ := fits.1
  have fit := fits.2 slot (slot + 1) begin due following nextOk beginOk dueOk followingOk
  omega

/-- A past slot's attestation deadline plus the delay is at most the current clock.

The slot after the deadline's starts at or before the clock.

A fitting delay puts the deadline plus the delay before the start of that slot. -/
theorem DelayFits.deadline_add_le {Δ time : ℕ} {slot current : Slot} {clock : UInt64}
    (fits : DelayFits fork config genesisTimeMs Δ)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time)
    (currentOk : computeSlotAtTimeMs config genesisTimeMs clock = .ok current)
    (past : slot < current) : time + Δ ≤ clock.toNat := by
  have ⟨start, _, startOk, _, _⟩ := deadline
  obtain ⟨nextOk, following, followingOk, followingLe⟩ :=
    nextSlotStart_le_of_slotAtTime currentOk past
  have before := fits.before_boundary nextOk startOk followingOk deadline
  omega

/-- A fitting delay places the attestation deadline inside each representable slot. -/
theorem DelayFits.due_lt_slot {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot next : Slot} {start following due : UInt64}
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (dueOk : getAttestationDueMs config fork = .ok due) :
    due < config.SLOT_DURATION_MS := by
  have before := fits.2 slot next start due following nextOk startOk dueOk followingOk
  obtain ⟨start', startOk', startNat, _⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_refl slot) startOk
  obtain ⟨following', followingOk', followingNat, _⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_refl next) followingOk
  rw [startOk, Except.ok.injEq] at startOk'
  rw [followingOk, Except.ok.injEq] at followingOk'
  subst start'
  subst following'
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  rw [nextNat, Nat.add_mul, Nat.one_mul] at followingNat
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-- Honest stores at ordered times have ordered current slots.

The later store must be up to date. -/
theorem Execution.currentSlot_le_of_time_le {anchor : Store preset fork}
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w : ValidatorIndex} (callerHonest : u ∈ J) (receiverHonest : w ∈ J) {n k : Nat}
    (later : (e.world n).time ≤ (e.world k).time)
    (updated : UpToDate config checks sources (e.world k).time
      ((e.world k).view w) ((e.world k).state w))
    {slot current : Slot}
    (callerSlot : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (receiverSlot : ((e.world k).state w).getCurrentSlot config = .ok current) :
    slot ≤ current := by
  have callerClock := e.clock_bounds u n
  have receiverClock := e.clock_bounds w k
  rw [anchored u callerHonest] at callerClock
  rw [anchored w receiverHonest] at receiverClock
  have clockLe : ((e.world n).state u).timeMs ≤ ((e.world k).state w).timeMs := by
    have initial := UInt64.le_iff_toNat_le.mp receiverClock.2.1
    have now := updated.1
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have callerRead := mapError_ok_iff.mp callerSlot
  have receiverRead := mapError_ok_iff.mp receiverSlot
  change computeSlotAtTimeMs config _ _ = .ok slot at callerRead
  change computeSlotAtTimeMs config _ _ = .ok current at receiverRead
  rw [callerClock.1] at callerRead
  rw [receiverClock.1] at receiverRead
  exact computeSlotAtTimeMs_mono clockLe callerRead receiverRead

/-- Honest stores at ordered times have ordered predecessor slots. -/
theorem Execution.previousSlot_le_of_time_le {anchor : Store preset fork}
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w : ValidatorIndex} (callerHonest : u ∈ J) (receiverHonest : w ∈ J) {n k : Nat}
    (later : (e.world n).time ≤ (e.world k).time)
    (updated : UpToDate config checks sources (e.world k).time
      ((e.world k).view w) ((e.world k).state w))
    {slot current oldLast last : Slot}
    (callerSlot : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (receiverSlot : ((e.world k).state w).getCurrentSlot config = .ok current)
    (callerLast : subChecked slot 1 = .ok oldLast)
    (receiverLast : subChecked current 1 = .ok last) : oldLast ≤ last := by
  have slots := e.currentSlot_le_of_time_le anchored callerHonest receiverHonest later updated
    callerSlot receiverSlot
  have := (subChecked_ok_iff.mp callerLast).2
  have := (subChecked_ok_iff.mp receiverLast).2
  have := UInt64.le_iff_toNat_le.mp slots
  exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- Prompt processing supplies both receiver events around a duty's next slot boundary. -/
theorem Execution.exists_duty_boundaries {Δ : ℕ}
    {slot next : Slot} {start following : UInt64} {time : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e following.toNat)
    {w : ValidatorIndex} (receiver : w ∈ J)
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time)
    (started : e.startTime ≤ time) :
    (∃ k, (e.world k).time + 1 = following.toNat ∧
      time + Δ ≤ (e.world k).time ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w)) ∧
    (∃ k, (e.world k).time = following.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w)) := by
  have before := fits.before_boundary nextOk startOk followingOk deadline
  have startedBefore : e.startTime < following.toNat := by omega
  obtain ⟨boundary, preboundary⟩ :=
    prompt w receiver next following followingOk startedBefore.le (Nat.le_refl _)
  obtain ⟨k, atTime, current⟩ := preboundary startedBefore
  exact ⟨⟨k, atTime, by omega, current⟩, boundary⟩

/-- Every honest store runs on the genesis time of any one honest store.

All honest stores start from the same anchor, and no move changes the genesis time. -/
theorem Execution.genesisTimeMs_eq_of_honest {anchor : Store preset fork}
    (start : ∀ u ∈ J, e.start u = anchor)
    {v : ValidatorIndex} (honest : v ∈ J) {i : ℕ}
    (genesis : ((e.world i).state v).genesisTimeMs = genesisTimeMs)
    {w : ValidatorIndex} (receiver : w ∈ J) :
    ∀ j, ((e.world j).state w).genesisTimeMs = genesisTimeMs := by
  intro j
  have left := (e.clock_bounds v i).1
  have right := (e.clock_bounds w j).1
  rw [start v honest] at left
  rw [start w receiver] at right
  exact right.trans (left.symm.trans genesis)

/-- A store that is up to date at the start of a slot is at that slot.

It must run on the genesis time of the slot's start, and a slot must have a duration. -/
theorem Execution.getCurrentSlot_of_slot_start (slots : 0 < config.SLOT_DURATION_MS)
    {w : ValidatorIndex} {j : ℕ} {slot : Slot} {begin : UInt64}
    (genesis : ((e.world j).state w).genesisTimeMs = genesisTimeMs)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atTime : (e.world j).time = begin.toNat)
    (upToDate : UpToDate config checks sources (e.world j).time ((e.world j).view w)
      ((e.world j).state w)) :
    ((e.world j).state w).getCurrentSlot config = .ok slot := by
  unfold Store.getCurrentSlot
  rw [genesis]
  have clock : ((e.world j).state w).timeMs = begin := UInt64.toNat_inj.mp (upToDate.1.trans atTime)
  rw [clock]
  exact mapError_ok_iff.mpr (computeSlotAtTimeMs_computeTimeAtSlotMs slots beginOk)

/-- A duty inside a complete slot interval has a valid committee vote before the delivery cutoff.

Each vote it assumes also passes the committee check in its target state. -/
theorem Execution.exists_voteAt_of_duty_interval {Δ : ℕ} {first time : ℕ}
    {begin last slot : Slot}
    (votes : VotesInSlots e begin last)
    (fits : DelayFits fork config genesisTimeMs Δ)
    {beginTime endTime : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endOk : computeTimeAtSlotMs config genesisTimeMs last = .ok endTime)
    (started : e.startTime ≤ first) (fresh : first ≤ beginTime.toNat)
    (complete : endTime.toNat ≤ time)
    {v : ValidatorIndex} (honest : v ∈ J) {committeeIndex : CommitteeIndex}
    (afterBegin : begin ≤ slot) (beforeEnd : slot < last)
    (duty : assignment.committee v slot = some committeeIndex) :
    ∃ next start following deadline n attestation indexed,
      addChecked slot 1 = .ok next ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧
      computeTimeAtSlotMs config genesisTimeMs next = .ok following ∧
      IsAttestationDeadline fork config genesisTimeMs slot deadline ∧
      first ≤ deadline ∧ deadline + Δ < following.toNat ∧ following.toNat ≤ time ∧
      VoteAt e v slot committeeIndex deadline n attestation indexed ∧
      VoteCommittees (config := config) (checks := checks)
        ((e.world n).state v) attestation := by
  have slotLt := UInt64.lt_iff_toNat_lt.mp beforeEnd
  have lastBound := last.toNat_lt
  have nextBound : slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by simp; omega
  have nextOk := addChecked_of_lt nextBound
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have nextLe : slot + 1 ≤ last := UInt64.le_iff_toNat_le.mpr (by
    simp only [UInt64.toNat_one] at nextNat; omega)
  obtain ⟨startTime, startOk, startNat, _⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt beforeEnd) endOk
  obtain ⟨following, followingOk, _, followingLe⟩ :=
    exists_timeAtSlotMs_of_le nextLe endOk
  obtain ⟨beginTime', beginOk', _, beginLe⟩ := exists_timeAtSlotMs_of_le afterBegin startOk
  rw [beginOk, Except.ok.injEq] at beginOk'
  subst beginTime'
  obtain ⟨due, dueOk⟩ := fits.1
  have deadline : IsAttestationDeadline fork config genesisTimeMs slot
      (startTime.toNat + due.toNat) := ⟨startTime, due, startOk, dueOk, rfl⟩
  have beginLe := UInt64.le_iff_toNat_le.mp beginLe
  have followingLe := UInt64.le_iff_toNat_le.mp followingLe
  have firstLe : first ≤ startTime.toNat + due.toNat := by omega
  obtain ⟨n, attestation, indexed, vote, committees⟩ :=
    votes v honest slot committeeIndex _ afterBegin beforeEnd duty deadline
      (started.trans firstLe)
  exact ⟨slot + 1, startTime, following, _, n, attestation, indexed,
    nextOk, startOk, followingOk, deadline, firstLe,
    fits.before_boundary nextOk startOk followingOk deadline, by omega, vote, committees⟩

/-- An accepted attestation stores its target state and records the votes of its indexed form.

The store that holds the target state is the one that the reads of the attestation name. -/
theorem Store.onAttestation_eq_of_reads {store after : Store preset fork}
    {attestation : Attestation preset fork} {isFromBlock : Bool}
    {indexed : IndexedAttestation preset fork}
    (accepted : store.onAttestation config checks attestation isFromBlock = .ok after)
    (reads : ReadsAttestation config checks store attestation indexed) :
    ∃ withTarget, store.storeTargetCheckpointState config checks attestation.data.target =
        .ok withTarget ∧
      after = withTarget.updateLatestMessages indexed.attestingIndices.data.toList attestation := by
  obtain ⟨withTarget, targetState, stored, found, indexedOk, signed⟩ := reads
  refine ⟨withTarget, stored, ?_⟩
  unfold Store.onAttestation at accepted
  cases valid : store.validateOnAttestation config attestation isFromBlock with
  | error err => simp [valid, bind, Except.bind] at accepted
  | ok value =>
    cases value
    simp only [valid, stored, found, indexedOk, signed, bind, Except.bind, Except.mapError,
      ↓reduceIte] at accepted
    cases committees : checkAttestationCommittees targetState attestation <;>
      simp_all [pure, Except.pure]

/-- An up-to-date store holds a vote for each non-equivocating signer of an accepted attestation.

The attestation is in its view, and the latest vote has at least the attestation's rank. -/
theorem UpToDate.recorded {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork}
    (upToDate : UpToDate config checks sources time view store)
    {attestation : Attestation preset fork} (seen : .attestation attestation ∈ view)
    (accepted : store.onAttestation config checks attestation false = .ok after)
    {indexed : IndexedAttestation preset fork}
    (reads : ReadsAttestation config checks store attestation indexed) {v : ValidatorIndex}
    (voter : v ∈ indexed.attestingIndices.data.toList) (counted : v ∉ store.equivocatingIndices) :
    ∃ m, store.latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  have fixed : after = store := upToDate.2 after (.attestation seen accepted)
  obtain ⟨withTarget, -, result⟩ := Store.onAttestation_eq_of_reads accepted reads
  have counted' : v ∉ withTarget.equivocatingIndices := by
    simpa [← fixed, result, Store.updateLatestMessages] using counted
  have voted := Store.foldl_recordVote indexed.attestingIndices.data.toList
    withTarget.latestMessages voter counted' (message := LatestMessage.ofAttestation attestation)
  simpa [← fixed, result, Store.updateLatestMessages] using voted

/-- Under synchrony, an up-to-date honest receiver that accepts an honest vote records its signer.

The receiver reads the same indexed attestation and does not count the signer as an equivocator.

Its latest vote has at least the honest vote's rank. -/
theorem VoteAt.recorded {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex} {time n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    {after : Store preset fork}
    -- Synchrony alone does not establish handler success, so acceptance is a hypothesis.
    (accepted : ((e.world k).state u).onAttestation config checks attestation false = .ok after)
    (reads : ReadsAttestation config checks ((e.world k).state u) attestation indexed)
    (counted : v ∉ ((e.world k).state u).equivocatingIndices) :
    ∃ m, ((e.world k).state u).latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  have seen := e.mem_view_of_send sync vote.sends honest receiver
    (by simpa [vote.atTime] using late)
  exact upToDate.recorded seen accepted reads (by simp [vote.alone]) counted

/-- A receiver that records an honest vote retains a vote of at least that rank at later events.

The acceptance hypotheses apply at event `k`. -/
theorem VoteAt.recorded_of_le {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex}
    (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex}
    {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    {after : Store preset fork}
    (accepted : ((e.world k).state u).onAttestation config checks attestation false = .ok after)
    (reads : ReadsAttestation config checks ((e.world k).state u) attestation indexed)
    (counted : v ∉ ((e.world k).state u).equivocatingIndices) {later : ℕ} (le : k ≤ later) :
    ∃ m, ((e.world later).state u).latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  obtain ⟨m, found, rank⟩ := vote.recorded sync honest receiver late upToDate accepted reads counted
  obtain ⟨last, kept, grew⟩ := Execution.latestMessages_rank e le found
  exact ⟨last, kept, UInt64.le_trans rank grew⟩

/-- A duty's epoch is current or previous at the next slot. -/
private theorem epoch_recent_at_next_slot {slot next : Slot}
    (nextOk : addChecked slot 1 = .ok next) :
    computeEpochAtSlot preset slot = computeEpochAtSlot preset next ∨
      computeEpochAtSlot preset slot = saturatingSub (computeEpochAtSlot preset next) 1 := by
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  simp only [UInt64.toNat_one] at nextNat
  have quotient : (slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat +
        if preset.SLOTS_PER_EPOCH.toNat ∣ slot.toNat + 1 then 1 else 0 := Nat.succ_div
  by_cases same : computeEpochAtSlot preset slot = computeEpochAtSlot preset next
  · exact Or.inl same
  · right
    have different : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≠
        next.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      intro eq
      exact same (UInt64.toNat_inj.mp (by simpa [computeEpochAtSlot] using eq))
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [nextNat]
      rw [nextNat] at different
      split at quotient <;> omega
    apply UInt64.toNat_inj.mp
    simp only [computeEpochAtSlot, saturatingSub]
    by_cases h : (1 : UInt64) < next / preset.SLOTS_PER_EPOCH
    · simp only [h, ite_true]
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)]
      simp only [UInt64.toNat_div, UInt64.toNat_one]
      rw [step]
      exact (Nat.add_sub_cancel _ _).symm
    · simp only [h, ite_false, UInt64.toNat_zero, UInt64.toNat_div]
      have : (next / preset.SLOTS_PER_EPOCH).toNat ≤ 1 := by
        simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_one, not_lt] using h
      simp only [UInt64.toNat_div] at this
      rw [step] at this
      exact Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_right this)

open EthLib.Consensus.Store in
/-- Known blocks, a recent target and a past slot discharge the wire attestation checks. -/
private theorem validateOnAttestation_of_facts {store : Store preset fork}
    {attestation : Attestation preset fork} {target voted : BeaconBlock preset fork}
    {current : Slot} (currentOk : store.getCurrentSlot config = .ok current)
    (recent : attestation.data.target.epoch = computeEpochAtSlot preset current ∨
      attestation.data.target.epoch = saturatingSub (computeEpochAtSlot preset current) 1)
    (epoch : attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot)
    (targetKnown : store.blocks[attestation.data.target.root]? = some target)
    (votedKnown : store.blocks[attestation.data.beaconBlockRoot]? = some voted)
    (notFuture : voted.slot ≤ attestation.data.slot)
    (payload : ∀ gloas : .glamsterdam ≤ fork,
      store.validatePayloadVote gloas attestation voted = .ok ())
    (checkpoint : store.getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root)
    (past : attestation.data.slot < current) :
    store.validateOnAttestation config attestation false = .ok () := by
  have slotBound : attestation.data.slot.toNat + 1 < 2 ^ 64 := by
    have := current.toNat_lt
    have := UInt64.lt_iff_toNat_lt.mp past
    omega
  have dueOk := addChecked_of_lt (a := attestation.data.slot) (b := 1)
    (by simpa using slotBound)
  have dueBound : ¬ current < attestation.data.slot + 1 := by
    rw [UInt64.lt_iff_toNat_lt, toNat_add_of_lt (by simpa using slotBound)]
    have := UInt64.lt_iff_toNat_lt.mp past
    simp only [UInt64.toNat_one]
    omega
  have recentOk : store.validateTargetEpochAgainstCurrentTime config attestation = .ok () := by
    simp [validateTargetEpochAgainstCurrentTime, getCurrentStoreEpoch, currentOk, recent,
      bind, Except.bind, pure, Except.pure]
  have targetOk := block_ok_iff.mpr targetKnown
  have votedOk := block_ok_iff.mpr votedKnown
  have notEarlier := UInt64.not_lt.mpr notFuture
  unfold validateOnAttestation
  by_cases gloas : .glamsterdam ≤ fork <;>
    simp [gloas, recentOk, targetOk, votedOk, notEarlier, payload,
      ← epoch, checkpoint, dueOk, currentOk, dueBound, bind, Except.bind, pure, Except.pure,
      Except.mapError, discard, Functor.mapConst, Except.map]

/-- A store that can compute the state of a target can store it and read it back. -/
theorem Store.exists_storeTargetCheckpointState {store : Store preset fork}
    {target : Checkpoint} {state : BeaconState preset fork}
    (computed : store.computeCheckpointState config checks target = .ok state) :
    ∃ withTarget targetState,
      store.storeTargetCheckpointState config checks target = .ok withTarget ∧
      withTarget.checkpointState target = .ok targetState := by
  by_cases cached : store.checkpointStates.contains target
  · have member := Std.TreeMap.contains_iff_mem.mp cached
    have present := Std.TreeMap.mem_iff_isSome_getElem?.mp member
    obtain ⟨targetState, found⟩ := Option.isSome_iff_exists.mp present
    refine ⟨store, targetState, ?_, EthLib.Consensus.Store.checkpointState_ok_iff.mpr found⟩
    simp [EthLib.Consensus.Store.storeTargetCheckpointState, cached, pure, Except.pure]
  · refine ⟨{ store with checkpointStates := store.checkpointStates.insert target state },
      state, ?_, EthLib.Consensus.Store.checkpointState_ok_iff.mpr (by simp)⟩
    simp [EthLib.Consensus.Store.storeTargetCheckpointState, cached, computed, bind, Except.bind,
      pure, Except.pure]

/-- A held, timely duty attestation is accepted, or bounded honest stores name a collision. -/
theorem VoteAt.accepted_of_target_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ}
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {slot : Slot} {committeeIndex : CommitteeIndex} {deadline n k : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (committees : ∀ withTarget targetState,
      ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
        .ok withTarget →
      withTarget.checkpointState attestation.data.target = .ok targetState →
      checkAttestationCommittees targetState attestation = .ok ())
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {targetBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[attestation.data.target.root]? = some targetBlock)
    (valid : ((e.world k).state w).validateOnAttestation config attestation false = .ok ()) :
    ((∃ after, ((e.world k).state w).onAttestation config checks attestation false = .ok after) ∧
      ReadsAttestation config checks ((e.world k).state w) attestation indexed) ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ last ∧ (e.world m).time ≤ last ∧
      ∃ root collision, EthLib.Consensus.Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  rcases EthLib.Consensus.Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ last) with agree | collision
  swap
  · obtain ⟨⟨u, n⟩, ⟨hu, hn⟩, ⟨v, m⟩, ⟨hv, hm⟩, root, collision, found⟩ := collision
    exact .inr ⟨u, hu, v, hv, n, m, hn, hm, root, collision, found⟩
  obtain ⟨sourceStore, sourceState, sourceStored, sourceRead, indexedOk, signed⟩ := vote.reads
  obtain ⟨base, boundary, baseFound, boundaryOk, ran⟩ :=
    e.targetState_fixedChecks anchored start honest sourceStored sourceRead
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ EthLib.Consensus.Store.Reachable.anchor anchored) k w receiver
  obtain ⟨receiverBase, receiverBaseFound, _, _⟩ := reached.blockStatesFromParents known
  have baseEq := e.blockStates_eq anchored (start v honest) (start w receiver)
    (agree (v, n) ⟨honest, nBound⟩ (w, k) ⟨receiver, kBound⟩) baseFound receiverBaseFound
  subst receiverBase
  have computed : ((e.world k).state w).computeCheckpointState config checks
      attestation.data.target = .ok sourceState := by
    simpa [EthLib.Consensus.Store.computeCheckpointState,
      EthLib.Consensus.Store.blockState_ok_iff.mpr receiverBaseFound,
      boundaryOk, lookaheadState, bind, Except.bind, Except.mapError] using ran
  obtain ⟨withTarget, targetState, stored, read⟩ := Store.exists_storeTargetCheckpointState computed
  rcases e.targetStates_eq_or_collision anchored start honest receiver nBound
      kBound sourceStored sourceRead stored read with stateEq | collision
  swap
  · exact .inr collision
  subst targetState
  have committees := committees sourceStore sourceState sourceStored sourceRead
  left
  refine ⟨⟨withTarget.updateLatestMessages indexed.attestingIndices.data.toList attestation, ?_⟩,
    ⟨withTarget, sourceState, stored, read, indexedOk, signed⟩⟩
  simp [EthLib.Consensus.Store.onAttestation, valid, stored, read, committees, indexedOk, signed,
    bind, Except.bind, Except.mapError, pure, Except.pure]

/-- At every fork, a held duty vote is accepted at the next slot, or honest stores collide.

The receiver holds the voted block, at the duty slot or earlier, with the target in its chain.

From Gloas the receiver must also accept the payload status that the vote names.

The vote's event and the receiver's event are bounded by the same time. -/
theorem VoteAt.accepted_at_next_slot_of_payloadVote {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ}
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {slot next : Slot} {committeeIndex : CommitteeIndex} {deadline n arrival : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (committees : ∀ withTarget targetState,
      ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
        .ok withTarget →
      withTarget.checkpointState attestation.data.target = .ok targetState →
      checkAttestationCommittees targetState attestation = .ok ())
    (dataSlot : attestation.data.slot = slot)
    (nextOk : addChecked slot 1 = .ok next)
    (currentOk : ((e.world arrival).state w).getCurrentSlot config = .ok next)
    (arrivalBound : (e.world arrival).time ≤ last) (nBound : (e.world n).time ≤ last)
    {voted : BeaconBlock preset fork}
    (votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some voted)
    (notFuture : voted.slot ≤ slot)
    (payload : ∀ gloas : .glamsterdam ≤ fork,
      ((e.world arrival).state w).validatePayloadVote gloas attestation voted = .ok ())
    (checkpoint : ((e.world arrival).state w).getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root) :
    ((∃ after, ((e.world arrival).state w).onAttestation config checks attestation false =
        .ok after) ∧
      ReadsAttestation config checks ((e.world arrival).state w) attestation indexed) ∨
    HonestCollision (e := e) last := by
  obtain ⟨_, target, _, targetKnown, _, _⟩ :=
    EthLib.Consensus.Store.isAncestor_of_getCheckpointBlock checkpoint
  -- The honest vote's data puts its target at the epoch of its slot.
  have epoch : attestation.data.target.epoch = computeEpochAtSlot preset slot := by
    obtain ⟨_, _, _, _, _, _, _, _, made⟩ := vote.honestData
    exact dataSlot ▸ target_epoch_eq_of_getAttestationData made
  have past : attestation.data.slot < next := UInt64.lt_iff_toNat_lt.mpr (by
    have sum := (addChecked_ok_iff.mp (dataSlot ▸ nextOk)).2
    simp only [UInt64.toNat_one] at sum
    omega)
  have valid := validateOnAttestation_of_facts currentOk
    ((epoch.trans (congrArg (computeEpochAtSlot preset) dataSlot).symm) ▸
      epoch_recent_at_next_slot (dataSlot ▸ nextOk))
    (epoch.trans (congrArg (computeEpochAtSlot preset) dataSlot).symm)
    targetKnown votedKnown (dataSlot ▸ notFuture)
    payload checkpoint past
  exact vote.accepted_of_target_known anchored start honest receiver committees
    nBound arrivalBound targetKnown valid

/-- From Gloas, a receiver passes the payload check of an honest duty vote for a block it holds.

Both stores start at the anchor store, and the receiver reads the vote a delay after its deadline.

For each envelope in its view that the receiver accepts, its store already marks the root verified.

Otherwise two honest stores at bounded times collide. -/
theorem VoteAt.validatePayloadVote_or_collision {Δ : ℕ} (sync : e.Synchronous Δ)
    (gloas : .glamsterdam ≤ fork) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor) {last : ℕ}
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    (startVoter : e.start v = anchor) (startReceiver : e.start w = anchor)
    {slot : Slot} {committeeIndex : CommitteeIndex} {deadline n arrival : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (late : deadline + Δ ≤ (e.world arrival).time) (arrivalBound : (e.world arrival).time ≤ last)
    (closed : ∀ (signed : SignedExecutionPayloadEnvelope preset fork) after,
      .envelope gloas signed ∈ (e.world arrival).view w →
      ((e.world arrival).state w).onExecutionPayloadEnvelope config checks sources gloas signed =
        .ok after →
      ((e.world arrival).state w).isPayloadVerified gloas signed.message.beaconBlockRoot = true)
    {voted : BeaconBlock preset fork}
    (votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some voted) :
    ((e.world arrival).state w).validatePayloadVote gloas attestation voted = .ok () ∨
      HonestCollision (e := e) last := by
  rcases e.blocksAgree_or_collision last with agree | collision
  swap
  · exact .inr collision
  -- The voter's head is the voted block, since the two stores agree.
  obtain ⟨head, headBlock, -, state, headOk, headKnown, -, -, made⟩ := vote.honestData
  obtain ⟨indexOk, -, slotEq, rootEq, -, -⟩ := getAttestationData_eq_ok_iff.mp made
  have nBound : (e.world n).time ≤ last := by
    have := vote.atTime
    omega
  obtain rfl : headBlock = voted := agree v honest w receiver n arrival nBound arrivalBound _ _ _
    (by rw [rootEq]; exact headKnown) votedKnown
  -- A vote at its head's slot or on an empty head names no payload.
  by_cases same : headBlock.slot = state.slot
  · rw [attestationDataIndex_of_glamsterdam_of_eq gloas same, Except.ok.injEq] at indexOk
    exact .inl (by simp [Store.validatePayloadVote, ← indexOk, pure, Except.pure])
  rw [attestationDataIndex_of_glamsterdam_of_ne gloas same] at indexOk
  cases status : head.payloadStatus <;> rw [status] at indexOk <;>
    simp only [Except.ok.injEq, reduceCtorEq] at indexOk
  · exact .inl (by simp [Store.validatePayloadVote, ← indexOk, pure, Except.pure])
  -- A full head has its payload verified at the voter, and synchrony delivers it.
  have verified := Store.isPayloadVerified_of_getHead gloas headOk status
  rw [← rootEq] at verified
  obtain ⟨st, stFound, -⟩ :=
    Store.Reachable.blockStatesFromParents
      (e.reachable_of_start (startReceiver ▸ Store.Reachable.anchor anchored) arrival) votedKnown
  rcases e.payloadVerified_of_partiallySynchronous sync gloas anchorSlot anchored honest receiver
      startVoter startReceiver (by rw [vote.atTime, Nat.max_zero]; exact late) arrivalBound
      closed verified ⟨st, stFound⟩ with delivered | collision
  · have slotNe : headBlock.slot ≠ attestation.data.slot := slotEq ▸ same
    exact .inl (by simp [Store.validatePayloadVote, ← indexOk, slotNe, delivered, pure,
      Except.pure])
  · exact .inr collision

/-- A held duty vote is accepted at the next slot, or bounded honest stores name a collision.

The receiver holds the voted block, at the duty slot or earlier, with the target in its chain.

The vote's event and the receiver's event are bounded by the same time. -/
theorem VoteAt.accepted_at_next_slot (preGloas : fork < .glamsterdam) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ}
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {slot next : Slot} {committeeIndex : CommitteeIndex} {deadline n arrival : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (committees : ∀ withTarget targetState,
      ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
        .ok withTarget →
      withTarget.checkpointState attestation.data.target = .ok targetState →
      checkAttestationCommittees targetState attestation = .ok ())
    (dataSlot : attestation.data.slot = slot)
    (nextOk : addChecked slot 1 = .ok next)
    (currentOk : ((e.world arrival).state w).getCurrentSlot config = .ok next)
    (arrivalBound : (e.world arrival).time ≤ last) (nBound : (e.world n).time ≤ last)
    {voted : BeaconBlock preset fork}
    (votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some voted)
    (notFuture : voted.slot ≤ slot)
    (checkpoint : ((e.world arrival).state w).getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root) :
    ((∃ after, ((e.world arrival).state w).onAttestation config checks attestation false =
        .ok after) ∧
      ReadsAttestation config checks ((e.world arrival).state w) attestation indexed) ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ last ∧ (e.world m).time ≤ last ∧
      ∃ root collision, EthLib.Consensus.Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  exact vote.accepted_at_next_slot_of_payloadVote anchored start honest receiver committees
    dataSlot nextOk currentOk arrivalBound nBound votedKnown notFuture
    (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) checkpoint

/-- A delivered duty is recorded and retained, or bounded honest stores name a collision.

The recorded vote ranks at least as high as the duty vote.

From Gloas, the anchor block must be at or before the slot of the anchor state. -/
theorem VoteAt.recorded_at_next_slot {Δ : ℕ} (sync : e.Synchronous Δ)
    (anchorSlot : .glamsterdam ≤ fork → anchorBlock.slot ≤ anchorState.slot)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ}
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {slot next : Slot} {committeeIndex : CommitteeIndex} {deadline n arrival endpoint : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (committees : ∀ withTarget targetState,
      ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
        .ok withTarget →
      withTarget.checkpointState attestation.data.target = .ok targetState →
      checkAttestationCommittees targetState attestation = .ok ())
    (dataSlot : attestation.data.slot = slot)
    (nextOk : addChecked slot 1 = .ok next)
    (currentOk : ((e.world arrival).state w).getCurrentSlot config = .ok next)
    (late : deadline + Δ ≤ (e.world arrival).time)
    (upToDate : UpToDate config checks sources (e.world arrival).time
      ((e.world arrival).view w) ((e.world arrival).state w))
    (counted : v ∉ ((e.world arrival).state w).equivocatingIndices)
    (later : arrival ≤ endpoint) (arrivalBound : (e.world arrival).time ≤ last)
    {voted : BeaconBlock preset fork}
    (votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some voted)
    (notFuture : voted.slot ≤ slot)
    (checkpoint : ((e.world arrival).state w).getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root) :
    (∃ message, ((e.world endpoint).state w).latestMessages[v]? = some message ∧
      (LatestMessage.ofAttestation attestation).rank ≤ message.rank) ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ last ∧ (e.world m).time ≤ last ∧
      ∃ root collision, EthLib.Consensus.Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  have nBound : (e.world n).time ≤ last := by have := vote.atTime; omega
  -- From Gloas the payload check of the vote passes, as the receiver is a fixed point.
  have accepted : ((∃ after, ((e.world arrival).state w).onAttestation config checks attestation
        false = .ok after) ∧
      ReadsAttestation config checks ((e.world arrival).state w) attestation indexed) ∨
      HonestCollision (e := e) last := by
    by_cases gloas : .glamsterdam ≤ fork
    · rcases vote.validatePayloadVote_or_collision sync gloas (anchorSlot gloas) anchored honest
          receiver (start v honest) (start w receiver) late arrivalBound
          (fun _ _ mem accepted => upToDate.2 _ (.envelope mem accepted) ▸
            Store.onExecutionPayloadEnvelope_verified accepted) votedKnown with checked | collision
      · exact vote.accepted_at_next_slot_of_payloadVote anchored start honest receiver committees
          dataSlot nextOk currentOk arrivalBound nBound votedKnown notFuture (fun _ => checked)
          checkpoint
      · exact .inr collision
    · exact vote.accepted_at_next_slot (Nat.lt_of_not_le gloas) anchored start honest receiver
        committees dataSlot nextOk currentOk arrivalBound nBound votedKnown notFuture checkpoint
  rcases accepted with ⟨⟨after, accepted⟩, reads⟩ | collision
  swap
  · exact .inr collision
  exact .inl (vote.recorded_of_le sync honest receiver late upToDate accepted reads counted later)

/-- Honest signatures for one target epoch carry the same attestation data. -/
theorem Execution.data_eq_of_signed_of_target_epoch (slots : 0 < config.SLOT_DURATION_MS)
    {n k : ℕ} {first second : Message preset fork} (sentFirst : first ∈ (e.world n).sent)
    (sentSecond : second ∈ (e.world k).sent) {v : ValidatorIndex} {data other : AttestationData}
    (signedFirst : (v, data) ∈ statements config checks anchorState anchorBlock first)
    (signedSecond : (v, other) ∈ statements config checks anchorState anchorBlock second)
    (honest : v ∈ J) (epoch : data.target.epoch = other.target.epoch) : data = other := by
  have nonslashable := e.isSlashableAttestationData_honest slots (max n k) honest
    (e.monotone_sent (Nat.le_max_left n k) sentFirst)
    (e.monotone_sent (Nat.le_max_right n k) sentSecond) signedFirst signedSecond
  by_contra different
  simp [isSlashableAttestationData, different, epoch] at nonslashable

/-- A latest vote at or above a signed vote's rank cannot come from an older slot. -/
theorem Execution.latest_slot_floor_of_signed_rank
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {v : ValidatorIndex} (honest : v ∈ J) {n k : ℕ}
    {message other : Message preset fork}
    (sent : message ∈ (e.world n).sent) (sentOther : other ∈ (e.world k).sent)
    {data : AttestationData} {attestation : Attestation preset fork}
    (signed : (v, data) ∈ statements config checks anchorState anchorBlock message)
    (signedOther : (v, attestation.data) ∈
      statements config checks anchorState anchorBlock other)
    {store : Store preset fork} (origin : store.VoteOrigin config v attestation)
    (epoch : data.target.epoch = computeEpochAtSlot preset data.slot)
    (rank : (LatestMessage.ofAttestation (fork := fork) attestation).rank ≥ data.target.epoch)
    {slot : Slot} (floor : slot ≤ data.slot) : slot ≤ attestation.data.slot := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have targetLe : data.target.epoch ≤ attestation.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  by_cases same : data.target.epoch = attestation.data.target.epoch
  · have dataEq := Execution.data_eq_of_signed_of_target_epoch slots sent sentOther
      signed signedOther honest same
    exact dataEq ▸ floor
  · have targetLt := UInt64.lt_of_le_of_ne targetLe same
    have slotLe : data.slot ≤ attestation.data.slot := by
      by_contra h
      have reversed := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt (UInt64.not_le.mp h)))
      rw [epoch, origin.targetEpoch] at targetLt
      have strict := UInt64.lt_iff_toNat_lt.mp targetLt
      simp only [computeEpochAtSlot, UInt64.toNat_div] at strict
      omega
    exact UInt64.le_trans floor slotLe

/-- An honest duty vote is a sent message that signs its own data. -/
theorem VoteAt.signed_sent {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {v : ValidatorIndex} (honest : v ∈ J)
    {slot : Slot} {committee : CommitteeIndex} {deadline n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committee deadline n attestation indexed) :
    Message.attestation attestation ∈ (e.world (n + 1)).sent ∧
      (v, attestation.data) ∈
        statements config checks anchorState anchorBlock (Message.attestation attestation) := by
  refine ⟨e.view_subset_sent (n + 1) v (by simp [Execution.world_succ, vote.sends, World.apply]),
    ?_⟩
  obtain ⟨_, _, _, _, indexedOk, _⟩ := vote.reads
  obtain ⟨attesters, attestersOk, _⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
  obtain ⟨indexed', indexedOk', _, dataEq, _⟩ :=
    getIndexedAttestation_of_getAttestingIndices attestersOk
  rw [indexedOk, Except.ok.injEq] at indexedOk'
  subst indexedOk'
  have reached := e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) n v honest
  refine ⟨(e.world n).state v, indexed, reached, vote.reads, ?_, dataEq.symm⟩
  have alone := vote.alone
  simp only [← Array.mem_toList_iff, alone, List.mem_singleton]

end EthLib.Consensus.Models.Network
