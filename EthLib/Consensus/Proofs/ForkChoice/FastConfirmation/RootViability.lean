module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.CheckpointConsistency
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.IncludedVotes
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification
import EthLib.Consensus.Proofs.ForkChoice.SiblingCap
import EthLib.Consensus.Proofs.Transition.InactivityLeakVoter
import EthLib.Consensus.Proofs.Transition.ParticipationFlagsKept
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Root viability: the confirmed root in the filtered tree

An accepted current-target test has honest signers with two thirds of the head state's balance.

At a later time, a confirmed root is in the filtered tree of an up-to-date honest store above it.

Otherwise two honest stores collide on a block, or accountable-safety evidence holds.

The honest count, the coverage of honest heads and the caller's later head reads are assumed.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- At every event at the given time, an up-to-date store of the caller reads a head. -/
def CallerHeadAt (u : ValidatorIndex) (begin : ℕ) : Prop :=
  ∀ k, (e.world k).time = begin →
    UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u) →
    ∃ hd : ForkChoiceNode, ((e.world k).state u).getHead config = .ok hd

/-- The rollover read for the current target of a call's head, at every rollover up to `last`.

The confirmed root's viability step reads it, so that it can name the target's honest voters. -/
def CallRolloverRead (u : ValidatorIndex) (n : ℕ) (head : Root) (last : ℕ) : Prop :=
  ∀ (target : Checkpoint) (nextEpoch : Epoch) (first : Slot) (begin : UInt64),
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    addChecked target.epoch 1 = .ok nextEpoch →
    computeStartSlotAtEpoch preset nextEpoch = .ok first →
    computeTimeAtSlotMs config genesisTimeMs first = .ok begin →
    begin.toNat ≤ last →
    CallerHeadAt (e := e) u begin.toNat

/-- Each accepted root has a recent realized justification in its own stored post-state.

It restricts the runs in scope: the rule does not check it. -/
def AcceptedRealizedRecent (store : Store preset fork) (roots : List Root) : Prop :=
  ∀ root ∈ roots, ∃ (block : BeaconBlock preset fork) (state : BeaconState preset fork),
    store.blocks[root]? = some block ∧ store.blockStates[root]? = some state ∧
    (computeEpochAtSlot preset block.slot).toNat ≤
      state.currentJustifiedCheckpoint.epoch.toNat + 1

/-- Each accepted root of an earlier epoch is realized as justified by the head's stored state.

It restricts the runs in scope: the rule does not check it. -/
def AcceptedRealizedHead (store : Store preset fork) (config : Config) (head : Root)
    (roots : List Root) : Prop :=
  ∀ root ∈ roots, ∀ epoch (block : BeaconBlock preset fork),
    store.getCurrentStoreEpoch config = .ok epoch → store.blocks[root]? = some block →
    computeEpochAtSlot preset block.slot < epoch →
    ∃ headState : BeaconState preset fork, store.blockStates[head]? = some headState ∧
      store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
      computeEpochAtSlot preset block.slot ≤ headState.currentJustifiedCheckpoint.epoch

/-- A target with an honest quorum at a call is included by the start of the epoch after next.

This is the adapter of Assumption 3 of arXiv 2405.00549v4 §4.2 to counted votes.

It is a premise on the network, and it differs from that assumption in four ways.

The quorum is honest voters with two thirds of the active balance of the pulled-up head state.

Each of them sent a vote for the target, with any source.

The target stays canonical from the confirming call to the receiver, not through epoch E + 1.

The conclusion is a held seed above the block, of epoch E or E + 1, that reads the target.

The seed has a realized justification at E or later, or holds the voters' target votes.

So the votes for the target of E count by the end of E + 1, and receivers of E + 2 see them.

The seed reads the call's block at the target root, so two honest stores may collide instead. -/
def TargetIncluded (limit : ℕ) : Prop :=
  ∀ u ∈ J, ∀ q n, q ≤ n → (e.world n).time ≤ limit →
    ∀ (head : ForkChoiceNode) state total target, ∀ voters : Finset ValidatorIndex,
    ((e.world q).state u).getHead config = .ok head →
    ((e.world q).state u).getPulledUpHeadState config head.root = .ok state →
    ((e.world q).state u).getCurrentTarget config head.root = .ok target →
    getTotalActiveBalance state = .ok total →
    ((e.world q).state u).getCurrentStoreEpoch config = .ok target.epoch →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok target.epoch →
    2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ next first begin, addChecked target.epoch 1 = .ok next →
    computeStartSlotAtEpoch preset next = .ok first →
    computeTimeAtSlotMs config genesisTimeMs first = .ok begin →
    (∀ v ∈ voters, v ∈ J ∧ SignsTarget e v target (begin.toNat - 1)) →
    ∀ w ∈ J, ∀ k current, (e.world k).time ≤ limit → (e.world n).time ≤ (e.world k).time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok current →
      target.epoch.toNat + 2 ≤ current.toNat →
      ∀ root rootEpoch, ((e.world k).state w).getBlockEpoch root = .ok rootEpoch →
      rootEpoch ≤ target.epoch →
      ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
      HonestHeadsCover (e := e) root (e.world n).time (e.world k).time →
      (∃ (seed : Root) (seedBlock : BeaconBlock preset fork) (seedState : BeaconState preset fork),
        ((e.world k).state w).blocks[seed]? = some seedBlock ∧
        ((e.world k).state w).blockStates[seed]? = some seedState ∧
        ((e.world k).state w).isAncestor ⟨seed, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
        target.epoch ≤ computeEpochAtSlot preset seedBlock.slot ∧
        (computeEpochAtSlot preset seedBlock.slot).toNat < target.epoch.toNat + 2 ∧
        getBlockRoot seedState target.epoch = .ok target.root ∧
        (target.epoch ≤ seedState.currentJustifiedCheckpoint.epoch ∨
          (∃ altair : .altair ≤ fork, ∀ v ∈ voters,
            TargetFlagAt (recentParticipation seedState altair
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) v.toNat) ∨
          ∃ before : fork < .altair, ∀ v ∈ voters,
            ∃ pending ∈ recentPending seedState before
                (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
              pending.data.target = target ∧
              ∃ indices, getPendingAttestingIndices seedState pending = .ok indices ∧
                v ∈ indices)) ∨
        HonestCollision (e := e) limit

/-- Two honest stores agree on an epoch's active validators below a common origin of the epoch.

The first reads the pulled-up state of a head, the second the stored state of a head.

Both heads descend from the origin. -/
private theorem active_eq_of_common_origin {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J)
    {n k : ℕ}
    (same : ∀ (r : Root) left right, ((e.world n).state u).blocks[r]? = some left →
      ((e.world k).state w).blocks[r]? = some right → left = right)
    {origin : Root} {originBlock otherOrigin : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    (otherKnown : ((e.world k).state w).blocks[origin]? = some otherOrigin)
    {countHead otherHead : Root} {countState otherState : BeaconState preset fork}
    (countRead : ((e.world n).state u).getPulledUpHeadState config countHead = .ok countState)
    (otherRead : ((e.world k).state w).blockState otherHead = .ok otherState)
    (countDescends : ((e.world n).state u).isAncestor ⟨countHead, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    (otherDescends : ((e.world k).state w).isAncestor ⟨otherHead, .pending⟩
      ⟨origin, .pending⟩ = .ok true) :
    getActiveValidatorIndices countState (computeEpochAtSlot preset originBlock.slot) =
      getActiveValidatorIndices otherState (computeEpochAtSlot preset originBlock.slot) := by
  have reached := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) n u
    caller
  have reachedOther := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored)
    k w receiver
  have sameOrigin := same origin originBlock otherOrigin originKnown otherKnown
  subst otherOrigin
  obtain ⟨common, commonHeld, anchorCommon, _⟩ := reached.blockStatesFromParents originKnown
  obtain ⟨commonOther, commonOtherHeld, _, _⟩ := reachedOther.blockStatesFromParents otherKnown
  have sameState := e.blockStates_eq anchored caller receiver (start u caller)
    (start w receiver) same commonHeld commonOtherHeld
  subst commonOther
  have originSlot : common.slot = originBlock.slot := by
    by_cases isAnchor : originBlock = anchorBlock
    · rw [anchorCommon isAnchor, isAnchor, anchorSlot]
    · exact (reached.blockState_header originKnown commonHeld isAnchor).1
  have fixed : computeEpochAtSlot preset originBlock.slot ≤ activityFixedEpoch common := by
    rw [← originSlot]
    exact getCurrentEpoch_le_activityFixedEpoch common
  have count := countRead
  simp only [Store.getPulledUpHeadState, bind_ok_iff] at count
  obtain ⟨raw, rawOk, epoch, epochOk, rest⟩ := count
  have run := reached.runKept_of_getAncestor (UInt64.le_of_eq anchorSlot)
    (Store.getAncestor_of_isAncestor_of_lt preGloas originKnown countDescends)
    (Store.blockState_ok_iff.mp rawOk) commonHeld
  have pulled : RunKept raw countState := by
    split at rest
    · obtain ⟨first, _, processed⟩ := bind_ok_iff.mp rest
      exact runKept_processSlots (mapError_ok_iff.mp processed)
    · cases Except.ok.inj rest
      exact RunKept.refl _
  have otherRun := reachedOther.runKept_of_getAncestor (UInt64.le_of_eq anchorSlot)
    (Store.getAncestor_of_isAncestor_of_lt preGloas otherKnown otherDescends)
    (Store.blockState_ok_iff.mp otherRead) commonOtherHeld
  exact ((run.trans pulled).active.getActiveValidatorIndices_eq fixed).trans
    (otherRun.active.getActiveValidatorIndices_eq fixed).symm

/-- A store read at a slot start reads each later slot start of the model's clock. -/
private theorem slot_at_later_start (slots : 0 < config.SLOT_DURATION_MS)
    {u : ValidatorIndex} {n k : ℕ} {reference later : Slot} {referenceBegin begin : UInt64}
    (referenceSlot : ((e.world n).state u).getCurrentSlot config = .ok reference)
    (referenceOk : computeTimeAtSlotMs config genesisTimeMs reference = .ok referenceBegin)
    (referenceTime : (e.world n).time = referenceBegin.toNat)
    (referenceReady : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (beginOk : computeTimeAtSlotMs config genesisTimeMs later = .ok begin)
    (atTime : (e.world k).time = begin.toNat)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u)) :
    ((e.world k).state u).getCurrentSlot config = .ok later := by
  have common : ((e.world k).state u).genesisTimeMs = ((e.world n).state u).genesisTimeMs := by
    rw [(e.clock_bounds u k).1, (e.clock_bounds u n).1]
  have referenceClock : ((e.world n).state u).timeMs = referenceBegin :=
    UInt64.toNat_inj.mp (referenceReady.1.trans referenceTime)
  have offset := genesis_offset_of_slot_start slots referenceOk
    (by simpa only [Store.getCurrentSlot, referenceClock] using mapError_ok_iff.mp referenceSlot)
  have clock : ((e.world k).state u).timeMs = begin :=
    UInt64.toNat_inj.mp (ready.1.trans atTime)
  unfold Store.getCurrentSlot
  rw [common, clock]
  exact mapError_ok_iff.mpr (slot_at_start_of_genesis_offset slots beginOk offset)

/-- An active counted voter has a duty in the epoch, read from the window of a later head. -/
private theorem duty_of_active {anchor : Store preset fork} {time : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (windows : AssignmentWindowAgreement (e := e) time) (fit : config.CommitteeWindowsFit preset)
    {u : ValidatorIndex} (caller : u ∈ J) {n k : ℕ} (kBound : (e.world k).time ≤ time)
    (same : ∀ (r : Root) left right, ((e.world n).state u).blocks[r]? = some left →
      ((e.world k).state u).blocks[r]? = some right → left = right)
    {origin : Root} {originBlock : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    {epoch next : Epoch} {first boundary last : Slot}
    (originEpoch : computeEpochAtSlot preset originBlock.slot = epoch)
    (nextOk : addChecked epoch 1 = .ok next)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (boundaryOk : computeStartSlotAtEpoch preset next = .ok boundary)
    (lastOk : subChecked boundary 1 = .ok last)
    {countHead : Root} {state : BeaconState preset fork}
    (countRead : ((e.world n).state u).getPulledUpHeadState config countHead = .ok state)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (countDescends : ((e.world n).state u).isAncestor ⟨countHead, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    {hd : ForkChoiceNode}
    (headOk : ((e.world k).state u).getHead config = .ok hd)
    (slotOk : ((e.world k).state u).getCurrentSlot config = .ok boundary)
    (descends : ((e.world k).state u).isAncestor hd ⟨origin, .pending⟩ = .ok true)
    {v : ValidatorIndex} (honest : v ∈ J)
    (active : v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset) :
    ∃ slot index, first ≤ slot ∧ slot ≤ last ∧ assignment.committee v slot = some index := by
  have forwardN := e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored) n u caller
  have forwardK := e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) k u caller
  have pending := Store.getHead_pending preGloas headOk
  have nodeEq : hd = ⟨hd.root, .pending⟩ := by
    cases hd
    simp_all
  obtain ⟨otherOrigin, otherKnown⟩ := Store.held_of_isAncestor descends
  obtain ⟨headState, headStateOk⟩ := headState_of_descends forwardK otherKnown
    (by rw [← nodeEq]; exact descends)
  have activeEq := active_eq_of_common_origin anchored start anchorSlot preGloas caller caller
    same originKnown otherKnown countRead headStateOk countDescends
    (by rw [← nodeEq]; exact descends)
  rw [originEpoch] at activeEq
  have stateEpoch := forwardN.pulledUpHeadState_epoch positive epochOk countRead
  have activeAt : v ∈ getActiveValidatorIndices headState epoch := by
    rw [← activeEq, ← stateEpoch]
    exact List.mem_toFinset.mp active
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  have lastPos := (subChecked_ok_iff.mp lastOk).1
  simp only [UInt64.toNat_one] at nextNat lastNat lastPos
  have past : last < boundary := UInt64.lt_iff_toNat_lt.mpr (by omega)
  obtain ⟨participants, read⟩ := Store.getCommitteesBetweenSlots_exists (first := first) fit
    headStateOk (BeaconState.registryWithinLimit_of_lt preGloas headState) slotOk past
  have member := Store.mem_getCommitteesBetweenSlots_of_active positive read headStateOk
    (by omega) (by rw [← nextNat, ← boundaryNat]; omega) activeAt
  have epochBoundary := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) boundaryOk
  have epochFirst := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) firstOk
  obtain ⟨slot, index, low, high, duty⟩ := (windows u caller k kBound hd boundary first last
    participants headOk slotOk past (fun found foundOk => by
      have le := forwardK.forwardReachable.headState_epoch_le slotOk foundOk
      rw [epochBoundary] at le
      rw [epochFirst]
      omega) read v honest).mp member
  exact ⟨slot, index, low, high, duty⟩

/-- A counted voter with a duty from the call's slot to the end of the epoch signs the target.

At the duty its head descends from the origin, which is in the target's epoch.

So the vote's walk to the epoch's first slot meets the caller's, which reads the target. -/
private theorem signs_of_duty {anchor : Store preset fork} {Δ time : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (preGloas : fork < .glamsterdam)
    (fits : DelayFits fork config genesisTimeMs Δ) (votes : ValidatedDutyVotes (e := e) time)
    (nonzero : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    {head : ForkChoiceNode} {target : Checkpoint} {origin : Root}
    {originBlock : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    (originEpoch : computeEpochAtSlot preset originBlock.slot = target.epoch)
    (descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨origin, .pending⟩ =
      .ok true)
    (targetRead : ((e.world n).state u).getCheckpointBlock head.root target.epoch =
      .ok target.root)
    {first boundary : Slot} {begin : UInt64}
    (firstOk : computeStartSlotAtEpoch preset target.epoch = .ok first)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs boundary = .ok begin)
    (bounded : begin.toNat ≤ time)
    {current : Slot} {callBegin : UInt64}
    (callBeginOk : computeTimeAtSlotMs config genesisTimeMs current = .ok callBegin)
    (atCall : (e.world n).time = callBegin.toNat)
    (covers : HonestHeadsCover (e := e) origin (e.world n).time begin.toNat)
    {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot} {index : CommitteeIndex}
    (after : current ≤ slot) (high : slot < boundary)
    (slotEpoch : computeEpochAtSlot preset slot = target.epoch)
    (duty : assignment.committee v slot = some index) :
    SignsTarget e v target (begin.toNat - 1) := by
  obtain ⟨due, dueOk⟩ := fits.1
  have highNat := UInt64.lt_iff_toNat_lt.mp high
  have nextSlotOk : addChecked slot 1 = .ok (slot + 1) :=
    addChecked_of_lt (by have := boundary.toNat_lt; simp only [UInt64.toNat_one]; omega)
  have nextLe : slot + 1 ≤ boundary := UInt64.le_iff_toNat_le.mpr (by
    rw [(addChecked_ok_iff.mp nextSlotOk).2]
    simp only [UInt64.toNat_one]
    omega)
  obtain ⟨following, followingOk, -, followingLe⟩ := exists_timeAtSlotMs_of_le nextLe beginOk
  obtain ⟨slotStart, slotStartOk, -, -⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt high) beginOk
  have deadlineOk : IsAttestationDeadline fork config genesisTimeMs slot
      (slotStart.toNat + due.toNat) := ⟨slotStart, due, slotStartOk, dueOk, rfl⟩
  have before := fits.before_boundary nextSlotOk slotStartOk followingOk deadlineOk
  have followingNat := UInt64.le_iff_toNat_le.mp followingLe
  obtain ⟨callBegin', callBeginOk', -, callLe⟩ := exists_timeAtSlotMs_of_le after slotStartOk
  rw [callBeginOk, Except.ok.injEq] at callBeginOk'
  subst callBegin'
  have callNat := UInt64.le_iff_toNat_le.mp callLe
  have started : e.startTime ≤ (e.world n).time := by
    have := e.monotone_time (Nat.zero_le n)
    simpa [Execution.world_zero, World.initial] using this
  obtain ⟨k, attestation, indexed, vote, -⟩ := votes v honest slot index _ duty deadlineOk
    (by omega) (by omega)
  have inSlot := fits.due_lt_slot nextSlotOk slotStartOk followingOk dueOk
  obtain ⟨-, dataEpoch, hv, -, hvOk, -, rootEq, -⟩ :=
    vote.data_head anchored (UInt64.le_of_eq anchorSlot) start honest deadlineOk dueOk inSlot
  have kTime := vote.atTime
  have kBound : (e.world k).time ≤ time := by omega
  have dataTarget := vote.data_target anchored anchorSlot anchorAtBoundary start honest
    (nonzero v honest k kBound)
  -- At the duty the voter's head descends from the origin.
  have descendsV := covers (e.world k).time (by omega) (by omega) v honest k hv rfl
    (by rw [kTime]; exact vote.upToDate) hvOk
  have pending := Store.getHead_pending preGloas hvOk
  have nodeEq : hv = ⟨hv.root, .pending⟩ := by
    cases hv
    simp_all
  rw [nodeEq] at descendsV
  obtain ⟨originBlockV, originKnownV⟩ := Store.held_of_isAncestor descendsV
  have nBound : (e.world n).time ≤ time := by omega
  have sameBlock := agree v honest u caller k n kBound nBound origin originBlockV originBlock
    originKnownV originKnown
  subst originBlockV
  -- The caller's target is the origin's walk to the epoch's first slot.
  have firstLe : first ≤ originBlock.slot := UInt64.le_iff_toNat_le.mpr (by
    have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
    have epochNat := congrArg UInt64.toNat originEpoch
    simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
    rw [firstNat, ← epochNat]
    exact Nat.div_mul_le_self _ _)
  have walk := Store.getAncestor_of_isAncestor_of_lt preGloas originKnown descends
  have read := targetRead
  simp only [Store.getCheckpointBlock, firstOk, Except.mapError, bind, Except.bind] at read
  have through := Store.getAncestor_trans firstLe walk
  rw [through] at read
  obtain ⟨reached, reachedOk, reachedRoot⟩ :
      ∃ x, ((e.world n).state u).getAncestor ⟨origin, .pending⟩ first = .ok x ∧
        x.root = target.root := by
    revert read
    cases ((e.world n).state u).getAncestor ⟨origin, .pending⟩ first <;>
      simp [pure, Except.pure]
  have reachedU := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) n u
    caller
  have reachedV := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k v
    honest
  have aboveAnchor := le_computeStartSlotAtEpoch_of_isStartSlotAtEpoch anchorAtBoundary
    (reachedU.anchorSlot_le (UInt64.le_of_eq anchorSlot) originKnown) (originEpoch ▸ firstOk)
  have walkV := Store.getAncestor_of_same_blocks reachedV
    (fun r b c found found' => agree u caller v honest n k nBound kBound r b c found found')
    aboveAnchor ⟨originBlock, originKnownV⟩ reachedOk
  have readV : ((e.world k).state v).getCheckpointBlock origin target.epoch =
      .ok target.root := by
    simp [Store.getCheckpointBlock, firstOk, Except.mapError, bind, Except.bind, walkV,
      reachedRoot, pure, Except.pure]
  have hvRead := Store.getCheckpointBlock_of_isAncestor preGloas originKnownV descendsV firstOk
    firstLe readV
  rw [← rootEq, ← slotEpoch, ← dataEpoch, dataTarget] at hvRead
  have rootSame := Except.ok.inj hvRead
  have targetEq : attestation.data.target = target := by
    have epochSame : attestation.data.target.epoch = target.epoch := dataEpoch.trans slotEpoch
    calc attestation.data.target
        = ⟨attestation.data.target.epoch, attestation.data.target.root⟩ := rfl
      _ = ⟨target.epoch, target.root⟩ := by rw [epochSame, rootSame]
      _ = target := rfl
  obtain ⟨sent, member⟩ := vote.signed_sent anchored start honest
  have succTime : (e.world (k + 1)).time = (e.world k).time := by
    simp [Execution.world_succ, vote.sends, World.apply]
  exact ⟨k + 1, by omega, _, sent, _, member, targetEq⟩

/-- An accepted current-target test has active honest signers with two thirds of the active balance.

Each votes for the target before the next epoch, unless two honest stores collide on a block.

It assumes the honest count, and honest heads above a block of the epoch until the next one. -/
theorem Execution.honestTargetVotes_signed_of_checked {anchor : Store preset fork} {Δ time : ℕ}
    {margin : ℕ} (slots : 0 < config.SLOT_DURATION_MS)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (votes : ValidatedDutyVotes (e := e) time)
    (windows : AssignmentWindowAgreement (e := e) time) (fit : config.CommitteeWindowsFit preset)
    (nonzero : HeldBlockStateRootsNonzero (e := e) time)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlotStart : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {head : ForkChoiceNode} {target : Checkpoint} {origin : Root} {first : Slot}
    {nextEpoch : Epoch} {begin : UInt64}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (justified : ((e.world n).state u).willCurrentTargetBeJustified config head.root = .ok true)
    (count : HonestTargetVotes e margin u n head.root)
    (targetOk : ((e.world n).state u).getCurrentTarget config head.root = .ok target)
    (originEpochOk : ((e.world n).state u).getBlockEpoch origin = .ok target.epoch)
    (descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨origin, .pending⟩ =
      .ok true)
    (nextOk : addChecked target.epoch 1 = .ok nextEpoch)
    (firstOk : computeStartSlotAtEpoch preset nextEpoch = .ok first)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs first = .ok begin)
    (bounded : begin.toNat ≤ time)
    (covers : HonestHeadsCover (e := e) origin (e.world n).time (begin.toNat + 1))
    (rollover : CallerHeadAt (e := e) u begin.toNat) :
    (∃ (state : BeaconState preset fork) (total : Gwei) (voters : Finset ValidatorIndex),
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state ∧
      getTotalActiveBalance state = .ok total ∧
      2 * total.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters ∧
      ∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧ SignsTarget e v target (begin.toNat - 1)) ∨
      HonestCollision (e := e) time := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agreeAll | collision
  rotate_left
  · obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, evidence, searched⟩ := collision
    exact .inr ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩
  have agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right :=
    fun a ha b hb i j hi hj => agreeAll (a, i) ⟨ha, hi⟩ (b, j) ⟨hb, hj⟩
  have positive := fit.positive
  refine .inl ?_
  obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := atSlotStart
  obtain ⟨state, total, target', slot, epochStart, lastCall, participants, voters, stateOk,
    totalOk, targetOk', slotOk, epochOk, epochStartOk, lastCallOk, participantsOk, targetRead,
    members, bound⟩ := quorum_of_current_target count justified
  rw [targetOk, Except.ok.injEq] at targetOk'
  subst target'
  rw [callSlotOk, Except.ok.injEq] at slotOk
  subst slot
  have slotEpoch : computeEpochAtSlot preset callSlot = target.epoch := by
    simpa only [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure,
      Except.pure, Except.ok.injEq] using epochOk
  rw [slotEpoch] at epochStartOk
  obtain ⟨originBlock, originKnown, originEpoch⟩ :
      ∃ b, ((e.world n).state u).blocks[origin]? = some b ∧
        computeEpochAtSlot preset b.slot = target.epoch := by
    simp only [Store.getBlockEpoch, bind_ok_iff, pure, Except.pure, Except.ok.injEq]
      at originEpochOk
    obtain ⟨b, bOk, bEpoch⟩ := originEpochOk
    exact ⟨b, Store.block_ok_iff.mp bOk, bEpoch⟩
  -- Slot arithmetic: the call is before the boundary, and the boundary is positive.
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have epochStartNat := (computeStartSlotAtEpoch_ok_iff.mp epochStartOk).2
  simp only [UInt64.toNat_one] at nextNat
  have epochNat := congrArg UInt64.toNat slotEpoch
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
  have callBelow : callSlot < first := UInt64.lt_iff_toNat_lt.mpr (by
    have bound := Nat.lt_mul_div_succ callSlot.toNat positive
    rw [epochNat, Nat.mul_comm, ← nextNat, ← firstNat] at bound
    exact bound)
  have callBefore : (e.world n).time < begin.toNat := by
    obtain ⟨offset, offsetOk, summed⟩ := bind_ok_iff.mp callBeginOk
    obtain ⟨otherOffset, otherOffsetOk, otherSummed⟩ := bind_ok_iff.mp beginOk
    have a := (mulChecked_ok_iff.mp offsetOk).2
    have b := (addChecked_ok_iff.mp summed).2
    have c := (mulChecked_ok_iff.mp otherOffsetOk).2
    have d := (addChecked_ok_iff.mp otherSummed).2
    have strict := Nat.mul_lt_mul_of_pos_right
      (UInt64.lt_iff_toNat_lt.mp callBelow) (UInt64.lt_iff_toNat_lt.mp slots)
    rw [atCall]
    omega
  have firstPos : 1 ≤ first := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp callBelow
    simp only [UInt64.toNat_one]
    omega)
  have lastOk : subChecked first 1 = .ok (first - 1) :=
    subChecked_ok_iff.mpr ⟨firstPos, UInt64.toNat_sub_of_le _ _ firstPos⟩
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  simp only [UInt64.toNat_one] at lastNat
  -- The caller's rollover event at the boundary.
  have started : e.startTime ≤ (e.world n).time := by
    have := e.monotone_time (Nat.zero_le n)
    simpa [Execution.world_zero, World.initial] using this
  obtain ⟨k, atK, readyK⟩ := (prompt u caller first begin beginOk (by omega) bounded).1
  obtain ⟨hd, hdOk⟩ := rollover k atK readyK
  have slotK := slot_at_later_start slots callSlotOk callBeginOk atCall upToDate beginOk atK
    readyK
  have nBound : (e.world n).time ≤ time := by omega
  have kBound : (e.world k).time ≤ time := by omega
  have hdDescends := covers (e.world k).time (by omega) (by omega) u caller k hd rfl readyK hdOk
  refine ⟨state, total, voters, stateOk, totalOk, bound, fun v member => ⟨(members v member).1,
    (members v member).2.1, ?_⟩⟩
  obtain ⟨honest, active, signed | unseen⟩ := members v member
  · obtain ⟨j, before, rest⟩ := signed
    exact ⟨j, by omega, rest⟩
  · obtain ⟨dutySlot, index, low, high, duty⟩ := duty_of_active anchored start anchorSlot
      positive preGloas retained windows fit caller kBound
      (agree u caller u caller n k nBound kBound) originKnown originEpoch nextOk epochStartOk
      firstOk lastOk stateOk epochOk descends hdOk slotK hdDescends honest active
    have after := duty_after_call anchored start positive retained windows caller nBound headOk
      callSlotOk (slotEpoch ▸ epochStartOk) lastCallOk participantsOk honest unseen
      (by rw [← slotEpoch] at epochStartOk; exact low)
      duty
    have highLt : dutySlot < first := UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.le_iff_toNat_le.mp high
      have := UInt64.le_iff_toNat_le.mp firstPos
      simp only [UInt64.toNat_one] at this
      omega)
    have dutyEpoch : computeEpochAtSlot preset dutySlot = target.epoch := by
      apply UInt64.toNat_inj.mp
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      have lowNat := UInt64.le_iff_toNat_le.mp low
      have highNat := UInt64.lt_iff_toNat_lt.mp highLt
      have firstSum : first.toNat = target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
          preset.SLOTS_PER_EPOCH.toNat := by
        rw [firstNat, nextNat, Nat.add_mul, Nat.one_mul]
      exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    exact signs_of_duty anchored start anchorSlot anchorAtBoundary preGloas fits votes nonzero
      agree caller originKnown originEpoch descends targetRead epochStartOk beginOk bounded
      callBeginOk atCall (fun t low high => covers t low (by omega)) honest after highLt
      dutyEpoch duty

end EthLib.Consensus.Models.Network

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-! ## The justified test above the root -/

/-- A held block above a root, each of whose descendants passes the justified test of fork choice.

That test is the justified half of the viability of a leaf. -/
private def JustifiedTestAbove (store : Store preset fork) (config : Config) (root : Root) : Prop :=
  ∃ (top : Root) (topBlock : BeaconBlock preset fork),
    store.blocks[top]? = some topBlock ∧
    store.isAncestor ⟨top, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
    ∀ (tip : Root) (source : Checkpoint) (epoch : Epoch),
      store.isAncestor ⟨tip, .pending⟩ ⟨top, .pending⟩ = .ok true →
      store.getCurrentStoreEpoch config = .ok epoch →
      store.getVotingSource config tip = .ok source →
      store.justifiedCheckpoint.epoch = GENESIS_EPOCH ∨
        source.epoch = store.justifiedCheckpoint.epoch ∨ epoch.toNat ≤ source.epoch.toNat + 2

/-- A receiver at most one epoch past the root passes the justified test above the root.

Each voting source above the root is at least the root's realized justification.

That justification is at most one epoch older than the root. -/
private theorem early_receiver_source {anchor : Store preset fork} {time T : ℕ}
    (preGloas : fork < .glamsterdam)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {root : Root} {chain : List Root}
    (realized : AcceptedRealizedRecent ((e.world n).state u) (chain ++ [root]))
    (low : (e.world n).time ≤ T) (high : T ≤ time) {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ}
    (atTime : (e.world k).time = T) {rootBlock : BeaconBlock preset fork} {current : Slot}
    (rootFound : ((e.world k).state w).blocks[root]? = some rootBlock)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (isEarly : (computeEpochAtSlot preset current).toNat ≤
      (computeEpochAtSlot preset rootBlock.slot).toNat + 1) :
    JustifiedTestAbove ((e.world k).state w) config root := by
  have forward := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  have reached := forward.reachable
  have callerBound : (e.world n).time ≤ time := low.trans high
  have receiverBound : (e.world k).time ≤ time := atTime ▸ high
  obtain ⟨callerBlock, callerState, callerFound, callerStored, recent⟩ :=
    realized root (by simp)
  have same := agree u caller w receiver n k callerBound receiverBound root callerBlock rootBlock
    callerFound rootFound
  subst same
  obtain ⟨state, stored, -⟩ := reached.blockStatesFromParents rootFound
  have stateEq := e.blockStates_eq anchorStore caller receiver (anchored u caller)
    (anchored w receiver) (agree u caller w receiver n k callerBound receiverBound) callerStored
    stored
  subst stateEq
  refine ⟨root, callerBlock, rootFound, Store.isAncestor_self (node := ⟨root, .pending⟩)
    rootFound, ?_⟩
  intro tip source epoch above epochOk sourceOk
  have lower := UInt64.le_iff_toNat_le.mp
    (reached.realized_le_source sound (UInt64.le_of_eq anchorSlot) preGloas rootFound stored above
        sourceOk)
  have epochEq : computeEpochAtSlot preset current = epoch := by
    simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
      using epochOk
  subst epochEq
  exact .inr (.inr (by omega))

/-! ## The justified checkpoint of a late receiver -/

/-- A checked call's epoch is at most one after the epoch of a root on the walk from its head. -/
private theorem call_epoch_le_root_add_one {store : Store preset fork}
    {fcr : FastConfirmationStore} {head start root : Root} {chain later : List Root}
    {callSlot : Slot} {rootBlock : BeaconBlock preset fork}
    (checked : store.FastConfirmationChecked config fcr head start root)
    (walk : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    (callSlotOk : store.getCurrentSlot config = .ok callSlot)
    (rootFound : store.blocks[root]? = some rootBlock) :
    (computeEpochAtSlot preset callSlot).toNat ≤
      (computeEpochAtSlot preset rootBlock.slot).toNat + 1 := by
  have callEpochOk : store.getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
  obtain ⟨cEpoch, -, -, sEpoch, cEpochOk, -, -, sEpochOk, recent, -⟩ := checked
  rw [callEpochOk, Except.ok.injEq] at cEpochOk
  subst cEpoch
  obtain ⟨b, t, bOk, tOk, lt⟩ := Store.slot_lt_of_mem_getAncestorRoots walk (by simp)
    (show root ∈ chain ++ root :: later by simp)
  rw [Store.block_ok_iff.mpr rootFound, Except.ok.injEq] at bOk
  subst bOk
  have sEq : sEpoch = computeEpochAtSlot preset t.slot := by
    simpa [Store.getBlockEpoch, tOk, bind, Except.bind, pure, Except.pure] using sEpochOk.symm
  subst sEq
  have mono := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
    (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lt))
  simp only [computeEpochAtSlot, UInt64.toNat_div] at recent ⊢
  omega

/-- A late receiver's justified checkpoint is not after the root's epoch and at most the call's.

Its honest signer votes in the call's epoch.

A vote from the call's slot on is cast on a head above the root, against the strict descent.

Before that slot, the no-conflict test gives an honest third that pins the checkpoint.

It pins it to the call's target, or a voter unseen by the call signs it from the call's slot on. -/
private theorem late_justified_not_in_call_epoch {anchor : Store preset fork} {Δ time : ℕ}
    {T : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ}
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (preGloas : fork < .glamsterdam) (fits : DelayFits fork config genesisTimeMs Δ)
    (windows : AssignmentWindowAgreement (e := e) time) (params : DirectSafety.Parameters preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time) {u : ValidatorIndex}
    (caller : u ∈ J) {n : ℕ}
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) {w : ValidatorIndex}
    (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode} (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root)
    {rootBlock : BeaconBlock preset fork} {current callSlot : Slot}
    (rootFound : ((e.world k).state w).blocks[root]? = some rootBlock)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (callSlotOk : ((e.world n).state u).getCurrentSlot config = .ok callSlot)
    (isLate : (computeEpochAtSlot preset rootBlock.slot).toNat + 1 <
      (computeEpochAtSlot preset current).toNat)
    (above : computeEpochAtSlot preset rootBlock.slot <
      ((e.world k).state w).justifiedCheckpoint.epoch)
    (notAfter : ((e.world k).state w).justifiedCheckpoint.epoch ≤
      computeEpochAtSlot preset callSlot) :
    False := by
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := params.roots
    omega
  have forwardOf := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore)
  have forwardW := forwardOf k w receiver
  have reachedW := forwardW.reachable
  have reachedU := (forwardOf n u caller).reachable
  have callerBound : (e.world n).time ≤ time := low.trans high
  have receiverBound : (e.world k).time ≤ time := atTime ▸ high
  have oneBlock := agree u caller w receiver n k callerBound receiverBound
  have slotEpochNat (slot : Slot) :
      (computeEpochAtSlot preset slot).toNat = slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  -- The caller holds the root, the same block.
  have headAbove := inputs.2.1
  obtain ⟨callerBlock, callerFound⟩ := Store.held_of_isAncestor headAbove
  have same := oneBlock root callerBlock rootBlock callerFound rootFound
  subst same
  obtain ⟨callSlot', callBegin, callSlotOk', callBeginOk, atCall⟩ := id atSlot
  have slotEq := Except.ok.inj (callSlotOk'.symm.trans callSlotOk)
  subst slotEq
  have callEpochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset callSlot') := by
    simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  -- The checked call: its epoch is at most one after the root's, and its tests.
  obtain ⟨cEpoch, cSlot, rEpoch, sEpoch, cEpochOk, cSlotOk, rEpochOk, sEpochOk, recent, tests⟩ :=
    inputs.1
  rw [callEpochOk, Except.ok.injEq] at cEpochOk
  subst cEpoch
  rw [callSlotOk, Except.ok.injEq] at cSlotOk
  subst cSlot
  have rEq : rEpoch = computeEpochAtSlot preset callerBlock.slot := by
    simpa [Store.getBlockEpoch, Store.block_ok_iff.mpr callerFound, bind, Except.bind, pure,
      Except.pure] using rEpochOk.symm
  subst rEq
  have callRecent := call_epoch_le_root_add_one inputs.1 walk callSlotOk callerFound
  -- So the receiver's justified epoch is the call's.
  have aboveNat := UInt64.lt_iff_toNat_lt.mp above
  have notAfterNat := UInt64.le_iff_toNat_le.mp notAfter
  have cpEpoch : ((e.world k).state w).justifiedCheckpoint.epoch =
      computeEpochAtSlot preset callSlot' := UInt64.toNat_inj.mp (by omega)
  have rootBefore : computeEpochAtSlot preset callerBlock.slot <
      computeEpochAtSlot preset callSlot' := cpEpoch ▸ above
  have anchorEpochEq : anchorEpoch = getCurrentEpoch anchorState := by
    obtain ⟨_, _, _, _, justified, _⟩ := getForkchoiceStore_anchor anchorStore
    rw [← anchorOk, justified]
  have afterAnchor : anchorEpoch < ((e.world k).state w).justifiedCheckpoint.epoch := by
    have le := UInt64.le_iff_toNat_le.mp
      (reachedU.anchorSlot_le (UInt64.le_of_eq anchorSlot) callerFound)
    have div := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) le
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [anchorEpochEq, getCurrentEpoch_toNat, ← anchorSlot]
    rw [slotEpochNat] at aboveNat
    omega
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.filterNodeTree_known tree
  -- A justified block above the root contradicts the strict descent.
  have close : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true →
      False := fun up =>
    strict (Store.eq_of_isAncestor_antisymm preGloas rootFound justifiedFound descends up)
  -- A read of the justified checkpoint on the caller's head above the root contradicts it too.
  have viaCaller (read : ((e.world n).state u).getCheckpointBlock head.root
      ((e.world k).state w).justifiedCheckpoint.epoch =
        .ok ((e.world k).state w).justifiedCheckpoint.root) : False := by
    have up := Store.isAncestor_of_getCheckpointBlock_above preGloas callerFound headAbove read
      (slot_le_of_epoch_lt positive above)
    exact close (Store.isAncestor_of_same_blocks reachedW preGloas oneBlock callerFound
      (reachedU.anchorSlot_le (UInt64.le_of_eq anchorSlot) callerFound)
      ⟨_, justifiedFound⟩ up)
  -- An honest vote for it from the call's slot on is cast on a head above the root.
  have viaDuty := fun {v} (honest : v ∈ J) {k' data} duty target after before =>
    let window := duty_window_of_slot_le (k' := k') (data := data) anchored fits callBeginOk
      receiver ready currentOk honest duty after before
    (justified_descends_of_duty anchorStore anchored anchorSlot anchorBoundary preGloas roots
      caller callerFound callerBound covers high receiver atTime ⟨_, justifiedFound⟩
      (slot_le_of_epoch_lt positive above) honest duty target (atCall.trans_le window.1)
      window.2).resolve_right (e.not_honestCollision_of_agree agree)
  -- The justification's own signer.
  obtain ⟨v, honest, i, -, m, sent, data, member, target, dataBefore⟩ :=
    signed w receiver k current (Nat.zero_le _) receiverBound ready currentOk afterAnchor
  obtain ⟨k', -, duty⟩ := e.exists_maySign_of_signed sent member honest
  obtain ⟨boundary, boundaryOk⟩ : ∃ boundary,
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset callSlot') = .ok boundary :=
    ⟨_, computeStartSlotAtEpoch_computeEpochAtSlot callSlot'⟩
  have dataEpoch : data.target.epoch = computeEpochAtSlot preset callSlot' := by
    rw [target, cpEpoch]
  -- At the epoch's first slot, the signer votes from the call's slot on.
  by_cases callAtStart : callSlot' ≤ boundary
  · exact close (viaDuty honest duty target
      (UInt64.le_trans callAtStart (boundary_le_of_duty duty (dataEpoch ▸ boundaryOk)))
      dataBefore)
  have offStart : isStartSlotAtEpoch preset callSlot' = .ok false := by
    unfold isStartSlotAtEpoch computeSlotsSinceEpochStart
    rw [boundaryOk]
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    apply decide_eq_false
    intro zero
    have below := UInt64.le_of_lt (UInt64.not_le.mp callAtStart)
    have eqNat := congrArg UInt64.toNat zero
    rw [UInt64.toNat_sub_of_le _ _ below] at eqNat
    exact callAtStart (UInt64.le_iff_toNat_le.mpr (by simpa using Nat.le_of_sub_eq_zero eqNat))
  -- Off the first slot, the no-conflict test passes with an honest count.
  have reservedN := inputs.2.2.1 callSlot' callSlotOk offStart
  have rootNe : computeEpochAtSlot preset callerBlock.slot ≠ computeEpochAtSlot preset callSlot' :=
    UInt64.ne_of_lt rootBefore
  have check : ((e.world n).state u).willNoConflictingCheckpointBeJustified config head.root =
      .ok true := by
    rcases tests with old | fresh
    · exact (old.2.2.2 offStart).1
    · exact (fresh.2.2 rootNe).2 offStart
  have cpHorizon : ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon :=
    UInt64.le_trans
      (forwardW.justified_epoch_le_current sound slots (UInt64.le_of_eq anchorSlot) epochOk).1
      (inHorizon w receiver k _ receiverBound epochOk)
  -- The call's unrealized justification as its target: the receiver has justified it.
  have viaUnrealized : ((e.world n).state u).getCurrentTarget config head.root =
      .ok ((e.world n).state u).unrealizedJustifiedCheckpoint → False := by
    intro targetOk
    obtain ⟨epoch', block, epochOk', readTarget, eq⟩ :=
      Store.getCurrentTarget_eq_ok_iff.mp targetOk
    cases Except.ok.inj (epochOk'.symm.trans callEpochOk)
    have sameCheckpoint := selected w receiver u caller k n receiverBound callerBound _ _
      (.inl rfl) (.inr rfl) (by rw [eq, cpEpoch]) cpHorizon
    rw [eq] at sameCheckpoint
    apply viaCaller
    rw [sameCheckpoint]
    exact readTarget
  -- The test reads the call's pulled-up state and target, and the target block's state.
  have nonzeroU := roots u caller n callerBound
  obtain ⟨target0, target0Ok, -⟩ := bind_ok_iff.mp check
  rcases (Store.willNoConflictingCheckpointBeJustified_eq_ok_true_iff target0Ok).mp check with
    same | ⟨state0, -, -, -, state0Ok, -⟩
  · exact viaUnrealized (same ▸ target0Ok)
  have read0 : ((e.world n).state u).getCheckpointBlock head.root target0.epoch =
      .ok target0.root := by
    obtain ⟨_, _, _, blockRead, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp target0Ok
    exact blockRead
  obtain ⟨-, block0, -, held0, -, -⟩ := Store.isAncestor_of_getCheckpointBlock read0
  obtain ⟨anc, ancStored, -⟩ := reachedU.blockStatesFromParents held0
  obtain ⟨fin, finRead, finAnchor⟩ :=
    Store.Reachable.finalizedState_of_blockState reachedU sound anchorSlot params nonzeroU ancStored
  -- The count with its pin reserve gives the pinned quorum.
  rcases quorum_of_no_conflicting_checkpoint (reservedN state0 anc fin target0 state0Ok target0Ok
      ancStored finRead finAnchor)
      check with targetOk |
    ⟨state, total, target', slot', first, last, participants, voters, stateOk, totalOk, targetOk',
      slotOk', targetEpochOk, firstOk, lastOk, participantsOk, read, members, large⟩
  · exact viaUnrealized targetOk
  have sameState := Except.ok.inj (stateOk.symm.trans state0Ok)
  have sameTarget := Except.ok.inj (targetOk'.symm.trans target0Ok)
  subst sameState sameTarget
  -- A counted honest third pins the receiver's justification.
  cases Except.ok.inj (slotOk'.symm.trans callSlotOk)
  have targetEpoch := Except.ok.inj (targetEpochOk.symm.trans callEpochOk)
  obtain ⟨v, voter, i, -, m, sent, data, member, dataTarget, dataBefore⟩ :=
    (pinned u caller n head.root state total _ voters callerBound ⟨head, headOk, rfl⟩
      stateOk totalOk callEpochOk target' anc fin targetOk' ancStored finRead finAnchor
      (fun v hv => ⟨(members v hv).1, (members v hv).2.1⟩) large w
      receiver k current (Nat.zero_le _) receiverBound ready currentOk cpEpoch
      (cpEpoch ▸ afterAnchor)).resolve_right (e.not_honestCollision_of_agree agree)
  obtain ⟨honest, -, signsOrUnseen⟩ := members v voter
  rcases signsOrUnseen with ⟨j, -, other, otherSent, otherData, otherSigned, otherTarget⟩ | unseen
  · -- The voter signed the call's target: one honest target per epoch.
    have sameData := e.data_eq_of_signed_of_target_epoch slots sent otherSent member otherSigned
      honest (by rw [dataTarget, otherTarget, cpEpoch, targetEpoch])
    apply viaCaller
    rw [← dataTarget, sameData, otherTarget]
    exact read
  · -- A voter unseen by the call votes from the call's slot on.
    obtain ⟨k'', -, duty'⟩ := e.exists_maySign_of_signed sent member honest
    have dutyCopy := duty'
    obtain ⟨index, assigned, -⟩ := dutyCopy
    have epochSlot : data.target.epoch = computeEpochAtSlot preset callSlot' := by
      rw [dataTarget, cpEpoch]
    have lowSlot := boundary_le_of_duty duty' (by rw [epochSlot]; exact firstOk)
    have after := duty_after_call anchorStore anchored positive (by omega) windows caller
      callerBound headOk callSlotOk firstOk lastOk participantsOk honest unseen lowSlot assigned
    exact close (viaDuty honest duty' dataTarget after dataBefore)

/-- A late receiver's justified checkpoint is at or before the root's epoch.

A checkpoint after the call's epoch has an honest signer with a duty after the call.

That duty puts the checkpoint above the root, against the strict descent. -/
private theorem late_justified_le_root {anchor : Store preset fork} {Δ time T : ℕ}
    {anchorEpoch horizon : Epoch} {margin : ℕ} (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (windows : AssignmentWindowAgreement (e := e) time) (params : DirectSafety.Parameters preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time) {u : ValidatorIndex}
    (caller : u ∈ J) {n : ℕ}
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) {w : ValidatorIndex}
    (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode} (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root)
    {rootBlock : BeaconBlock preset fork} {current : Slot}
    (rootFound : ((e.world k).state w).blocks[root]? = some rootBlock)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (isLate : (computeEpochAtSlot preset rootBlock.slot).toNat + 1 <
      (computeEpochAtSlot preset current).toNat) :
    ((e.world k).state w).justifiedCheckpoint.epoch ≤ computeEpochAtSlot preset rootBlock.slot := by
  by_contra notBelow
  have above := UInt64.not_le.mp notBelow
  have callerBound : (e.world n).time ≤ time := low.trans high
  have receiverBound : (e.world k).time ≤ time := atTime ▸ high
  obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := id atSlot
  by_cases afterCall : computeEpochAtSlot preset callSlot <
      ((e.world k).state w).justifiedCheckpoint.epoch
  swap
  · exact late_justified_not_in_call_epoch slots positive preGloas fits windows params ring
      anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon roots agree selected
      pinned signed caller atSlot headOk inputs walk low high covers receiver atTime ready tree
      descends strict
      rootFound currentOk callSlotOk isLate above
      (UInt64.not_lt.mp afterCall)
  -- The caller holds the root, the same block.
  obtain ⟨callerBlock, callerFound⟩ := Store.held_of_isAncestor inputs.2.1
  have same := agree u caller w receiver n k callerBound receiverBound root callerBlock
    rootBlock callerFound rootFound
  subst same
  -- The signer of the receiver's justified checkpoint.
  have callEpochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
  have anchorBefore := (inputs.2.2.2.2.2 _ callEpochOk).2
  have anchorEpochEq : anchorEpoch = getCurrentEpoch anchorState := by
    obtain ⟨_, _, _, _, justified, _⟩ := getForkchoiceStore_anchor anchorStore
    rw [← anchorOk, justified]
  obtain ⟨v, honest, i, -, m, sent, data, member, target, before⟩ := signed w receiver k current
    (Nat.zero_le _) receiverBound ready currentOk
    (by rw [anchorEpochEq]; exact UInt64.lt_trans anchorBefore afterCall)
  obtain ⟨k', -, duty⟩ := e.exists_maySign_of_signed sent member honest
  -- Its duty is in the justified epoch, after the call's, so after the call's slot.
  have after : callSlot ≤ data.slot := by
    obtain ⟨_, -, -, -, -, ⟨_, _, _, _, _, _, _, _, dataOk⟩, -⟩ := id duty
    have epochLt := UInt64.lt_iff_toNat_lt.mp (target ▸ afterCall)
    rw [target_epoch_eq_of_getAttestationData dataOk] at epochLt
    simp only [computeEpochAtSlot, UInt64.toNat_div] at epochLt
    exact UInt64.le_of_lt (UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_div_lt_div epochLt))
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.filterNodeTree_known tree
  obtain ⟨low', high'⟩ := duty_window_of_slot_le anchored fits callBeginOk receiver ready currentOk
    honest duty after before
  have up := (justified_descends_of_duty anchorStore anchored anchorSlot anchorBoundary preGloas
    roots caller callerFound callerBound covers high receiver atTime
    ⟨justifiedBlock, justifiedFound⟩ (slot_le_of_epoch_lt positive above) honest duty target
    (atCall.trans_le low') high').resolve_right (e.not_honestCollision_of_agree agree)
  exact strict (Store.eq_of_isAncestor_antisymm preGloas rootFound justifiedFound descends up)

/-! ## A late receiver of a root before the call's epoch -/

/-- A late receiver of a root before the call's epoch passes the justified test above the head.

The call's head realizes the root's epoch, and the receiver holds the head.

Each voting source above the head is then at least the receiver's justified epoch. -/
private theorem late_previous_receiver_source {anchor : Store preset fork} {Δ time : ℕ}
    {T : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ time)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (windows : AssignmentWindowAgreement (e := e) time) (params : DirectSafety.Parameters preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (anchorParent : AnchorParentAbsent (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (heldReads : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time →
      (e.world j).time ≤ time → ∀ (r : Root) (st : BeaconState preset fork),
      ((e.world j).state b).blockStates[r]? = some st →
      getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤ st.currentJustifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock st.currentJustifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
      .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (realized : AcceptedRealizedRecent ((e.world n).state u) (chain ++ [root]))
    (realizedHead : AcceptedRealizedHead ((e.world n).state u) config head.root (chain ++ [root]))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) {w : ValidatorIndex}
    (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode} (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root)
    {rootBlock : BeaconBlock preset fork} {current callSlot : Slot}
    (rootFound : ((e.world k).state w).blocks[root]? = some rootBlock)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (callSlotOk : ((e.world n).state u).getCurrentSlot config = .ok callSlot)
    (previous : computeEpochAtSlot preset rootBlock.slot < computeEpochAtSlot preset callSlot)
    (isLate : (computeEpochAtSlot preset rootBlock.slot).toNat + 1 <
      (computeEpochAtSlot preset current).toNat) :
    JustifiedTestAbove ((e.world k).state w) config root := by
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := params.roots
    omega
  have justifiedLe := late_justified_le_root slots positive preGloas fits windows params ring
      anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon roots agree selected
      pinned signed caller atSlot headOk inputs walk low high covers receiver atTime ready tree
      descends strict
      rootFound currentOk isLate
  -- The anchor store runs on the model's time of genesis.
  have anchorClock : anchor.genesisTimeMs = genesisTimeMs :=
    (getForkchoiceStore_timeMs anchorStore).1.trans anchorGenesis
  have forwardOf := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore)
  have forwardW := forwardOf k w receiver
  have reachedW := forwardW.reachable
  have reachedU := (forwardOf n u caller).reachable
  have callerBound : (e.world n).time ≤ time := low.trans high
  have receiverBound : (e.world k).time ≤ time := atTime ▸ high
  have oneBlock := agree u caller w receiver n k callerBound receiverBound
  have slotEpochNat (slot : Slot) :
      (computeEpochAtSlot preset slot).toNat = slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  -- The caller holds the root, the same block.
  have rootMem : root ∈ chain ++ [root] := by simp
  obtain ⟨callerBlock, callerState, callerFound, callerStored, rootRecent⟩ := realized root rootMem
  have same := oneBlock root callerBlock rootBlock callerFound rootFound
  subst same
  have callEpochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  -- The call's epoch is the one after the root's: the walk starts at most one epoch back.
  have callRecent := call_epoch_le_root_add_one inputs.1 walk callSlotOk callerFound
  -- The caller's head realized the root's epoch.
  obtain ⟨headState, headStored, headAbove, headRealized⟩ :=
    realizedHead root rootMem _ callerBlock callEpochOk callerFound previous
  obtain ⟨headBlock, headKnown, -⟩ := Store.slot_le_of_isAncestor callerFound headAbove
  -- The receiver's slot starts more than one delay after the call.
  have genesisOf := e.genesisTimeMs_eq_of_honest anchored (i := 0) receiver
    (by simpa [Execution.world_zero, World.initial, anchored w receiver] using anchorClock)
    receiver
  obtain ⟨currentBegin, currentBeginOk, currentBeginLe⟩ :=
    slotStart_le_clock (genesisOf k) currentOk (UInt64.le_refl _)
  rw [ready.1] at currentBeginLe
  obtain ⟨callSlot', callBegin, callSlotOk', callBeginOk, atCall⟩ := atSlot
  have slotEq := Except.ok.inj (callSlotOk'.symm.trans callSlotOk)
  subst slotEq
  have callBefore : callSlot' < current := by
    apply UInt64.lt_iff_toNat_lt.mpr
    by_contra notLt
    have mono := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) (Nat.le_of_not_lt notLt)
    rw [slotEpochNat, slotEpochNat] at isLate
    rw [slotEpochNat, slotEpochNat] at callRecent
    omega
  have delay := fits.start_add_lt_of_lt slots callBefore callBeginOk currentBeginOk
  -- The receiver's finality is held, as the anchor state's root is not zero.
  obtain ⟨anchorKey, -, anchorFound⟩ := reachedW.anchor_known
  have nonzero := roots w receiver k receiverBound anchorKey anchorBlock anchorFound
  have finalizedKnown := reachedW.finalized_known sound (UInt64.le_of_eq anchorSlot) positive
    window nonzero
  -- The caller's head reads the receiver's finality.
  have finalRead : ((e.world n).state u).getCheckpointBlock head.root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
    by_cases atAnchor : ((e.world k).state w).finalizedCheckpoint.epoch ≤
        getCurrentEpoch anchorState
    · obtain ⟨epochEq, rootHash⟩ := reachedW.finalized_eq_anchor_of_epoch_le atAnchor
      obtain ⟨anchorRoot, anchorHash, -⟩ := getForkchoiceStore_anchor anchorStore
      have rootEq := Except.ok.inj (anchorHash.symm.trans rootHash)
      rw [epochEq, ← rootEq]
      exact reachedU.getCheckpointBlock_anchor anchorSlot anchorBoundary
        (anchorParent u caller n callerBound) headKnown anchorHash
    have finalBelow := (reachedW.finalized_lt_justified_or_anchor sound).resolve_left atAnchor
    -- The root's realized justification is a selected checkpoint at or after the finality.
    obtain ⟨rootState, rootStored, -⟩ := reachedW.blockStatesFromParents rootFound
    have stateEq := e.blockStates_eq anchorStore caller receiver (anchored u caller)
      (anchored w receiver) oneBlock callerStored rootStored
    subst stateEq
    have finalNat := UInt64.lt_iff_toNat_lt.mp finalBelow
    have justifiedNat := UInt64.le_iff_toNat_le.mp justifiedLe
    have finalLe : ((e.world k).state w).finalizedCheckpoint.epoch ≤
        callerState.currentJustifiedCheckpoint.epoch :=
      UInt64.le_iff_toNat_le.mpr (by omega)
    have later : getCurrentEpoch anchorState < callerState.currentJustifiedCheckpoint.epoch :=
      UInt64.lt_of_lt_of_le (UInt64.not_le.mp atAnchor) finalLe
    have sliceRead := heldReads w receiver w receiver k k receiverBound receiverBound root
      callerState rootStored later finalLe
    have rootRead : ((e.world k).state w).getCheckpointBlock root
        callerState.currentJustifiedCheckpoint.epoch =
          .ok callerState.currentJustifiedCheckpoint.root := by
      rcases reachedW.getCheckpointBlock_of_blockState sound (UInt64.le_of_eq anchorSlot) positive
          window rootStored (.inl (by simp)) later with ⟨ok, -⟩ | zero
      · exact ok
      · rw [reachedW.anchorState_root, Except.ok.injEq] at zero
        exact absurd zero nonzero
    have composed := (Store.getCheckpointBlock_trans preGloas rootRead finalLe).trans sliceRead
    -- The read moves to the caller's store, and up to its head.
    have boundaryRead := composed
    unfold Store.getCheckpointBlock at boundaryRead
    obtain ⟨boundary, boundaryOk, -⟩ := bind_ok_iff.mp boundaryRead
    have boundaryOk := mapError_ok_iff.mp boundaryOk
    have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have anchorNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp atAnchor)
    rw [getCurrentEpoch_toNat] at anchorNat
    have aboveAnchor : anchorBlock.slot ≤ boundary := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [anchorSlot, boundaryNat]
      have split := Nat.lt_div_mul_add (a := anchorState.slot.toNat) positive
      have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (Nat.succ_le_of_lt anchorNat)
      rw [Nat.succ_mul] at mono
      omega
    have moved := Store.getCheckpointBlock_of_same_blocks reachedU
      (agree w receiver u caller k n receiverBound callerBound) boundaryOk aboveAnchor
      ⟨_, callerFound⟩ composed
    have below : boundary ≤ callerBlock.slot := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [boundaryNat]
      rw [slotEpochNat] at justifiedNat
      have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
        (show ((e.world k).state w).finalizedCheckpoint.epoch.toNat ≤
          callerBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat by omega)
      have back := Nat.div_mul_le_self callerBlock.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      omega
    exact Store.getCheckpointBlock_of_isAncestor (node := ⟨head.root, .pending⟩) preGloas
      callerFound headAbove boundaryOk below moved
  -- The receiver holds the head: the head was held more than one delay before.
  have late : max (e.world n).time 0 + Δ ≤ (e.world k).time := by
    rw [Nat.max_zero, atCall]
    omega
  obtain ⟨headHeld, -⟩ := (e.blocks_of_partiallySynchronous sync preGloas admitted anchorStore
    anchored caller receiver late receiverBound ready finalizedKnown headKnown
    finalRead).resolve_right (e.not_honestCollision_of_agree agree)
  have headAboveW := Store.isAncestor_of_same_blocks reachedW preGloas oneBlock callerFound
    (reachedU.anchorSlot_le (UInt64.le_of_eq anchorSlot) callerFound) ⟨_, headHeld⟩ headAbove
  obtain ⟨receiverHeadState, receiverHeadStored, -⟩ := reachedW.blockStatesFromParents headHeld
  have stateEq := e.blockStates_eq anchorStore caller receiver (anchored u caller)
    (anchored w receiver) oneBlock headStored receiverHeadStored
  subst stateEq
  -- Every tip above the head reads the receiver's justified epoch as its source.
  refine ⟨head.root, headBlock, headHeld, headAboveW, ?_⟩
  intro tip source epoch above _ sourceOk
  have lower := reachedW.realized_le_source sound (UInt64.le_of_eq anchorSlot) preGloas headHeld
      receiverHeadStored above
    sourceOk
  have anchorLower : getCurrentEpoch anchorState ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    obtain ⟨_, _, _, _, justified, _⟩ := getForkchoiceStore_anchor anchorStore
    have lower := (e.checkpointsAdvance_of_le w (Nat.zero_le k)).1.epoch_le
    simp only [Execution.world_zero, World.initial, anchored w receiver, justified] at lower
    exact lower
  have upper := forwardW.votingSource_le_justified sound positive slots anchorLower sourceOk
  have sameEpoch : source.epoch = ((e.world k).state w).justifiedCheckpoint.epoch :=
    UInt64.le_antisymm upper (UInt64.le_trans justifiedLe (UInt64.le_trans headRealized lower))
  exact .inr (.inl sameEpoch)

/-! ## A late receiver of a root of the call's epoch -/

/-- A late receiver of a root of the call's epoch passes the justified test above a seed.

The seed is a held block above the root that includes the honest votes for the call's target.

It lifts the voting source of each block above it to the receiver's justified epoch. -/
private theorem late_current_receiver_source {anchor : Store preset fork} {Δ time T : ℕ}
    {anchorEpoch horizon : Epoch} {margin : ℕ} (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    (votes : ValidatedDutyVotes (e := e) time) (windows : AssignmentWindowAgreement (e := e) time)
    (fit : config.CommitteeWindowsFit preset)
    (params : DirectSafety.Parameters preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (drift : QuorumDriftWithin (e := e) horizon time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (included : TargetIncluded (e := e) time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (rollover : CallRolloverRead (e := e) u n head.root time)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (startCovers : HonestHeadsCover (e := e) start (e.world n).time (time + 1))
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) {w : ValidatorIndex}
    (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode} (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root)
    {rootBlock : BeaconBlock preset fork} {current callSlot : Slot}
    (rootFound : ((e.world k).state w).blocks[root]? = some rootBlock)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (callSlotOk : ((e.world n).state u).getCurrentSlot config = .ok callSlot)
    (sameEpoch : computeEpochAtSlot preset rootBlock.slot = computeEpochAtSlot preset callSlot)
    (isLate : (computeEpochAtSlot preset rootBlock.slot).toNat + 1 <
      (computeEpochAtSlot preset current).toNat) :
    JustifiedTestAbove ((e.world k).state w) config root := by
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := params.roots
    omega
  have justifiedLe := late_justified_le_root slots positive preGloas fits windows params ring
      anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon roots agree selected
      pinned signed caller atSlot headOk inputs walk low high covers receiver atTime ready tree
      descends strict
    rootFound currentOk isLate
  have forwardOf : ∀ v ∈ J, ∀ i, Store.ForwardReachable config anchorState anchorBlock
      ((e.world i).state v) := fun v hv i =>
    e.forwardReachable (fun a ha => (anchored a ha) ▸ Store.ForwardReachable.anchor anchorStore)
      i v hv
  have callerBound : (e.world n).time ≤ time := low.trans high
  have receiverBound : (e.world k).time ≤ time := atTime ▸ high
  have reachedN := (forwardOf u caller n).reachable
  have forwardK := forwardOf w receiver k
  have reachedK := forwardK.reachable
  have heldOf {s : Store preset fork} {a b : Root}
      (h : s.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true) :
      ∃ block, s.blocks[b]? = some block :=
    Store.held_of_isAncestor h
  -- The caller holds the root, the same block as the receiver.
  obtain ⟨callerBlock, rootFoundN⟩ := heldOf inputs.2.1
  have sameRoot := agree u caller w receiver n k callerBound receiverBound root callerBlock
    rootBlock rootFoundN rootFound
  rw [sameRoot] at rootFoundN
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
  have rootEpochOkN : ((e.world n).state u).getBlockEpoch root =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr rootFoundN, sameEpoch, bind, Except.bind,
      pure, Except.pure]
  have callEpochs := inputs.2.2.2.2.2 _ epochOk
  have slotEpochNat (slot : Slot) :
      (computeEpochAtSlot preset slot).toNat = slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  have lateNat : (computeEpochAtSlot preset callSlot).toNat + 1 <
      (computeEpochAtSlot preset current).toNat := by
    rw [← sameEpoch]
    exact isLate
  -- At an epoch's first slot, the root is of an earlier epoch.
  by_cases atBoundary : isStartSlotAtEpoch preset callSlot = .ok false
  swap
  · exfalso
    have startTrue : isStartSlotAtEpoch preset callSlot = .ok true := by
      have first := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) callSlot
      unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at atBoundary ⊢
      rw [first] at atBoundary ⊢
      simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
        at atBoundary ⊢
      simpa using atBoundary
    exact inputs.2.2.2.2.1 callSlot _ _ callSlotOk startTrue epochOk rootEpochOkN rfl
  -- The call's slot and the next epoch's boundary start before the receiver's time.
  obtain ⟨callSlot', callBegin, callSlotOk', callBeginOk, atCall⟩ := id atSlot
  cases Except.ok.inj (callSlotOk'.symm.trans callSlotOk)
  have genesisK := e.genesisTimeMs_eq_of_honest anchored (i := 0) receiver
    (by simpa [Execution.world_zero, World.initial, anchored w receiver] using
      (getForkchoiceStore_timeMs anchorStore).1.trans anchorGenesis) receiver k
  obtain ⟨currentBegin, currentBeginOk, currentBeginLe⟩ :=
    slotStart_le_clock genesisK currentOk (UInt64.le_refl _)
  rw [ready.1, atTime] at currentBeginLe
  have callLt : callSlot < current := UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_div_lt_div
    (c := preset.SLOTS_PER_EPOCH.toNat) (by rw [← slotEpochNat, ← slotEpochNat]; omega))
  have callBefore := fits.start_add_lt_of_lt slots callLt callBeginOk currentBeginOk
  have callBeforeT : (e.world n).time < T := by omega
  obtain ⟨next, boundary, nextOk, boundaryOk, boundaryLt⟩ := exists_nextEpochStart_lt positive
      lateNat
  obtain ⟨begin, beginOk, -, -⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt boundaryLt) currentBeginOk
  have beginBefore := fits.start_add_lt_of_lt slots boundaryLt beginOk currentBeginOk
  have beginLe : begin.toNat ≤ time := by omega
  -- The record of the target check of the call's epoch.
  obtain ⟨readEpoch, readSlot, rootEpoch, startEpoch, readEpochOk, -, readRootOk, startEpochOk, -,
    branches⟩ := inputs.1
  cases Except.ok.inj (readEpochOk.symm.trans epochOk)
  cases Except.ok.inj (readRootOk.symm.trans rootEpochOkN)
  have record : ∃ q, q ≤ n ∧ ∃ (origin : Root) (headQ : ForkChoiceNode),
      UpToDate config checks sources (e.world q).time ((e.world q).view u) ((e.world q).state u) ∧
      (∃ slot begin, ((e.world q).state u).getCurrentSlot config = .ok slot ∧
        computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
        (e.world q).time = begin.toNat) ∧
      ((e.world q).state u).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset callSlot) ∧
      ((e.world q).state u).getHead config = .ok headQ ∧
      ((e.world q).state u).willCurrentTargetBeJustified config headQ.root = .ok true ∧
      ((e.world q).state u).isAncestor ⟨headQ.root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
      ReservedTargetVotes (e := e) margin u q headQ.root ∧
      ((e.world n).state u).getBlockEpoch origin = .ok (computeEpochAtSlot preset callSlot) ∧
      ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
      HonestHeadsCover (e := e) origin (e.world q).time ((e.world n).time + 1) := by
    rcases branches with old | currentBranch
    · exact absurd rfl old.2.1
    by_cases sameStart : startEpoch = computeEpochAtSlot preset callSlot
    swap
    -- The call itself checked the target.
    · exact ⟨n, le_rfl, root, head, upToDate, atSlot, epochOk, headOk,
        currentBranch.2.1 rfl sameStart, inputs.2.1, inputs.2.2.1 callSlot callSlotOk atBoundary,
        rootEpochOkN, Store.isAncestor_self (node := ⟨root, .pending⟩) rootFoundN,
        fun t lo hi => covers t lo (by omega)⟩
    -- The start's record serves for the root above it.
    subst sameStart
    obtain ⟨q, qLe, origin, -, originEpoch, startAbove, arm, originCover⟩ :=
      inputs.2.2.2.1 _ epochOk startEpochOk
    rcases arm with anchorOrigin | ⟨headQ, readyQ, epochQ, headQOk, checkQ, originBelow, countQ,
      atSlotQ⟩
    · exfalso
      obtain ⟨anchorKey, anchorHash, anchorKnown⟩ := reachedN.anchor_known
      obtain ⟨anchorRoot, rootHash, -, -, -, anchorFinal, -⟩ :=
        getForkchoiceStore_anchor anchorStore
      have sameKey := Except.ok.inj (anchorHash.symm.trans rootHash)
      subst sameKey
      simp only [anchorFinal] at anchorOrigin
      subst anchorOrigin
      simp only [Store.getBlockEpoch, Store.block_ok_iff.mpr anchorKnown, bind, Except.bind, pure,
        Except.pure, Except.ok.injEq] at originEpoch
      have after := callEpochs.2
      rw [← originEpoch, anchorSlot] at after
      exact absurd after (UInt64.lt_irrefl _)
    obtain ⟨originBlock, originFoundN⟩ := heldOf startAbove
    have pending : head = ⟨head.root, .pending⟩ := by
      rw [← Store.getHead_pending preGloas headOk]
    have startHead := startCovers (e.world n).time le_rfl (by omega) u caller n head rfl upToDate
      headOk
    rw [pending] at startHead
    obtain ⟨startBlock, startFound⟩ := heldOf startHead
    obtain ⟨rootRead, startRead, rootReadOk, startReadOk, slotLt⟩ :=
      Store.slot_lt_of_mem_getAncestorRoots (member := root) walk (by simp) (by simp)
    rw [Store.block_ok_iff, rootFoundN, Option.some.injEq] at rootReadOk
    rw [Store.block_ok_iff, startFound, Option.some.injEq] at startReadOk
    rw [← rootReadOk, ← startReadOk] at slotLt
    have rootWalk := Store.getAncestor_of_isAncestor_of_lt preGloas rootFoundN inputs.2.1
    have startWalk := Store.getAncestor_of_isAncestor_of_lt preGloas startFound startHead
    have through := Store.getAncestor_trans (UInt64.le_of_lt slotLt) rootWalk
    rw [startWalk] at through
    have rootAboveStart := Store.isAncestor_of_getAncestor through.symm
    exact ⟨q, qLe, origin, headQ, readyQ, atSlotQ, epochQ, headQOk, checkQ, originBelow, countQ,
      originEpoch, Store.isAncestor_trans_of_lt preGloas startFound originFoundN rootAboveStart
        startAbove, originCover⟩
  obtain ⟨q, qLe, origin, headQ, readyQ, atSlotQ, epochQ, headQOk, checkQ, originBelow, countQ,
    originEpochN, rootAboveOrigin, originCover⟩ := record
  have qBound : (e.world q).time ≤ time := (e.monotone_time qLe).trans callerBound
  have forwardQ := forwardOf u caller q
  have reachedQ := forwardQ.reachable
  have sameQN := agree u caller u caller q n qBound callerBound
  have sameQK := agree u caller w receiver q k qBound receiverBound
  have sameNK := agree u caller w receiver n k callerBound receiverBound
  -- The reads of the record's call: its pulled-up state, its target and the target's state.
  obtain ⟨pulled, -, support, -, -, pulledOk, -, supportOk, -, -, -⟩ :=
    Store.willCurrentTargetBeJustified_eq_ok_true_iff.mp checkQ
  obtain ⟨target, targetOk⟩ : ∃ target,
      ((e.world q).state u).getCurrentTarget config headQ.root = .ok target := by
    have score := supportOk
    unfold Store.computeHonestFfgSupportForCurrentTarget at score
    simp only [bind_ok_iff, mapError_ok_iff] at score
    obtain ⟨_, _, _, _, _, _, scoreValue, scoreOk, _⟩ := score
    unfold Store.getCurrentTargetScore at scoreOk
    obtain ⟨target, targetOk, _⟩ := bind_ok_iff.mp scoreOk
    exact ⟨target, targetOk⟩
  obtain ⟨tEpoch, tRoot, tEpochOk, tRead, targetEq⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
  have targetEpoch : target.epoch = computeEpochAtSlot preset callSlot := by
    rw [targetEq]
    exact Except.ok.inj (tEpochOk.symm.trans epochQ)
  have targetRead : ((e.world q).state u).getCheckpointBlock headQ.root target.epoch =
      .ok target.root := by
    rw [targetEq]
    exact tRead
  have targetNat := congrArg UInt64.toNat targetEpoch
  obtain ⟨-, targetBlock, -, targetHeld, -, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock targetRead
  obtain ⟨anc, ancStored, -⟩ := reachedQ.blockStatesFromParents targetHeld
  obtain ⟨fin, finRead, finAnchor⟩ :=
    Store.Reachable.finalizedState_of_blockState reachedQ sound anchorSlot params
      (roots u caller q qBound) ancStored
  have count := countQ pulled anc fin target pulledOk targetOk ancStored finRead finAnchor
  -- The origin is the same block at the record's call, at the call and at the receiver.
  obtain ⟨originBlock, originHeldQ⟩ := heldOf originBelow
  have originHeldN := e.blocks_of_le qLe originHeldQ
  have originEpochNat : computeEpochAtSlot preset originBlock.slot = target.epoch := by
    rw [targetEpoch]
    simpa [Store.getBlockEpoch, Store.block_ok_iff.mpr originHeldN, bind, Except.bind, pure,
      Except.pure] using originEpochN
  have originEpochQ : ((e.world q).state u).getBlockEpoch origin = .ok target.epoch := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr originHeldQ, originEpochNat, bind,
      Except.bind, pure, Except.pure]
  have rootAboveOriginK := Store.isAncestor_of_same_blocks reachedK preGloas sameNK originHeldN
    (reachedN.anchorSlot_le (UInt64.le_of_eq anchorSlot) originHeldN) ⟨_, rootFound⟩
    rootAboveOrigin
  obtain ⟨originBlockK, originHeldK⟩ := heldOf rootAboveOriginK
  have sameOrigin := sameQK origin originBlock originBlockK originHeldQ originHeldK
  rw [← sameOrigin] at originHeldK
  -- The origin stays covered from the record's call through the next boundary.
  have coverage : HonestHeadsCover (e := e) origin (e.world q).time (begin.toNat + 1) := by
    intro earlier lo hi a member i hd atI readyI hdOk
    by_cases early : earlier < (e.world n).time + 1
    · exact originCover earlier lo early a member i hd atI readyI hdOk
    have iBound : (e.world i).time ≤ time := by omega
    have aboveRoot := covers earlier (by omega) (by omega) a member i hd atI readyI hdOk
    have pendingHd : hd = ⟨hd.root, .pending⟩ := by
      rw [← Store.getHead_pending preGloas hdOk]
    rw [pendingHd] at aboveRoot ⊢
    obtain ⟨rootBlockI, rootHeldI⟩ := heldOf aboveRoot
    have copied := Store.isAncestor_of_same_blocks (forwardOf a member i).reachable preGloas
      (agree u caller a member n i callerBound iBound) originHeldN
      (reachedN.anchorSlot_le (UInt64.le_of_eq anchorSlot) originHeldN) ⟨_, rootHeldI⟩
      rootAboveOrigin
    obtain ⟨originBlockI, originHeldI⟩ := heldOf copied
    exact Store.isAncestor_trans_of_lt preGloas rootHeldI originHeldI aboveRoot copied
  -- The caller reads the same target, so the rollover read applies to it.
  have headAboveOrigin := Store.isAncestor_trans_of_lt preGloas rootFoundN originHeldN
    inputs.2.1 rootAboveOrigin
  have targetN : ((e.world n).state u).getCurrentTarget config head.root = .ok target :=
    Store.getCurrentTarget_eq_ok_iff.mpr ⟨target.epoch, target.root, targetEpoch ▸ epochOk,
      Store.getCheckpointBlock_of_shared_origin reachedQ reachedN anchorSlot sameQN preGloas
          targetRead originHeldQ
        originBelow originEpochNat headAboveOrigin, rfl⟩
  have nextOk' : addChecked target.epoch 1 = .ok next := targetEpoch ▸ nextOk
  have windowRead := rollover target next boundary begin targetN nextOk' boundaryOk beginOk beginLe
  -- The current-target step at the record's call names the honest voters of the target.
  obtain ⟨pulled', total, voters, pulledOk', totalOk, twoThirds, members⟩ :=
    (Execution.honestTargetVotes_signed_of_checked slots (by omega) preGloas fits prompt
      votes windows fit roots anchorStore anchorSlot anchorBoundary anchored caller readyQ
      atSlotQ headQOk checkQ count targetOk originEpochQ originBelow nextOk' boundaryOk beginOk
      beginLe coverage windowRead).resolve_right (e.not_honestCollision_of_agree agree)
  cases Except.ok.inj (pulledOk'.symm.trans pulledOk)
  -- Assumption 3: a seed above the root carries the voters' target votes.
  have receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have rootEpochK : ((e.world k).state w).getBlockEpoch root = .ok target.epoch := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr rootFound, sameEpoch, targetEpoch, bind,
      Except.bind, pure, Except.pure]
  have rootReadK := Store.getCheckpointBlock_of_shared_origin reachedQ reachedK anchorSlot sameQK
      preGloas targetRead
    originHeldQ originBelow originEpochNat rootAboveOriginK
  obtain ⟨seed, seedBlock, seedState, seedHeld, seedStored, seedAbove, seedLower, seedUpper,
      seedRead, seedVotes⟩ :=
    (included u caller q n qLe callerBound headQ pulled total target voters headQOk pulledOk
      targetOk totalOk (targetEpoch ▸ epochQ) (targetEpoch ▸ epochOk) (by omega) next boundary
      begin nextOk' boundaryOk beginOk (fun v hv => ⟨(members v hv).1, (members v hv).2.2⟩)
      w receiver k (computeEpochAtSlot preset current) receiverBound (by omega) ready
      receiverEpochOk (by omega) root target.epoch rootEpochK (UInt64.le_refl _) rootReadK
      (by rw [atTime]; exact covers)).resolve_right (e.not_honestCollision_of_agree agree)
  have seedSlot := reachedK.blockState_slot_eq anchorSlot seedHeld seedStored
  have seedEpochEq : getCurrentEpoch seedState = computeEpochAtSlot preset seedBlock.slot := by
    simp only [getCurrentEpoch, seedSlot]
  have seedLowerNat := UInt64.le_iff_toNat_le.mp seedLower
  have seedLate : computeEpochAtSlot preset seedBlock.slot < computeEpochAtSlot preset current :=
    UInt64.lt_iff_toNat_lt.mpr (by omega)
  have receiverHorizon := inHorizon w receiver k _ receiverBound receiverEpochOk
  have aboveOriginOf {P : Root}
      (above : ((e.world k).state w).isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true) :
      ((e.world k).state w).isAncestor ⟨P, .pending⟩ ⟨origin, .pending⟩ = .ok true :=
    Store.isAncestor_trans_of_lt preGloas seedHeld originHeldK above
      (Store.isAncestor_trans_of_lt preGloas rootFound originHeldK seedAbove rootAboveOriginK)
  -- The voters are active at the target epoch in each state above the seed.
  have active : ∀ (P : Root) (Ps : BeaconState preset fork),
      ((e.world k).state w).blockStates[P]? = some Ps →
      ((e.world k).state w).isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      ∀ v ∈ voters, v ∈ getActiveValidatorIndices Ps target.epoch := by
    intro P Ps stored above v member
    have eq := active_eq_of_common_origin anchorStore anchored anchorSlot preGloas caller
      receiver sameQK originHeldQ originHeldK pulledOk (Store.blockState_ok_iff.mpr stored)
      originBelow (aboveOriginOf above)
    rw [originEpochNat] at eq
    have pulledEpoch := forwardQ.pulledUpHeadState_epoch positive epochQ pulledOk
    have act := (members v member).2.1
    simp only [activeVoters, List.mem_toFinset, pulledEpoch] at act
    rw [← eq, targetEpoch]
    exact act
  -- A counted state above the seed weighs the voters at two thirds, unslashed.
  have quorum : ∀ (P : Root) (Ps W : BeaconState preset fork) (totalW : Gwei),
      ((e.world k).state w).blockStates[P]? = some Ps →
      ((e.world k).state w).isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      CountedState ((e.world k).state w) config W →
      (W = Ps ∨ ∃ slot, processSlots config checks Ps slot = .ok W) →
      getCurrentEpoch W = getCurrentEpoch seedState →
      getTotalActiveBalance W = .ok totalW →
      2 * totalW.toNat ≤ 3 * stake (fun v => balanceAt W v.toNat) voters ∧
        ∀ v ∈ voters, (slashedFlagAt W v.toNat).getD false = false := by
    intro P Ps W totalW stored above counted shape epochW totalWOk
    have clean : ∀ v ∈ voters, (slashedFlagAt W v.toNat).getD false = false := fun v member =>
      unslashed w receiver k W receiverBound counted v (members v member).1
    have checkRead := Store.getCheckpointBlock_of_shared_origin reachedQ reachedK anchorSlot sameQK
        preGloas targetRead
      originHeldQ originBelow originEpochNat (aboveOriginOf above)
    have epochWEq : getCurrentEpoch W = computeEpochAtSlot preset seedBlock.slot :=
      epochW.trans seedEpochEq
    have drifted := (drift u caller q headQ.root pulled anc target qBound pulledOk targetOk
      ancStored w receiver k P Ps W receiverBound stored checkRead shape
      (by rw [epochWEq]; exact seedLower) (by rw [epochWEq]; omega)
      (UInt64.le_trans (by rw [epochWEq]; exact UInt64.le_of_lt seedLate) receiverHorizon)
      voters totalW total (fun v member => ⟨(members v member).2.1, clean v member⟩) totalWOk
      totalOk).resolve_right (e.not_honestCollision_of_agree agree)
    have reserveLe := quorumReserve_le_pinReserve config pulled anc fin
    exact ⟨by omega, clean⟩
  have sourceLower := fun tip source above read =>
    includedVotes_votingSource_ge reachedK sound anchorSlot preGloas positive window (by omega)
        seedHeld
      seedStored
      (by rw [targetEpoch]; exact callEpochs.1) (by rw [targetEpoch]; exact callEpochs.2)
      seedLower seedUpper seedRead receiverEpochOk seedLate seedVotes active quorum tip source above
      read
  -- Every leaf above the seed votes from the receiver's justified epoch.
  refine ⟨seed, seedBlock, seedHeld, seedAbove, ?_⟩
  intro tip source epoch tipAbove _ sourceOk
  have lower := sourceLower tip source tipAbove sourceOk
  have anchorLower : getCurrentEpoch anchorState ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    obtain ⟨_, _, _, _, justified, _⟩ := getForkchoiceStore_anchor anchorStore
    have lowerJ := (e.checkpointsAdvance_of_le w (Nat.zero_le k)).1.epoch_le
    simp only [Execution.world_zero, World.initial, anchored w receiver, justified] at lowerJ
    exact lowerJ
  have upper := forwardK.votingSource_le_justified sound positive slots anchorLower sourceOk
  have jLe : ((e.world k).state w).justifiedCheckpoint.epoch ≤ target.epoch := by
    rw [targetEpoch, ← sameEpoch]
    exact justifiedLe
  have sourceEq : source.epoch = ((e.world k).state w).justifiedCheckpoint.epoch :=
    UInt64.le_antisymm upper (UInt64.le_trans jLe lower)
  exact .inr (.inl sourceEq)

/-! ## The root in the filtered tree -/

/-- An up-to-date honest receiver passes the justified test above the root. -/
private theorem receiver_source_above_root {anchor : Store preset fork} {Δ time T : ℕ}
    {anchorEpoch horizon : Epoch} {margin : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ time)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    (votes : ValidatedDutyVotes (e := e) time) (windows : AssignmentWindowAgreement (e := e) time)
    (fit : config.CommitteeWindowsFit preset)
    (params : DirectSafety.Parameters preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (anchorParent : AnchorParentAbsent (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (drift : QuorumDriftWithin (e := e) horizon time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (included : TargetIncluded (e := e) time)
    (heldReads : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time →
      (e.world j).time ≤ time → ∀ (r : Root) (st : BeaconState preset fork),
      ((e.world j).state b).blockStates[r]? = some st →
      getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤ st.currentJustifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock st.currentJustifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
      .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (rollover : CallRolloverRead (e := e) u n head.root time)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (realized : AcceptedRealizedRecent ((e.world n).state u) (chain ++ [root]))
    (realizedHead : AcceptedRealizedHead ((e.world n).state u) config head.root (chain ++ [root]))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (startCovers : HonestHeadsCover (e := e) start (e.world n).time (time + 1))
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) {w : ValidatorIndex}
    (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode} (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root) :
    JustifiedTestAbove ((e.world k).state w) config root := by
  have forward := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore)
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.filterNodeTree_known tree
  obtain ⟨rootBlock, rootFound, -⟩ := Store.slot_le_of_isAncestor justifiedFound descends
  obtain ⟨current, currentOk, -, -⟩ :=
    (forward k w receiver).slots_le_current slots (UInt64.le_of_eq anchorSlot)
  by_cases isEarly : (computeEpochAtSlot preset current).toNat ≤
      (computeEpochAtSlot preset rootBlock.slot).toNat + 1
  · exact early_receiver_source preGloas anchorStore sound anchorSlot anchored agree caller realized
      low high receiver atTime
      rootFound currentOk isEarly
  have isLate := Nat.lt_of_not_ge isEarly
  obtain ⟨callSlot, -, callSlotOk, -, -⟩ := id atSlot
  -- The caller holds the root, the same block, at or before its current slot.
  obtain ⟨callerBlock, callerFound⟩ := Store.held_of_isAncestor inputs.2.1
  have same := agree u caller w receiver n k (low.trans high) (atTime ▸ high) root callerBlock
    rootBlock callerFound rootFound
  subst same
  obtain ⟨readSlot, readSlotOk, blocksBelow, -⟩ :=
    (forward n u caller).slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have slotEq := Except.ok.inj (readSlotOk.symm.trans callSlotOk)
  subst slotEq
  have below := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
    (UInt64.le_iff_toNat_le.mp (blocksBelow root callerBlock callerFound))
  rcases Nat.lt_or_eq_of_le below with lt | eq
  · exact late_previous_receiver_source sync slots positive preGloas admitted fits windows params
      ring anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon roots
      anchorParent agree selected pinned signed anchorGenesis heldReads caller atSlot headOk inputs
      walk realized realizedHead low high covers receiver atTime ready tree descends strict
      rootFound currentOk readSlotOk
      (UInt64.lt_iff_toNat_lt.mpr (by simpa only [computeEpochAtSlot, UInt64.toNat_div] using lt))
      isLate
  · exact late_current_receiver_source slots positive preGloas fits prompt votes windows fit params
      ring anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon roots agree
      selected pinned signed drift unslashed anchorGenesis included caller upToDate atSlot
      headOk rollover inputs walk low high startCovers covers receiver atTime ready tree descends
      strict rootFound currentOk readSlotOk
      (UInt64.toNat_inj.mp (by simpa only [computeEpochAtSlot, UInt64.toNat_div] using eq))
      isLate

/-- Each block above the root reads the receiver's finalized checkpoint.

The root's realized justification is at or after that checkpoint, and it reads it. -/
private theorem finalized_read_above_root {anchor : Store preset fork} {Δ time T : ℕ}
    {anchorEpoch horizon : Epoch} {margin : ℕ} (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (windows : AssignmentWindowAgreement (e := e) time) (params : DirectSafety.Parameters preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (anchorParent : AnchorParentAbsent (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (heldReads : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time →
      (e.world j).time ≤ time → ∀ (r : Root) (st : BeaconState preset fork),
      ((e.world j).state b).blockStates[r]? = some st →
      getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤ st.currentJustifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock st.currentJustifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
      .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (realized : AcceptedRealizedRecent ((e.world n).state u) (chain ++ [root]))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) {w : ValidatorIndex}
    (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode} (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root) {tip : Root}
    (above : ((e.world k).state w).isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    ((e.world k).state w).getCheckpointBlock tip ((e.world k).state w).finalizedCheckpoint.epoch =
      .ok ((e.world k).state w).finalizedCheckpoint.root := by
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := params.roots
    omega
  have forward := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  have reached := forward.reachable
  have callerBound : (e.world n).time ≤ time := low.trans high
  have receiverBound : (e.world k).time ≤ time := atTime ▸ high
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.filterNodeTree_known tree
  obtain ⟨rootBlock, rootFound, -⟩ := Store.slot_le_of_isAncestor justifiedFound descends
  obtain ⟨tipBlock, tipFound, -⟩ := Store.slot_le_of_isAncestor rootFound above
  obtain ⟨anchorRoot, anchorHash, -⟩ := getForkchoiceStore_anchor anchorStore
  have unknown := anchorParent w receiver k receiverBound
  by_cases atAnchor : ((e.world k).state w).finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  -- Finality at the anchor's epoch is the anchor, which every held block reads.
  · obtain ⟨epochEq, rootHash⟩ := reached.finalized_eq_anchor_of_epoch_le atAnchor
    have rootEq := Except.ok.inj (anchorHash.symm.trans rootHash)
    rw [epochEq, ← rootEq]
    exact reached.getCheckpointBlock_anchor anchorSlot anchorBoundary unknown tipFound anchorHash
  -- A later finality is before the root's epoch.
  obtain ⟨current, currentOk, -, -⟩ := forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have below : ((e.world k).state w).finalizedCheckpoint.epoch.toNat + 1 ≤
      (computeEpochAtSlot preset rootBlock.slot).toNat := by
    by_cases isEarly : (computeEpochAtSlot preset current).toNat ≤
        (computeEpochAtSlot preset rootBlock.slot).toNat + 1
    · rcases forward.finalized_add_two_le_or_anchor sound slots epochOk with old | old
      · omega
      · exact absurd old atAnchor
    · have justifiedLe := UInt64.le_iff_toNat_le.mp (late_justified_le_root slots positive preGloas
        fits windows params ring anchorStore sound anchorSlot anchorBoundary anchored anchorOk
        inHorizon roots agree selected pinned signed caller atSlot headOk inputs walk low high
        covers receiver atTime ready tree descends strict rootFound currentOk (by omega))
      rcases reached.finalized_lt_justified_or_anchor sound with old | old
      · exact absurd old atAnchor
      · have := UInt64.lt_iff_toNat_lt.mp old
        omega
  -- The root's realized justification reads the finality, by the finality reads of held states.
  obtain ⟨callerBlock, callerState, callerFound, callerStored, recent⟩ :=
    realized root (by simp)
  have same := agree u caller w receiver n k callerBound receiverBound root callerBlock
    rootBlock callerFound rootFound
  subst same
  obtain ⟨state, stored, -⟩ := reached.blockStatesFromParents rootFound
  have stateEq := e.blockStates_eq anchorStore caller receiver (anchored u caller)
    (anchored w receiver) (agree u caller w receiver n k callerBound receiverBound)
    callerStored stored
  subst stateEq
  have finalLe : ((e.world k).state w).finalizedCheckpoint.epoch ≤
      callerState.currentJustifiedCheckpoint.epoch := UInt64.le_iff_toNat_le.mpr (by omega)
  have later : getCurrentEpoch anchorState < callerState.currentJustifiedCheckpoint.epoch :=
    UInt64.lt_of_lt_of_le (UInt64.not_le.mp atAnchor) finalLe
  have finalRead := heldReads w receiver w receiver k k receiverBound receiverBound root
    callerState stored later finalLe
  obtain ⟨anchorKey, -, anchorFound⟩ := reached.anchor_known
  have nonzero := roots w receiver k receiverBound anchorKey anchorBlock anchorFound
  rcases reached.getCheckpointBlock_of_blockState sound (UInt64.le_of_eq anchorSlot) positive
      window stored (.inl (by simp)) later with ⟨rootRead, -⟩ | zero
  swap
  · rw [reached.anchorState_root, Except.ok.injEq] at zero
    exact absurd zero nonzero
  obtain ⟨boundary, boundaryOk⟩ : ∃ boundary, computeStartSlotAtEpoch preset
      ((e.world k).state w).finalizedCheckpoint.epoch = .ok boundary := by
    have split := finalRead
    unfold Store.getCheckpointBlock at split
    obtain ⟨boundary, boundaryOk, -⟩ := bind_ok_iff.mp split
    exact ⟨boundary, mapError_ok_iff.mp boundaryOk⟩
  have boundaryLe : boundary ≤ callerBlock.slot := by
    have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have epochNat : (computeEpochAtSlot preset callerBlock.slot).toNat =
        callerBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
    rw [epochNat] at below
    have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat below
    have back := Nat.div_mul_le_self callerBlock.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    apply UInt64.le_iff_toNat_le.mpr
    rw [boundaryNat]
    rw [Nat.add_mul, Nat.one_mul] at mono
    omega
  exact Store.getCheckpointBlock_of_isAncestor preGloas rootFound above boundaryOk boundaryLe
    ((Store.getCheckpointBlock_trans preGloas rootRead finalLe).trans finalRead)

/-- The root is in the receiver's filtered tree, given the finality reads of held states.

A viable leaf above the block of the justified test keeps the root in the tree. -/
private theorem root_mem_filtered_of_reads {anchor : Store preset fork} {Δ time T : ℕ}
    {anchorEpoch horizon : Epoch} {margin : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ time)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    (votes : ValidatedDutyVotes (e := e) time) (windows : AssignmentWindowAgreement (e := e) time)
    (fit : config.CommitteeWindowsFit preset)
    (params : DirectSafety.Parameters preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (anchorParent : AnchorParentAbsent (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (drift : QuorumDriftWithin (e := e) horizon time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (included : TargetIncluded (e := e) time)
    (heldReads : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time →
      (e.world j).time ≤ time → ∀ (r : Root) (st : BeaconState preset fork),
      ((e.world j).state b).blockStates[r]? = some st →
      getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤ st.currentJustifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock st.currentJustifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
      .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (rollover : CallRolloverRead (e := e) u n head.root time)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (realized : AcceptedRealizedRecent ((e.world n).state u) (chain ++ [root]))
    (realizedHead : AcceptedRealizedHead ((e.world n).state u) config head.root (chain ++ [root]))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (startCovers : HonestHeadsCover (e := e) start (e.world n).time (time + 1))
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) {w : ValidatorIndex}
    (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode} (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root) :
    (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes := by
  have src := receiver_source_above_root sync slots positive preGloas admitted fits prompt votes
      windows fit params ring anchorStore sound anchorSlot anchorBoundary anchored anchorOk
      inHorizon roots anchorParent agree selected pinned signed drift unslashed anchorGenesis
      included heldReads caller upToDate atSlot headOk rollover inputs walk realized
      realizedHead low high startCovers covers receiver atTime ready tree descends strict
  obtain ⟨top, topBlock, topFound, topAbove, sourceOk⟩ := src
  have reached := e.reachable (fun v hv => (anchored v hv) ▸ Store.Reachable.anchor anchorStore)
    k w receiver
  have lower := reached.parentsBelow (UInt64.le_of_eq anchorSlot)
    (anchorParent w receiver k (atTime ▸ high))
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.filterNodeTree_known tree
  obtain ⟨rootBlock, rootFound, -⟩ := Store.slot_le_of_isAncestor justifiedFound descends
  have rootPath := (Store.isAncestor_iff (lower := lower) preGloas justifiedFound rfl
    descends).mp rfl
  have topPath := (Store.isAncestor_iff (lower := lower) preGloas rootFound rfl topAbove).mp rfl
  obtain ⟨leaf, leafBlock, leafFound, leafPath, ⟨verdict, read⟩, member⟩ :=
    Store.exists_leaf_above_mem_filterNodeTree (lower := lower) preGloas rootFound topFound
        rootPath topPath
      tree
  have leafTop := Store.isAncestor_of_blockTree_ancestor preGloas leafFound topFound
    leafPath
  have leafRoot := Store.isAncestor_of_blockTree_ancestor preGloas leafFound rootFound
    (topPath.trans leafPath)
  have reads := read
  unfold Store.isViableLeaf at reads
  obtain ⟨epoch, epochOk, reads⟩ := bind_ok_iff.mp reads
  obtain ⟨voting, votingOk, -⟩ := bind_ok_iff.mp reads
  apply member
  rw [read, Store.isViableLeaf_eq_true read epochOk votingOk (sourceOk leaf voting epoch leafTop
      epochOk
    votingOk) (.inr (finalized_read_above_root slots positive preGloas fits windows params ring
        anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon roots anchorParent
        agree selected pinned signed heldReads caller atSlot headOk inputs walk realized low high
        covers receiver atTime ready tree descends strict leafRoot))]

/-- At a time T, the confirmed root of a call is in the filtered tree of an honest store.

The store is up to date, and the root strictly descends from its justified block.

Otherwise two honest stores collide, or accountable-safety evidence holds. -/
theorem Execution.rootInFilteredTree_of_checked [DecidablePred (· ∈ J)]
    {anchor : Store preset fork} {Δ time T : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ}
    {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    (admitted : BlocksAdmitted e 0 Δ time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (votes : ValidatedDutyVotes (e := e) time)
    (windows : AssignmentWindowAgreement (e := e) time)
    (fit : config.CommitteeWindowsFit preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (anchorParent : AnchorParentAbsent (e := e) time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (drift : QuorumDriftWithin (e := e) horizon time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (floor : HeldTerminalStakeFloor (e := e) horizon time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (params : DirectSafety.Parameters preset) (genesis : Genesis config checks g)
    (upgrade : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (included : TargetIncluded (e := e) time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root} (headOk : ((e.world n).state u).getHead config = .ok head)
    (rollover : CallRolloverRead (e := e) u n head.root time)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      start root)
    (walk : ((e.world n).state u).getAncestorRoots head.root start = .ok (chain ++ root :: later))
    (realized : AcceptedRealizedRecent ((e.world n).state u) (chain ++ [root]))
    (realizedHead : AcceptedRealizedHead ((e.world n).state u) config head.root (chain ++ [root]))
    (low : (e.world n).time ≤ T) (high : T ≤ time)
    (startCovers : HonestHeadsCover (e := e) start (e.world n).time (time + 1))
    (covers : HonestHeadsCover (e := e) root (e.world n).time T)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {nodes : List ForkChoiceNode}
    (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true)
    (strict : root ≠ ((e.world k).state w).justifiedCheckpoint.root) :
    (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes ∨ HonestCollision (e := e) time ∨
      HeldStateFinalityEvidence (e := e) pre time ∨
        CrossStoreJustifiedEvidence (e := e) pre time := by
  have positive := fit.positive
  rcases e.blocksAgree_or_collision time with agree | collision
  swap
  · exact .inr (.inl collision)
  rcases e.selectedCheckpointsAgree_or_evidence anchorStore anchored anchorSlot roots anchorParent
      params genesis pre upgrade enough floor with selected | crossEvidence
  swap
  · exact .inr (.inr (.inr crossEvidence))
  rcases Execution.heldFinality_or_evidence pre anchorStore anchored sound anchorSlot
      anchorBoundary slots inHorizon roots anchorParent params genesis upgrade enough floor with
    heldReads | evidence
  · exact .inl (root_mem_filtered_of_reads sync slots positive preGloas admitted fits prompt votes
      windows fit params ring anchorStore sound anchorSlot anchorBoundary anchored anchorOk
      inHorizon roots anchorParent agree selected pinned signed drift unslashed anchorGenesis
      included heldReads caller upToDate atSlot headOk rollover inputs walk realized
      realizedHead low high startCovers covers receiver atTime ready tree descends strict)
  · exact .inr (.inr (.inl evidence))

end EthLib.Consensus.Models.Network
