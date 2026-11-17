module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.CheckpointConsistency
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification
import EthLib.Consensus.Proofs.ForkChoice.SiblingCap
import EthLib.Consensus.Proofs.Transition.ParticipationFlagsKept
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Root viability: the current target

An up-to-date honest store may accept the current-target test of the fast confirmation rule.

Honest validators then sign that target with two thirds of the active balance of its head state.

The honest count and the coverage of honest heads by a block of the epoch are assumed.

So is the caller's head at the start of the next epoch.
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

/-- The caller's head read at the start of the epoch after the target's.

At that time the caller's up-to-date store has a head.

An honest voter that has not voted by the call needs a duty in the target's epoch.

`AssignmentWindowAgreement` gives that duty only through the past window of an actual head.

This head read is assumed, and head totality of an honest store would discharge it.

The window of that head over the target's epoch then reads under `Config.CommitteeWindowsFit`. -/
def RolloverWindowRead (u : ValidatorIndex) (begin : ℕ) : Prop :=
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
    RolloverWindowRead (e := e) u begin.toNat

/-- Each accepted root has a recent realized justification in its own stored post-state.

This is an assumption on the run, entry 1 of the rule's spec changes. -/
def AcceptedRealizedRecent (store : Store preset fork) (roots : List Root) : Prop :=
  ∀ root ∈ roots, ∃ (block : BeaconBlock preset fork) (state : BeaconState preset fork),
    store.blocks[root]? = some block ∧ store.blockStates[root]? = some state ∧
    (computeEpochAtSlot preset block.slot).toNat ≤
      state.currentJustifiedCheckpoint.epoch.toNat + 1

/-- Each accepted root of an earlier epoch is realized as justified by the head's stored state.

This is an assumption on the run, entry 3 of the rule's spec changes. -/
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

So the votes for the target of E count by the end of E + 1, and receivers of E + 2 see them. -/
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
      ∃ (seed : Root) (seedBlock : BeaconBlock preset fork) (seedState : BeaconState preset fork),
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
                v ∈ indices)

/-- A successful pulled-up state read has the store's current epoch. -/
private theorem pulled_epoch {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {head : Root} {state : BeaconState preset fork} {epoch : Epoch}
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (stateOk : store.getPulledUpHeadState config head = .ok state) :
    getCurrentEpoch state = epoch := by
  have parsed := stateOk
  simp only [Store.getPulledUpHeadState, epochOk, bind_ok_iff] at parsed
  obtain ⟨raw, rawOk, readEpoch, readEpochOk, parsed⟩ := parsed
  cases Except.ok.inj readEpochOk
  split at parsed
  · obtain ⟨first, firstOk, processed⟩ := bind_ok_iff.mp parsed
    rw [getCurrentEpoch, (processSlots_slot (mapError_ok_iff.mp processed)).2]
    exact computeEpochAtSlot_computeStartSlotAtEpoch
      (UInt64.lt_iff_toNat_lt.mpr positive) (mapError_ok_iff.mp firstOk)
  · rename_i notOld
    have stateEq : raw = state := Except.ok.inj parsed
    subst state
    have epochRead := epochOk
    simp only [Store.getCurrentStoreEpoch, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at epochRead
    obtain ⟨current, currentOk, epochEq⟩ := epochRead
    have rawLe := headState_epoch_le forward currentOk rawOk
    rw [epochEq] at rawLe
    exact UInt64.le_antisymm (UInt64.le_iff_toNat_le.mpr rawLe) (UInt64.not_lt.mp notOld)

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

/-- A matching slot-start read bounds the genesis offset by one slot duration. -/
private theorem genesis_offset_of_slot_start {genesis actual : UInt64}
    {slot : Slot} {begin : UInt64}
    (slots : 0 < config.SLOT_DURATION_MS)
    (beginOk : computeTimeAtSlotMs config genesis slot = .ok begin)
    (slotOk : computeSlotAtTimeMs config actual begin = .ok slot) :
    actual.toNat ≤ genesis.toNat ∧
      genesis.toNat < actual.toNat + config.SLOT_DURATION_MS.toNat := by
  simp only [computeTimeAtSlotMs, bind_ok_iff] at beginOk
  obtain ⟨offset, offsetOk, summed⟩ := beginOk
  have offsetNat := (mulChecked_ok_iff.mp offsetOk).2
  have beginNat := (addChecked_ok_iff.mp summed).2
  simp only [computeSlotAtTimeMs, bind_ok_iff] at slotOk
  obtain ⟨elapsed, elapsedOk, divided⟩ := slotOk
  have elapsedNat := (subChecked_ok_iff.mp elapsedOk).2
  have elapsedBound := (subChecked_ok_iff.mp elapsedOk).1
  have quotient := (divChecked_ok_iff.mp divided).2
  have positive := UInt64.lt_iff_toNat_lt.mp slots
  have lower := Nat.div_mul_le_self elapsed.toNat config.SLOT_DURATION_MS.toNat
  have upper := Nat.lt_mul_div_succ elapsed.toNat positive
  rw [← quotient] at lower upper
  rw [Nat.mul_comm, Nat.add_mul, Nat.one_mul] at upper
  omega

/-- The same sub-slot genesis offset preserves the slot read at every slot start. -/
private theorem slot_at_start_of_genesis_offset {genesis actual : UInt64}
    {slot : Slot} {begin : UInt64}
    (slots : 0 < config.SLOT_DURATION_MS)
    (beginOk : computeTimeAtSlotMs config genesis slot = .ok begin)
    (offset : actual.toNat ≤ genesis.toNat ∧
      genesis.toNat < actual.toNat + config.SLOT_DURATION_MS.toNat) :
    computeSlotAtTimeMs config actual begin = .ok slot := by
  have parsed := beginOk
  simp only [computeTimeAtSlotMs, bind_ok_iff] at parsed
  obtain ⟨distance, distanceOk, summed⟩ := parsed
  have distanceNat := (mulChecked_ok_iff.mp distanceOk).2
  have beginNat := (addChecked_ok_iff.mp summed).2
  have low : actual ≤ begin := UInt64.le_iff_toNat_le.mpr (by omega)
  have elapsedNat : (begin - actual).toNat = begin.toNat - actual.toNat :=
    UInt64.toNat_sub_of_le _ _ low
  have quotient : (begin - actual).toNat / config.SLOT_DURATION_MS.toNat = slot.toNat := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega
  unfold computeSlotAtTimeMs
  rw [subChecked_ok_iff.mpr ⟨low, elapsedNat⟩]
  simp only [bind, Except.bind]
  exact divChecked_ok_iff.mpr ⟨by intro zero; simp [zero] at slots, quotient.symm⟩

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
  have originRead := descends
  unfold Store.isAncestor at originRead
  obtain ⟨otherOrigin, otherKnown, _⟩ := bind_ok_iff.mp originRead
  have otherKnown := Store.block_ok_iff.mp otherKnown
  obtain ⟨headState, headStateOk⟩ := headState_of_descends forwardK otherKnown
    (by rw [← nodeEq]; exact descends)
  have activeEq := active_eq_of_common_origin anchored start anchorSlot preGloas caller caller
    same originKnown otherKnown countRead headStateOk countDescends
    (by rw [← nodeEq]; exact descends)
  rw [originEpoch] at activeEq
  have stateEpoch := pulled_epoch forwardN positive epochOk countRead
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
      have le := headState_epoch_le forwardK.forwardReachable slotOk foundOk
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
    (agree : HonestBlocksAgree (e := e) time)
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
  have originRead := descendsV
  unfold Store.isAncestor at originRead
  obtain ⟨originBlockV, originKnownV, _⟩ := bind_ok_iff.mp originRead
  have originKnownV := Store.block_ok_iff.mp originKnownV
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

/-- An accepted current-target test has honest signers with two thirds of the active balance.

The caller is an up-to-date honest store at a slot start of the target's epoch E.

Its head passes the current-target test, and `HonestTargetVotes` names the honest count.

The block `origin` is of epoch E, and the head descends from it.

Every up-to-date honest head descends from `origin` from the call through the start of E + 1.

At the start of E + 1 the caller has a head, and `fit` lets it read its window over epoch E.

Then honest validators with two thirds of the pulled-up head state's active balance sign the target.

Three times their stake is at least twice that balance plus the `margin` of the count.

Each of them is active in that state, and sends that signature before the start of E + 1.

A counted voter that has not signed by the call has a duty in E at or after the call's slot. -/
theorem Execution.honestTargetVotes_signed_of_checked {anchor : Store preset fork} {Δ time : ℕ}
    {margin : ℕ} (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (votes : ValidatedDutyVotes (e := e) time)
    (windows : AssignmentWindowAgreement (e := e) time) (fit : config.CommitteeWindowsFit preset)
    (nonzero : HeldBlockStateRootsNonzero (e := e) time)
    (agree : HonestBlocksAgree (e := e) time)
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
    (rollover : RolloverWindowRead (e := e) u begin.toNat) :
    ∃ (state : BeaconState preset fork) (total : Gwei) (voters : Finset ValidatorIndex),
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state ∧
      getTotalActiveBalance state = .ok total ∧
      2 * total.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters ∧
      ∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧ SignsTarget e v target (begin.toNat - 1) := by
  obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := atSlotStart
  obtain ⟨state, total, target', slot, epochStart, lastCall, participants, voters, stateOk,
    totalOk, targetOk', slotOk, epochOk, epochStartOk, lastCallOk, participantsOk, -, members,
    bound⟩ := quorum_of_current_target count justified
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
  have targetRead : ((e.world n).state u).getCheckpointBlock head.root target.epoch =
      .ok target.root := by
    obtain ⟨epoch, root, _, read, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
    exact read
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

namespace EthLib.Consensus.Store

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {store : Store preset fork}
  {lower : store.ParentsBelow}

/-! ## A viable leaf above a block keeps the block in the filtered tree -/

/-- A path through the children that fork choice reads. -/
private inductive NodePath (store : Store preset fork) :
    ForkChoiceNode → ForkChoiceNode → Prop where
  | refl (node) : NodePath store node node
  | step {node child leaf children} : store.getNodeChildren node = .ok children →
      child ∈ children → NodePath store child leaf → NodePath store node leaf

/-- Child paths concatenate. -/
private theorem NodePath.trans {a b c : ForkChoiceNode} (ab : store.NodePath a b)
    (bc : store.NodePath b c) : store.NodePath a c := by
  induction ab with
  | refl => exact bc
  | step read mem _ ih => exact .step read mem (ih bc)

/-- Traversal succeeds along every child path, even when its result is empty. -/
private theorem NodePath.filterNodeTree {node leaf : ForkChoiceNode}
    (path : store.NodePath node leaf) {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes) :
    ∃ below, store.filterNodeTree config leaf = .ok below ∧ ∀ y ∈ below, y ∈ nodes := by
  induction path generalizing nodes with
  | refl => exact ⟨nodes, walk, fun _ h => h⟩
  | step childrenOk childMem _ ih =>
    obtain ⟨below, -, belowOk, lift⟩ := filterNodeTree_sub walk childrenOk childMem
    obtain ⟨result, resultOk, sub⟩ := ih belowOk
    exact ⟨result, resultOk, fun y hy => lift y (sub y hy)⟩

/-- A reached leaf has a successful viability read, whether it is viable or not. -/
private theorem NodePath.isViableLeaf_ok {node leaf : ForkChoiceNode}
    (path : store.NodePath node leaf) {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes)
    (terminal : store.getNodeChildren leaf = .ok []) :
    ∃ b, store.isViableLeaf config leaf = .ok b := by
  obtain ⟨below, belowOk, -⟩ := path.filterNodeTree walk
  obtain ⟨children, childrenOk, cases⟩ := filterNodeTree_cases belowOk
  rw [terminal, Except.ok.injEq] at childrenOk
  subst childrenOk
  rcases cases with ⟨-, b, read, -⟩ | ⟨ne, -⟩
  · exact ⟨b, read⟩
  · exact absurd rfl ne

/-- A viable leaf belongs to the filtered result of every start on its child path. -/
private theorem NodePath.mem_filterNodeTree {node leaf : ForkChoiceNode}
    (path : store.NodePath node leaf) {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes)
    (terminal : store.getNodeChildren leaf = .ok [])
    (viable : store.isViableLeaf config leaf = .ok true) : leaf ∈ nodes := by
  obtain ⟨below, belowOk, lift⟩ := path.filterNodeTree walk
  have result : below = [leaf] := by
    rw [Store.filterNodeTree, terminal] at belowOk
    simpa [viable, bind, Except.bind, pure, Except.pure] using belowOk.symm
  exact lift leaf (result ▸ List.mem_singleton_self leaf)

/-- Before Gloas, every ancestor relation between held roots gives a child path. -/
private theorem nodePath_of_ancestor (before : fork < .glamsterdam)
    {root leaf : Root} {block : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (above : (blockTree lower).Ancestor (some root) (some leaf)) :
    store.NodePath ⟨root, .pending⟩ ⟨leaf, .pending⟩ := by
  induction h : store.nodeRank ⟨root, .pending⟩ using Nat.strong_induction_on
      generalizing root block with
  | _ rank ih =>
  by_cases same : root = leaf
  · subst same
    exact .refl _
  obtain ⟨child, childOf, childAbove⟩ := above.exists_child (by simpa using same)
  cases child with
  | none => exact False.elim (childOf.1 rfl)
  | some child =>
    obtain ⟨childBlock, childFound, parent⟩ := blockTree_isChild_iff.mp childOf
    have childrenOk : ∃ children, store.getNodeChildren ⟨root, .pending⟩ = .ok children := by
      have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
      simp [getNodeChildren, later, pure, Except.pure]
    obtain ⟨children, childrenOk⟩ := childrenOk
    have childMem : (⟨child, .pending⟩ : ForkChoiceNode) ∈ children :=
      (mem_getNodeChildren before childrenOk).mpr ⟨rfl, childBlock, childFound, parent⟩
    have slots := UInt64.lt_iff_toNat_lt.mp
      (lower child childBlock block childFound (parent ▸ found))
    have bound := childBlock.slot.toNat_lt
    have rankLower : store.nodeRank ⟨child, .pending⟩ < store.nodeRank ⟨root, .pending⟩ := by
      simp only [nodeRank, childFound, found, ↓reduceIte]
      omega
    exact .step childrenOk childMem (ih _ (h ▸ rankLower) childFound childAbove rfl)

/-- A held block has a held leaf above it in the finite strict-slot tree, before Gloas. -/
private theorem exists_leaf_above (lower : store.ParentsBelow) (before : fork < .glamsterdam)
    {root : Root} {block : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block) :
    ∃ leaf leafBlock, store.blocks[leaf]? = some leafBlock ∧
      store.NodePath ⟨root, .pending⟩ ⟨leaf, .pending⟩ ∧
      store.getNodeChildren ⟨leaf, .pending⟩ = .ok [] := by
  induction h : store.nodeRank ⟨root, .pending⟩ using Nat.strong_induction_on
      generalizing root block with
  | _ rank ih =>
  have childrenOk : ∃ children, store.getNodeChildren ⟨root, .pending⟩ = .ok children := by
    have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    simp [getNodeChildren, later, pure, Except.pure]
  obtain ⟨children, childrenOk⟩ := childrenOk
  by_cases empty : children = []
  · exact ⟨root, block, found, .refl _, empty ▸ childrenOk⟩
  obtain ⟨child, childMem⟩ := List.exists_mem_of_ne_nil _ empty
  obtain ⟨pending, childBlock, childFound, parent⟩ :=
    (mem_getNodeChildren before childrenOk).mp childMem
  have slots := UInt64.lt_iff_toNat_lt.mp
    (lower child.root childBlock block childFound (parent ▸ found))
  have bound := childBlock.slot.toNat_lt
  have rankLower : store.nodeRank child < store.nodeRank ⟨root, .pending⟩ := by
    simp only [nodeRank, childFound, found, pending, ↓reduceIte]
    omega
  have childEq : child = ⟨child.root, .pending⟩ := by cases child; simp_all
  obtain ⟨leaf, leafBlock, leafFound, path, terminal⟩ :=
    ih _ (h ▸ (childEq ▸ rankLower)) childFound rfl
  exact ⟨leaf, leafBlock, leafFound, .step childrenOk childMem (childEq ▸ path), terminal⟩

/-- Before Gloas, a child path follows the strict-slot block tree. -/
private theorem NodePath.ancestor {node leaf : ForkChoiceNode} (path : store.NodePath node leaf)
    (before : fork < .glamsterdam) :
    (blockTree lower).Ancestor (some node.root) (some leaf.root) := by
  induction path with
  | refl => exact .refl _
  | step read mem _ ih =>
    obtain ⟨-, block, found, parent⟩ := (mem_getNodeChildren before read).mp mem
    exact (blockTree_isChild_iff.mpr ⟨block, found, parent⟩).ancestor.trans ih

/-- A viable leaf read above `top` keeps each block `mid` from the start to `top` in the result. -/
private theorem exists_leaf_above_through (before : fork < .glamsterdam) {start mid top : Root}
    {midBlock topBlock : BeaconBlock preset fork} {nodes : List ForkChoiceNode}
    (midFound : store.blocks[mid]? = some midBlock)
    (topFound : store.blocks[top]? = some topBlock)
    (below : (blockTree lower).Ancestor (some start) (some mid))
    (above : (blockTree lower).Ancestor (some mid) (some top))
    (walk : store.filterNodeTree config ⟨start, .pending⟩ = .ok nodes) :
    ∃ leaf leafBlock, store.blocks[leaf]? = some leafBlock ∧
      (blockTree lower).Ancestor (some top) (some leaf) ∧
      (∃ b, store.isViableLeaf config ⟨leaf, .pending⟩ = .ok b) ∧
      (store.isViableLeaf config ⟨leaf, .pending⟩ = .ok true →
        (⟨mid, .pending⟩ : ForkChoiceNode) ∈ nodes) := by
  obtain ⟨startBlock, startRead⟩ := filterNodeTree_known walk
  have toMid := nodePath_of_ancestor before startRead below
  have toTop := nodePath_of_ancestor before midFound above
  obtain ⟨leaf, leafBlock, leafRead, leafPath, terminal⟩ :=
    exists_leaf_above lower before topFound
  refine ⟨leaf, leafBlock, leafRead, leafPath.ancestor before, ?_, ?_⟩
  · exact (toMid.trans (toTop.trans leafPath)).isViableLeaf_ok walk terminal
  intro viable
  obtain ⟨result, resultOk, lift⟩ := toMid.filterNodeTree walk
  exact lift _ (filterNodeTree_self resultOk (List.ne_nil_of_mem
    ((toTop.trans leafPath).mem_filterNodeTree resultOk terminal viable)))

end EthLib.Consensus.Store

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Included target votes justify at an epoch boundary -/

/-- A validator is not slashed in a state, read through its slashed flag. -/
private def SeedNotSlashed (state : BeaconState preset fork) (v : ValidatorIndex) : Prop :=
  (slashedFlagAt state v.toNat).getD false = false

private theorem seed_recent_epoch_ne (state : BeaconState preset fork)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    getPreviousEpoch state ≠ getCurrentEpoch state := by
  have previous := getPreviousEpoch_toNat state
  have late : 1 < (getCurrentEpoch state).toNat := counted
  intro same
  have := congrArg UInt64.toNat same
  omega

/-- An active index that is not slashed reads an unslashed validator. -/
private theorem seed_validator_of_active {state : BeaconState preset fork} {epoch : Epoch}
    {v : ValidatorIndex} (active : v ∈ getActiveValidatorIndices state epoch)
    (clean : SeedNotSlashed state v) :
    ∃ validator, getValidator state v = .ok validator ∧ validator.slashed = false := by
  have found := Array.getElem?_eq_getElem (lt_size_of_mem_getActiveValidatorIndices active)
  exact ⟨_, getValidator_eq_ok_iff.mpr found,
    by simpa [SeedNotSlashed, slashedFlagAt, found] using clean⟩

private theorem seed_mem_target_indices {state : BeaconState preset fork}
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (altair : .altair ≤ fork) (recent : Bool) {indices : List ValidatorIndex}
    (read : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices)
    {v : ValidatorIndex}
    (active : v ∈ getActiveValidatorIndices state
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (clean : SeedNotSlashed state v)
    (flagged : TargetFlagAt (recentParticipation state altair recent) v.toNat) :
    v ∈ indices := by
  have ne := seed_recent_epoch_ne state counted
  have selected : (if recent then getCurrentEpoch state else getPreviousEpoch state) =
      getPreviousEpoch state ∨
      (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        getCurrentEpoch state := by cases recent <;> simp
  unfold getUnslashedParticipatingIndices at read
  dsimp only at read
  rw [ite_eq_left selected] at read
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
    obtain ⟨activeIndices, activeOk, entries, entriesOk, rfl⟩ := read
    obtain ⟨validator, validatorOk, unslashed⟩ := seed_validator_of_active active clean
    have member : v ∈ activeIndices :=
      (getActiveValidatorIndicesChecked_ok activeOk).symm ▸ active
    obtain ⟨entry, entryMem, entryOk⟩ := exists_mem_of_mapM_ok entriesOk member
    obtain ⟨flags, found, set⟩ := flagged
    have flagsEq : (if (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        getCurrentEpoch state then (state.currentEpochParticipation altair).data
        else (state.previousEpochParticipation altair).data)[v.toNat]? = some flags := by
      cases recent <;> simpa [recentParticipation, ne] using found
    simp only [flagsEq, validatorOk, set, unslashed, Bool.not_false, Bool.and_self,
      bind, Except.bind, Except.ok.injEq] at entryOk
    subst entry
    exact List.mem_map.mpr ⟨(v, true), List.mem_filter.mpr ⟨entryMem, rfl⟩, rfl⟩

private theorem seed_mem_pending_indices {state : BeaconState preset fork}
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (before : fork < .altair) (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (matching : getMatchingTargetAttestations state before
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations)
    (read : getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex}
    (active : v ∈ getActiveValidatorIndices state
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (clean : SeedNotSlashed state v)
    {pending : PendingAttestation preset} (member : pending ∈ recentPending state before recent)
    (target : pending.data.target.root = root) {signers : List ValidatorIndex}
    (signersOk : getPendingAttestingIndices state pending = .ok signers)
    (signed : v ∈ signers) : v ∈ indices := by
  have ne := seed_recent_epoch_ne state counted
  have sourceOk : getMatchingSourceAttestations state before
      (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        .ok (recentPending state before recent) := by
    cases recent <;> simp [getMatchingSourceAttestations, recentPending, ne, ensure]
  have listed : pending ∈ attestations := by
    simp only [getMatchingTargetAttestations, sourceOk, bind, Except.bind] at matching
    split at matching
    · rename_i empty
      have := Array.isEmpty_iff.mp empty
      rw [this] at member
      simp at member
    · simp only [rootOk, liftAccessor, Except.mapError,
        pure, Except.pure, Except.ok.injEq] at matching
      subst attestations
      exact Array.mem_filter.mpr ⟨member, by simpa using target⟩
  simp only [getUnslashedAttestingIndices, bind_ok_iff] at read
  obtain ⟨lists, listsOk, filtered⟩ := read
  obtain ⟨result, resultMem, resultOk⟩ := exists_mem_of_mapM_ok listsOk
    (Array.mem_toList_iff.mpr listed)
  have same := Except.ok.inj (signersOk.symm.trans resultOk)
  subst result
  have inSet : v ∈ sortedSet lists.flatten :=
    mem_sortedSet.mpr (List.mem_flatten.mpr ⟨signers, resultMem, signed⟩)
  have pass : (do return !(← getValidator state v).slashed) =
      (Except.ok true : Except AccessorError Bool) := by
    obtain ⟨validator, validatorOk, unslashed⟩ := seed_validator_of_active active clean
    simp [validatorOk, unslashed]
  exact mem_filterM_ok_of_test filtered inSet pass

private theorem seed_weighs_justifies {state after : BeaconState preset fork}
    {total previous current : Gwei}
    (weighed : weighJustificationAndFinalization state total previous current = .ok after)
    (recent : Bool)
    (quorum : 2 * total.toNat ≤ 3 * (if recent then current else previous).toNat) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at weighed
  obtain ⟨previousWeight, previousOk, threshold, thresholdOk, first, firstOk, currentWeight,
    currentOk, second, secondOk, _, _, _, _, _, _, _, _, rfl⟩ := weighed
  have thresholdEq := (mulChecked_ok_iff.mp thresholdOk).2
  have previousEq := (mulChecked_ok_iff.mp previousOk).2
  have currentEq := (mulChecked_ok_iff.mp currentOk).2
  have epochs := getPreviousEpoch_le state
  cases recent
  · have passed : threshold ≤ previousWeight := by
      simp only [UInt64.le_iff_toNat_le]
      simp only [Bool.false_eq_true, ↓reduceIte] at quorum
      simp only [UInt64.toNat_ofNat] at thresholdEq previousEq
      omega
    have firstEpoch := (justifyCheckpoint_ok firstOk).resolve_right
      (by simp [decide_eq_true passed])
    rcases justifyCheckpoint_ok secondOk with ⟨-, epoch, -⟩ | ⟨-, same⟩
    · simpa [epoch] using epochs
    · simp [same, firstEpoch.2.1]
  · have passed : threshold ≤ currentWeight := by
      simp only [UInt64.le_iff_toNat_le]
      simp only [↓reduceIte] at quorum
      simp only [UInt64.toNat_ofNat] at thresholdEq currentEq
      omega
    have secondEpoch := (justifyCheckpoint_ok secondOk).resolve_right
      (by simp [decide_eq_true passed])
    simp [secondEpoch.2.1]

/-- Included active, unslashed target voters with two thirds of the total justify their epoch. -/
private theorem seed_processJustificationAndFinalization_justifies
    {state after : BeaconState preset fork}
    (computed : processJustificationAndFinalization state = .ok after)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {voters : Finset ValidatorIndex} {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (quorum : 2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters)
    (voted : ∀ v ∈ voters,
      v ∈ getActiveValidatorIndices state
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      SeedNotSlashed state v ∧
      ((∃ altair : .altair ≤ fork,
          TargetFlagAt (recentParticipation state altair recent) v.toNat) ∨
        ∃ before : fork < .altair, ∃ pending ∈ recentPending state before recent,
          pending.data.target.root = root ∧
          ∃ indices, getPendingAttestingIndices state pending = .ok indices ∧ v ∈ indices)) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  have enough : ∀ (indices : List ValidatorIndex) (balance : Gwei),
      getTotalBalance state indices = .ok balance → voters ⊆ indices.toFinset →
      2 * total.toNat ≤ 3 * balance.toNat := by
    intro indices balance balanceOk subset
    have value := (getTotalBalance_ok_iff_stake.mp balanceOk).2.2
    have lower := stake_mono (w := fun v => balanceAt state v.toNat) subset
    omega
  have late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 := UInt64.not_le.mpr counted
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    simp only [processJustificationAndFinalizationAltair, late, ↓reduceIte, bind_ok_iff,
      liftAccessor_ok, totalOk, Except.ok.injEq, exists_eq_left'] at computed
    obtain ⟨previous, previousOk, current, currentOk, previousBalance, previousBalanceOk,
      currentBalance, currentBalanceOk, weighed⟩ := computed
    apply seed_weighs_justifies weighed recent
    have read : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) =
          .ok (if recent then current else previous) := by cases recent <;> assumption
    apply enough (if recent then current else previous) _ (by cases recent <;> assumption)
    intro v member
    obtain ⟨active, clean, flags | ⟨before, -⟩⟩ := voted v member
    · obtain ⟨_, flags⟩ := flags
      exact List.mem_toFinset.mpr
        (seed_mem_target_indices counted altair recent read active clean flags)
    · exact False.elim (Nat.not_lt_of_ge altair before)
  · rename_i notAltair
    simp only [bind_ok_iff, liftAccessor_ok, totalOk, Except.ok.injEq,
      exists_eq_left', getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, previousBalance,
      ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩, currentBalance,
      ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    apply seed_weighs_justifies weighed recent
    apply enough (if recent then currentIndices else previousIndices) _
      (by cases recent <;> assumption)
    intro v member
    obtain ⟨active, clean, voted⟩ := voted v member
    rcases voted with ⟨altair, -⟩ | ⟨before, pending, member, target, indices, read, signed⟩
    · exact absurd altair notAltair
    · exact List.mem_toFinset.mpr (seed_mem_pending_indices counted before recent rootOk
        (attestations := if recent then current else previous)
        (by cases recent <;> assumption) (by cases recent <;> assumption)
        active clean member target read signed)

/-- At the last slot, caching preserves the quorum that the epoch transition weighs. -/
private theorem seed_advanceSlot_justifies {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (advanced : advanceSlot config checks state = .ok after)
    (lastSlot : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {voters : Finset ValidatorIndex} {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (quorum : 2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters)
    (voted : ∀ v ∈ voters,
      v ∈ getActiveValidatorIndices state
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      SeedNotSlashed state v ∧
      ((∃ altair : .altair ≤ fork,
          TargetFlagAt (recentParticipation state altair recent) v.toNat) ∨
        ∃ before : fork < .altair, ∃ pending ∈ recentPending state before recent,
          pending.data.target.root = root ∧
          ∃ indices, getPendingAttestingIndices state pending = .ok indices ∧ v ∈ indices)) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advanced
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
  change _ ≤ epoched.currentJustifiedCheckpoint.epoch
  rw [frame.currentJustified]
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have current : getCurrentEpoch cached = getCurrentEpoch state := by rw [cachedEq]; rfl
  have previous : getPreviousEpoch cached = getPreviousEpoch state := by rw [cachedEq]; rfl
  have roots : getBlockRoot cached
      (if recent then getCurrentEpoch cached else getPreviousEpoch cached) = .ok root := by
    rw [current, previous, getBlockRoot_processSlot cachedOk
      (slot_lt_epoch_add_historical positive window (by cases recent <;> simp))]
    exact rootOk
  have totalEq : getTotalActiveBalance cached = getTotalActiveBalance state := by
    rw [cachedEq]; rfl
  have balanceEq : ∀ index, balanceAt cached index = balanceAt state index := by
    intro index; rw [cachedEq]; rfl
  have result := seed_processJustificationAndFinalization_justifies (voters := voters)
    justifiedOk (current.symm ▸ counted) recent roots (totalEq.trans totalOk) ?_ ?_
  · simpa [current, previous] using result
  · simpa only [balanceEq] using quorum
  · have activeEq : ∀ epoch, getActiveValidatorIndices cached epoch =
        getActiveValidatorIndices state epoch := by
      intro epoch
      rw [cachedEq]
      rfl
    have pendingEq : ∀ pending, getPendingAttestingIndices cached pending =
        getPendingAttestingIndices state pending := by
      intro pending
      rw [cachedEq]
      rfl
    intro v member
    obtain ⟨active, clean, flags | pending⟩ := voted v member
    · refine ⟨?_, ?_, .inl ?_⟩
      · rwa [current, previous, activeEq]
      · simpa [cachedEq, SeedNotSlashed, slashedFlagAt] using clean
      · simpa [cachedEq, recentParticipation] using flags
    · refine ⟨?_, ?_, .inr ?_⟩
      · rwa [current, previous, activeEq]
      · simpa [cachedEq, SeedNotSlashed, slashedFlagAt] using clean
      · obtain ⟨before, attestation, member, target, indices, read, signed⟩ := pending
        refine ⟨before, attestation, ?_, target, indices, ?_, signed⟩
        · simpa only [cachedEq, recentPending] using member
        · rw [pendingEq]
          exact read

/-- A weighing past the first two epochs reads the total active balance. -/
private theorem seed_total_of_justified {state after : BeaconState preset fork}
    (computed : processJustificationAndFinalization state = .ok after)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  rcases processJustificationAndFinalization_reads computed with ⟨early, -⟩ |
    ⟨-, _, _, total, _, _, _, _, totalOk, -⟩
  · exact absurd early (UInt64.not_le.mpr counted)
  · exact ⟨total, totalOk⟩

/-- The last slot of an epoch past the first two reads the total active balance. -/
private theorem seed_total_of_advance {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (advanced : advanceSlot config checks state = .ok after)
    (lastSlot : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, -⟩ := advanceSlot_ok advanced
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨justified, justifiedOk, -⟩ := processEpoch_frame epochedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have current : getCurrentEpoch cached = getCurrentEpoch state := by rw [cachedEq]; rfl
  obtain ⟨total, totalOk⟩ := seed_total_of_justified justifiedOk (current.symm ▸ counted)
  refine ⟨total, ?_⟩
  rw [cachedEq] at totalOk
  exact totalOk

/-! ## Votes kept inside an epoch -/

/-- The list of an epoch of a seed or the next one reads that epoch. -/
private theorem seed_list_epoch {state : BeaconState preset fork} {epoch : Epoch}
    (lower : epoch ≤ getCurrentEpoch state)
    (upper : (getCurrentEpoch state).toNat < epoch.toNat + 2) :
    (if decide (getCurrentEpoch state = epoch) then getCurrentEpoch state
      else getPreviousEpoch state) = epoch := by
  by_cases same : getCurrentEpoch state = epoch
  · simp [same]
  · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte]
    have lowerNat := UInt64.le_iff_toNat_le.mp lower
    have ne : (getCurrentEpoch state).toNat ≠ epoch.toNat :=
      fun eq => same (UInt64.toNat_inj.mp eq)
    apply UInt64.toNat_inj.mp
    rw [getPreviousEpoch_toNat]
    omega

/-- A slot strictly inside an epoch is not followed by a boundary. -/
private theorem seed_not_boundary {s e n : ℕ} (low : e * n ≤ s) (high : s + 1 < (e + 1) * n) :
    (s + 1) % n ≠ 0 := by
  intro zero
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero zero
  have h1 : n * e < n * k := by rw [← hk, Nat.mul_comm]; omega
  have h2 : n * k < n * (e + 1) := by rw [← hk, Nat.mul_comm]; exact high
  have := Nat.lt_of_mul_lt_mul_left h1
  have := Nat.lt_of_mul_lt_mul_left h2
  omega

/-- A slot that ends no epoch caches roots and moves on, with any signature checks. -/
private theorem seed_advanceSlot_inside {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after)
    (inside : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0) :
    (∀ other : SignatureChecks, advanceSlot config other state = .ok after) ∧
      (∀ altair current, recentParticipation after altair current =
        recentParticipation state altair current) ∧
      (∀ before current, recentPending after before current =
        recentPending state before current) := by
  have computed' := computed
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have notBoundary : ¬next % preset.SLOTS_PER_EPOCH = 0 := fun boundary =>
    inside (by simpa [UInt64.toNat_mod, sum] using congrArg UInt64.toNat boundary)
  have epochedEq : cached = epoched := by
    simpa [epochIfLast, notBoundary, pure, Except.pure] using epochedOk
  subst epochedEq
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  refine ⟨fun other => ?_, fun _ _ => by rw [cachedEq]; rfl,
    fun _ _ => by rw [cachedEq]; rfl⟩
  have epochOther : epochIfLast config other next cached = .ok cached := by
    simp [epochIfLast, notBoundary, pure, Except.pure]
  simp only [advanceSlot, bind_ok_iff] at computed' ⊢
  obtain ⟨next', nextOk, cached', cachedOk', epoched', -, done⟩ := computed'
  have same : cached' = cached := Except.ok.inj (cachedOk'.symm.trans cachedOk)
  subst same
  have nextSame : next' = next := by
    simp only [pure, Except.pure, Except.ok.injEq] at done
    have := congrArg BeaconState.slot done
    simpa using this
  subst nextSame
  exact ⟨next', nextOk, cached', cachedOk', cached', epochOther, rfl⟩

/-- Slots inside an epoch keep its recent root, target flags and pending attestations.

They give the same state with any signature checks. -/
private theorem seed_slots_keep {config : Config} {checks : SignatureChecks}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {epoch : Epoch} {root : Root} :
    ∀ {count : ℕ} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      state.slot.toNat + count <
        ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      (∀ other : SignatureChecks, advanceSlots config other count state = .ok after) ∧
      (RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current))
  | 0, state, after, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ => rfl, RunKept.refl _, rfl, fun _ read => read, fun _ _ _ _ flagged => flagged,
      fun _ _ _ member => member⟩
  | count + 1, state, after, computed, inside => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    have nextSlot := advanceSlot_slot nextOk
    have stateEpoch := getCurrentEpoch_toNat state
    have nextEpochNat := getCurrentEpoch_toNat next
    have low := Nat.div_mul_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [← stateEpoch] at low
    have same : getCurrentEpoch next = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [nextEpochNat, nextSlot]
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.add_mul, Nat.one_mul]
        rw [Nat.add_mul, Nat.one_mul] at inside
        omega
    have nextInside : next.slot.toNat + count <
        ((getCurrentEpoch next).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
      rw [same, nextSlot]
      omega
    obtain ⟨others, run, epochEq, roots, flags, pendings⟩ :=
      seed_slots_keep positive window (epoch := epoch) (root := root) rest nextInside
    have notLast := seed_not_boundary low (by omega)
    obtain ⟨nextOther, flagsEq, pendingEq⟩ := seed_advanceSlot_inside nextOk notLast
    have step := runKept_advanceSlot nextOk
    refine ⟨fun other => ?_, step.trans run, epochEq.trans same, fun near read => ?_, ?_, ?_⟩
    · simp only [advanceSlots, bind_ok_iff]
      exact ⟨next, nextOther other, others other⟩
    · apply roots (same ▸ near)
      apply getBlockRoot_advanceSlot nextOk read
      rw [Nat.add_mul, Nat.one_mul] at inside
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat near
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · intro altair current position within flagged
      exact flags altair current position (Nat.lt_of_lt_of_le within step.grows)
        (by rw [flagsEq]; exact flagged)
    · intro before current pending member
      exact pendings before current pending (by rw [pendingEq]; exact member)

/-- Before Altair, an attestation keeps each pending attestation of both epochs. -/
private theorem seed_processAttestation_keepsPending {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (before : fork < .altair)
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (current : Bool) {pending : PendingAttestation preset}
    (member : pending ∈ recentPending state before current) :
    pending ∈ recentPending after before current := by
  obtain ⟨_, _, _, _, _, recorded, _⟩ := processAttestation_records before computed
  obtain ⟨added, same⟩ := recordPendingAttestation_lists recorded
  generalize (attestation.data.target.epoch == getCurrentEpoch state) = target at added same
  by_cases here : current = target
  · subst here
    rw [added]
    exact Array.mem_push_of_mem _ member
  · have flipped : current = !target := by cases current <;> cases target <;> simp_all
    subst flipped
    rw [same]
    exact member

/-- A frame for pending attestations keeps both lists. -/
private theorem seed_pendingFrame_recentPending {first second : BeaconState preset fork}
    (frame : PendingFrame first second) (before : fork < .altair) (current : Bool) :
    recentPending second before current = recentPending first before current := by
  cases current <;> simp [recentPending, frame.previousPending, frame.currentPending]

/-- Before Altair, a block keeps each pending attestation of both epochs. -/
private theorem seed_processBlock_keepsPending {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    (before : fork < .altair) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (current : Bool) {pending : PendingAttestation preset}
    (member : pending ∈ recentPending state before current) :
    pending ∈ recentPending after before current := by
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  rw [seed_pendingFrame_recentPending tail before current]
  refine foldlM_ok_invariant (fun s => pending ∈ recentPending s before current)
    (fun _ _ _ holds ok => seed_processAttestation_keepsPending before ok current holds) ?_
    attested
  rw [seed_pendingFrame_recentPending head before current]
  exact member

/-- A block keeps the run, the epoch, each root, each target flag and each pending attestation. -/
private theorem seed_block_keep
    {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {state after : BeaconState preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    {epoch : Epoch} {root : Root} :
    RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current) := by
  have slotEq := processBlock_slot computed
  refine ⟨runKept_processBlock computed, by simp only [getCurrentEpoch, slotEq], ?_,
    fun altair current _ inside flagged =>
      TargetFlagAt.of_processBlock computed altair current inside flagged,
    fun before current _ member =>
      seed_processBlock_keepsPending before computed current member⟩
  intro _ read
  unfold getBlockRoot at read ⊢
  simpa only [getBlockRootAtSlot_congr slotEq (processBlock_blockRoots computed)] using read

/-- A state that keeps the seed's votes passes them on through a step that keeps them. -/
private theorem seed_kept_trans {seed state after : BeaconState preset fork}
    {epoch : Epoch} {root : Root} {recent : Bool}
    (near : (getCurrentEpoch seed).toNat ≤ epoch.toNat + 1)
    (kept : RunKept seed state ∧ getCurrentEpoch state = getCurrentEpoch seed ∧
      getBlockRoot state epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < seed.validators.data.size →
        TargetFlagAt (recentParticipation seed altair recent) position →
        TargetFlagAt (recentParticipation state altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending seed before recent,
        pending ∈ recentPending state before recent))
    (step : RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current)) :
    RunKept seed after ∧ getCurrentEpoch after = getCurrentEpoch seed ∧
      getBlockRoot after epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < seed.validators.data.size →
        TargetFlagAt (recentParticipation seed altair recent) position →
        TargetFlagAt (recentParticipation after altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending seed before recent,
        pending ∈ recentPending after before recent) := by
  obtain ⟨run, epochEq, read, flags, pendings⟩ := kept
  obtain ⟨run', epochEq', roots, flags', pendings'⟩ := step
  exact ⟨run.trans run', epochEq'.trans epochEq, roots (epochEq ▸ near) read,
    fun altair position inside flagged => flags' altair recent position
      (Nat.lt_of_lt_of_le inside run.grows) (flags altair position inside flagged),
    fun before pending member => pendings' before recent pending (pendings before pending member)⟩

/-! ## Pending attestations after the anchor epoch read their own epoch -/

/-- Each pending attestation of a list after the anchor epoch has that target epoch and slot. -/
private def SeedPending (anchorEpoch : Epoch) (state : BeaconState preset fork) : Prop :=
  ∀ (before : fork < .altair) (recent : Bool),
    anchorEpoch < (if recent then getCurrentEpoch state else getPreviousEpoch state) →
    ∀ pending ∈ recentPending state before recent,
      pending.data.target.epoch =
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch

private theorem seedPending_frame {anchorEpoch : Epoch} {state after : BeaconState preset fork}
    (holds : SeedPending anchorEpoch state) (frame : PendingFrame state after) :
    SeedPending anchorEpoch after := by
  have current : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previous : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  intro before recent later pending member
  rw [seed_pendingFrame_recentPending frame] at member
  rw [current, previous] at later ⊢
  exact holds before recent later pending member

private theorem seedPending_attestation {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (before : fork < .altair) (holds : SeedPending anchorEpoch state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    SeedPending anchorEpoch after := by
  have frame := voteFrame_processAttestation computed
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, currentEq]
  obtain ⟨recent, slotEpoch, -⟩ := processAttestation_checks before computed
  obtain ⟨pending, -, dataEq, -, -, recorded, -⟩ := processAttestation_records before computed
  obtain ⟨added, same⟩ := recordPendingAttestation_lists recorded
  intro before' current later other member
  rw [currentEq, previousEq] at later ⊢
  by_cases chosen : current = (attestation.data.target.epoch == getCurrentEpoch state)
  · rw [chosen, added] at member
    rcases Array.mem_push.mp member with old | rfl
    · rw [← chosen] at old
      exact holds before current later other old
    rw [dataEq]
    refine ⟨?_, slotEpoch.symm⟩
    cases current
    · have differ : attestation.data.target.epoch ≠ getCurrentEpoch state := by
        intro eq
        simp [eq] at chosen
      simpa using recent.resolve_right differ
    · simpa using (beq_iff_eq.mp chosen.symm)
  · have flipped : current = !(attestation.data.target.epoch == getCurrentEpoch state) := by
      revert chosen
      cases current <;> cases (attestation.data.target.epoch == getCurrentEpoch state) <;> simp
    rw [flipped, same, ← flipped] at member
    exact holds before current later other member

private theorem seedPending_block {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (holds : SeedPending anchorEpoch state)
    (computed : processBlock config checks engine state block = .ok after) :
    SeedPending anchorEpoch after := by
  intro before
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  refine seedPending_frame ?_ tail before
  exact foldlM_ok_invariant (fun s => SeedPending anchorEpoch s)
    (fun _ _ _ held ok => seedPending_attestation before held ok)
    (seedPending_frame holds head) attested

private theorem seedPending_advanceSlot {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    (holds : SeedPending anchorEpoch state)
    (computed : advanceSlot config checks state = .ok after) :
    SeedPending anchorEpoch after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedLists : ∀ before current, recentPending cached before current =
      recentPending state before current := by
    intro before current
    cases current <;> simp [recentPending, cachedEq]
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro before current later pending member
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    obtain ⟨rotated, emptied⟩ := processEpoch_pendingRotation before epochedOk
    cases current
    · have moved : recentPending { epoched with slot := next } before false =
          recentPending state before true := by
        rw [← cachedLists before true]
        simp [recentPending, rotated]
      rw [moved] at member
      have prior : anchorEpoch < getCurrentEpoch state := by
        simpa only [Bool.false_eq_true, ↓reduceIte, previousEq] using later
      obtain ⟨epoch, slot⟩ := holds before true (by simpa using prior) pending member
      refine ⟨?_, slot⟩
      simpa [previousEq] using epoch
    · simp [recentPending, emptied] at member
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } =
        getPreviousEpoch state := by
      unfold getPreviousEpoch
      rw [currentEq]
    have lists : recentPending { cached with slot := next } before current =
        recentPending state before current := cachedLists before current
    rw [lists] at member
    rw [currentEq, previousEq] at later ⊢
    exact holds before current later pending member

private theorem seedPending_stateTransition {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (holds : SeedPending anchorEpoch state) (sound : Invariant state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    SeedPending anchorEpoch after := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancing⟩ := slotsOk
  exact seedPending_block ((advanceSlots_invariant_of
    (fun s t => SeedPending anchorEpoch s → SeedPending anchorEpoch t) (fun _ kept => kept)
    (fun _ one two kept => two (one kept)) (fun _ ok kept => seedPending_advanceSlot kept ok)
    sound advancing).2.2 holds) blockOk

/-- Each held state of a reachable store reads its pending attestations at their own epoch.

This holds for the attestations after the anchor epoch. -/
private theorem Store.Reachable.seedPending {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    {root : Root} {state : BeaconState preset fork}
    (found : store.blockStates[root]? = some state) :
    SeedPending (getCurrentEpoch anchorState) state :=
  reachable.blockState_induction reachable.blockStatesFromParents
    (fun _ st => SeedPending (getCurrentEpoch anchorState) st)
    (fun _ _ _ recent later => by
      have bound := getPreviousEpoch_le anchorState
      cases recent <;> simp only [Bool.false_eq_true, ↓reduceIte] at later
      · exact (UInt64.not_lt.mpr bound later).elim
      · exact (UInt64.lt_irrefl _ later).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ parentHeld transition ih =>
      seedPending_stateTransition ih ((reachable.ordered sound).2 parentHeld) transition)
    found

namespace Models.Network

/-- Above a seed, each block state keeps its votes within that epoch, or has justified it.

The weighing at the last slot of the seed's epoch is the hypothesis `weigh`. -/
private theorem seed_carry {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {seed : ForkChoiceNode} {seedSlot : Slot} {seedState : BeaconState preset fork}
    (anchorBelow : anchorBlock.slot ≤ seedSlot)
    (seedStored : store.blockStates[seed.root]? = some seedState)
    {epoch : Epoch} {root : Root} {recent : Bool}
    (near : (getCurrentEpoch seedState).toNat ≤ epoch.toNat + 1)
    (seedRead : getBlockRoot seedState epoch = .ok root)
    (weigh : ∀ (parent : Root) (parentState state after : BeaconState preset fork)
        (child : Root) (childBlock : BeaconBlock preset fork) (other : SignatureChecks),
      store.blockStates[parent]? = some parentState →
      store.getAncestor ⟨parent, .pending⟩ seedSlot = .ok seed →
      store.blocks[child]? = some childBlock → childBlock.parentRoot = parent →
      getCurrentEpoch parentState = getCurrentEpoch seedState →
      (state = parentState ∨ ∃ slot, slot ≤ childBlock.slot ∧
        processSlots config checks parentState slot = .ok state) →
      (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
        getBlockRoot state epoch = .ok root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair recent) position →
          TargetFlagAt (recentParticipation state altair recent) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
          pending ∈ recentPending state before recent)) →
      advanceSlot config other state = .ok after →
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      epoch ≤ after.currentJustifiedCheckpoint.epoch)
    {node : ForkChoiceNode} {state : BeaconState preset fork}
    (held : store.blockStates[node.root]? = some state)
    (walk : store.getAncestor node seedSlot = .ok seed) :
    (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
      getBlockRoot state epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
        TargetFlagAt (recentParticipation seedState altair recent) position →
        TargetFlagAt (recentParticipation state altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
        pending ∈ recentPending state before recent)) ∨
      epoch ≤ state.currentJustifiedCheckpoint.epoch := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  by_cases low : block.slot ≤ seedSlot
  · rw [Store.getAncestor_of_le found low] at walk
    cases walk
    rw [held, Option.some.injEq] at seedStored
    subst seedStored
    exact .inl ⟨RunKept.refl _, rfl, seedRead, fun _ _ _ flagged => flagged,
      fun _ _ member => member⟩
  have other : block ≠ anchorBlock := fun same => low (same ▸ anchorBelow)
  obtain ⟨post, postOk, -, notAnchor⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  obtain ⟨parentState, blockChecks, engine, signed, -, message, parentHeld, transition⟩ :=
    notAnchor other
  rw [Store.getAncestor] at walk
  split at walk
  · simp_all
  rename_i b same
  rw [found, Option.some.injEq] at same
  subst b
  simp only [low, ↓reduceIte] at walk
  split at walk
  · simp [throw, throwThe, MonadExceptOf.throw] at walk
  rename_i parent parentFound
  split at walk
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at walk
  have parentInv := (reachable.ordered sound).2 parentHeld
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transition
  have slotBounds := stateTransition_slot transition
  rw [message] at slotsOk blockOk slotBounds
  have cjEq : state.currentJustifiedCheckpoint = advanced.currentJustifiedCheckpoint :=
    (frame_processBlock blockOk).currentJustified
  rcases seed_carry reachable sound preGloas positive window anchorBelow seedStored
      near seedRead weigh parentHeld walk with kept | justified
  swap
  · exact .inr (UInt64.le_trans justified
      (stateTransition_currentJustified_mono parentInv transition))
  have parentEpochNat := getCurrentEpoch_toNat parentState
  have parentHigh : parentState.slot.toNat <
      ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [parentEpochNat, Nat.add_mul, Nat.one_mul]
    have := Nat.lt_div_mul_add (a := parentState.slot.toNat) positive
    omega
  have blockAfter := UInt64.lt_iff_toNat_lt.mp slotBounds.1
  have blockFits := block.slot.toNat_lt
  by_cases inEpoch : block.slot.toNat <
      ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat
  · simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, advancedOk⟩ := slotsOk
    have slotsKeep := (seed_slots_keep positive window (epoch := epoch) (root := root)
      advancedOk (by omega)).2
    exact .inl (seed_kept_trans near (seed_kept_trans near kept slotsKeep)
      (seed_block_keep blockOk))
  obtain ⟨middle, middleShape, middleSlot, middleKept, middleRest⟩ : ∃ middle,
      (middle = parentState ∨ ∃ slot, slot ≤ block.slot ∧
        processSlots config checks parentState slot = .ok middle) ∧
      middle.slot.toNat + 1 =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ∧
      (RunKept seedState middle ∧ getCurrentEpoch middle = getCurrentEpoch seedState ∧
        getBlockRoot middle epoch = .ok root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair recent) position →
          TargetFlagAt (recentParticipation middle altair recent) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
          pending ∈ recentPending middle before recent)) ∧
      processSlots config blockChecks middle block.slot = .ok advanced := by
    by_cases atEnd : parentState.slot.toNat + 1 =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat
    · exact ⟨parentState, .inl rfl, atEnd, kept, slotsOk⟩
    have lastNat : (UInt64.ofNat (((getCurrentEpoch parentState).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat - 1)).toNat =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat - 1 := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨middle, firstOk, restOk⟩ := processSlots_split
      (UInt64.lt_iff_toNat_lt.mpr (by rw [lastNat]; omega))
      (UInt64.lt_iff_toNat_lt.mpr (by rw [lastNat]; omega)) slotsOk
    have middleSlot := (processSlots_slot firstOk).2
    have firstCopy := firstOk
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at firstCopy
    obtain ⟨u, lt, advancing⟩ := firstCopy
    obtain ⟨others, keep⟩ := seed_slots_keep positive window (epoch := epoch) (root := root)
      advancing (by rw [lastNat]; omega)
    have firstChecks : processSlots config checks parentState
        (UInt64.ofNat (((getCurrentEpoch parentState).toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat - 1)) = .ok middle := by
      simp only [processSlots, bind_ok_iff, ensure_ok_iff]
      exact ⟨u, lt, others checks⟩
    refine ⟨middle, .inr ⟨_, UInt64.le_iff_toNat_le.mpr (by rw [lastNat]; omega), firstChecks⟩,
      by rw [middleSlot, lastNat]; omega, seed_kept_trans near kept keep, restOk⟩
  have middleInv : Invariant middle := by
    rcases middleShape with same | ⟨_, _, ok⟩
    · exact same ▸ parentInv
    · exact (processSlots_invariant parentInv ok).1
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at middleRest
  obtain ⟨_, _, restAdvance⟩ := middleRest
  have countPos : block.slot.toNat - middle.slot.toNat =
      (block.slot.toNat - middle.slot.toNat - 1) + 1 := by omega
  rw [countPos] at restAdvance
  simp only [advanceSlots, bind_ok_iff] at restAdvance
  obtain ⟨next, nextOk, tail⟩ := restAdvance
  have justified := weigh _ parentState middle next node.root block blockChecks parentHeld
    (by rwa [Store.parentPayloadStatus_of_lt preGloas] at walk) found rfl kept.2.1
    middleShape middleKept nextOk (by rw [middleSlot]; exact Nat.mul_mod_left _ _)
  have nextInv := (advanceSlot_invariant middleInv nextOk).1
  rw [cjEq]
  exact .inr (UInt64.le_trans justified (advanceSlots_currentJustified_mono nextInv tail))
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transition
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A seed that holds the counted target votes lifts each voting source above it to the target.

The votes are included in the seed, or the seed has justified the target already.

Each counted state above the seed in its epoch weighs the voters at two thirds, unslashed. -/
private theorem seed_source_lower {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {seed : Root} {seedBlock : BeaconBlock preset fork} {seedState : BeaconState preset fork}
    (seedHeld : store.blocks[seed]? = some seedBlock)
    (seedStored : store.blockStates[seed]? = some seedState)
    {target : Checkpoint}
    (targetLate : GENESIS_EPOCH + 1 < target.epoch)
    (anchorBefore : getCurrentEpoch anchorState < target.epoch)
    (seedLower : target.epoch ≤ computeEpochAtSlot preset seedBlock.slot)
    (seedUpper : (computeEpochAtSlot preset seedBlock.slot).toNat < target.epoch.toNat + 2)
    (seedRead : getBlockRoot seedState target.epoch = .ok target.root)
    {voters : Finset ValidatorIndex}
    -- The store is past the seed's epoch, so a tip of the seed's epoch reads its pull-up.
    {current : Epoch} (storeEpoch : store.getCurrentStoreEpoch config = .ok current)
    (late : computeEpochAtSlot preset seedBlock.slot < current)
    (seedVotes : target.epoch ≤ seedState.currentJustifiedCheckpoint.epoch ∨
      (∃ altair : .altair ≤ fork, ∀ v ∈ voters,
        TargetFlagAt (recentParticipation seedState altair
          (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) v.toNat) ∨
      ∃ before : fork < .altair, ∀ v ∈ voters,
        ∃ pending ∈ recentPending seedState before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
          pending.data.target = target ∧
          ∃ indices, getPendingAttestingIndices seedState pending = .ok indices ∧ v ∈ indices)
    -- The voters are active at the target epoch in each block state above the seed.
    (active : ∀ (P : Root) (Ps : BeaconState preset fork), store.blockStates[P]? = some Ps →
      store.isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      ∀ v ∈ voters, v ∈ getActiveValidatorIndices Ps target.epoch)
    -- A counted state above the seed in its epoch weighs the voters at two thirds, unslashed.
    (quorum : ∀ (P : Root) (Ps W : BeaconState preset fork) (total : Gwei),
      store.blockStates[P]? = some Ps →
      store.isAncestor ⟨P, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      CountedState store config W →
      (W = Ps ∨ ∃ slot, processSlots config checks Ps slot = .ok W) →
      getCurrentEpoch W = getCurrentEpoch seedState →
      getTotalActiveBalance W = .ok total →
      2 * total.toNat ≤ 3 * stake (fun v => balanceAt W v.toNat) voters ∧
        ∀ v ∈ voters, (slashedFlagAt W v.toNat).getD false = false) :
    ∀ (tip : Root) (source : Checkpoint),
      store.isAncestor ⟨tip, .pending⟩ ⟨seed, .pending⟩ = .ok true →
      store.getVotingSource config tip = .ok source →
      target.epoch ≤ source.epoch := by
  intro tip source tipAbove sourceOk
  have realizedLeSource {root tip : Root} {block : BeaconBlock preset fork}
      {base : BeaconState preset fork} {source : Checkpoint}
      (held : store.blocks[root]? = some block) (stored : store.blockStates[root]? = some base)
      (above : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
      (read : store.getVotingSource config tip = .ok source) :
      base.currentJustifiedCheckpoint.epoch ≤ source.epoch :=
    reachable.realized_le_source sound (UInt64.le_of_eq anchorSlot) preGloas held stored above read
  rcases seedVotes with realizedSeed | seedVotes
  · exact UInt64.le_trans realizedSeed (realizedLeSource seedHeld seedStored tipAbove sourceOk)
  have seedEpochEq : getCurrentEpoch seedState = computeEpochAtSlot preset seedBlock.slot := by
    simp only [getCurrentEpoch,
      reachable.blockState_slot_eq anchorSlot seedHeld seedStored]
  have near : (getCurrentEpoch seedState).toNat ≤ target.epoch.toNat + 1 := by
    rw [seedEpochEq]
    omega
  have listEpoch : ∀ X : BeaconState preset fork,
      getCurrentEpoch X = computeEpochAtSlot preset seedBlock.slot →
      (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch) then getCurrentEpoch X
        else getPreviousEpoch X) = target.epoch := by
    intro X epochEq
    have list := seed_list_epoch (state := X) (by rw [epochEq]; exact seedLower)
      (by rw [epochEq]; exact seedUpper)
    rw [epochEq] at list ⊢
    exact list
  have seedSelf : store.isAncestor ⟨seed, .pending⟩ ⟨seed, .pending⟩ = .ok true :=
    Store.isAncestor_self (node := ⟨seed, .pending⟩) seedHeld
  -- A state that keeps the seed's votes and that the store counts can weigh them.
  have weighAt : ∀ (P : Root) (Ps W : BeaconState preset fork) (total : Gwei),
      store.blockStates[P]? = some Ps →
      store.getAncestor ⟨P, .pending⟩ seedBlock.slot = .ok ⟨seed, .pending⟩ →
      CountedState store config W →
      (W = Ps ∨ ∃ slot, processSlots config checks Ps slot = .ok W) →
      getCurrentEpoch Ps = getCurrentEpoch seedState →
      (RunKept seedState W ∧ getCurrentEpoch W = getCurrentEpoch seedState ∧
        getBlockRoot W target.epoch = .ok target.root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ),
          position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position →
          TargetFlagAt (recentParticipation W altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
          pending ∈ recentPending W before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)))) →
      getTotalActiveBalance W = .ok total →
      getBlockRoot W (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)
        then getCurrentEpoch W else getPreviousEpoch W) = .ok target.root ∧
      2 * total.toNat ≤ 3 * stake (fun v => balanceAt W v.toNat) voters ∧
      ∀ v ∈ voters,
        v ∈ getActiveValidatorIndices W
          (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)
            then getCurrentEpoch W else getPreviousEpoch W) ∧
        SeedNotSlashed W v ∧
        ((∃ altair : .altair ≤ fork, TargetFlagAt (recentParticipation W altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) v.toNat) ∨
          ∃ before : fork < .altair, ∃ pending ∈ recentPending W before
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
            pending.data.target.root = target.root ∧
            ∃ indices, getPendingAttestingIndices W pending = .ok indices ∧ v ∈ indices) := by
    intro P Ps W total stored walk counts shape epochP kept totalOk
    obtain ⟨run, epochW, readW, flagsW, pendingW⟩ := kept
    have epochSeed := epochW.trans seedEpochEq
    have list := listEpoch W epochSeed
    have aboveSeed := Store.isAncestor_of_getAncestor walk
    obtain ⟨enough, clean⟩ := quorum P Ps W total stored aboveSeed counts shape epochW totalOk
    have activeW : ∀ v ∈ voters, v ∈ getActiveValidatorIndices W target.epoch := by
      intro v member
      rcases shape with same | ⟨_, ok⟩
      · exact same ▸ active P Ps stored aboveSeed v member
      · rw [(runKept_processSlots ok).active.getActiveValidatorIndices_eq
          (UInt64.le_trans (by rw [epochP, seedEpochEq]; exact seedLower)
            (getCurrentEpoch_le_activityFixedEpoch Ps))]
        exact active P Ps stored aboveSeed v member
    have epochWNat : (getCurrentEpoch W).toNat ≤ target.epoch.toNat + 1 := by
      rw [epochSeed]
      omega
    refine ⟨by rw [list]; exact readW, enough,
      fun v member => ⟨by rw [list]; exact activeW v member, clean v member, ?_⟩⟩
    rcases seedVotes with ⟨altair, flags⟩ | ⟨before, pendings⟩
    · exact .inl ⟨altair, flagsW altair v.toNat (lt_size_of_mem_getActiveValidatorIndices
        (active seed seedState seedStored seedSelf v member)) (flags v member)⟩
    · obtain ⟨pending, pendingMember, pendingTarget, indices, indicesOk, mem⟩ :=
        pendings v member
      obtain ⟨-, slotEpoch⟩ := reachable.seedPending sound seedStored before
        (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))
        (by rw [listEpoch seedState seedEpochEq]; exact anchorBefore) pending pendingMember
      refine .inr ⟨before, pending, pendingW before pending pendingMember,
        by rw [pendingTarget], indices, ?_, mem⟩
      rw [run.getPendingAttestingIndices_eq retained
        (by rw [slotEpoch, pendingTarget, seedEpochEq]; exact seedLower)
        (by rw [slotEpoch, pendingTarget]; exact epochWNat)]
      exact indicesOk
  -- The last slot of the seed's epoch justifies the target.
  have weigh : ∀ (parent : Root) (parentState state after : BeaconState preset fork)
      (child : Root) (childBlock : BeaconBlock preset fork) (other : SignatureChecks),
      store.blockStates[parent]? = some parentState →
      store.getAncestor ⟨parent, .pending⟩ seedBlock.slot = .ok ⟨seed, .pending⟩ →
      store.blocks[child]? = some childBlock → childBlock.parentRoot = parent →
      getCurrentEpoch parentState = getCurrentEpoch seedState →
      (state = parentState ∨ ∃ slot, slot ≤ childBlock.slot ∧
        processSlots config checks parentState slot = .ok state) →
      (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
        getBlockRoot state target.epoch = .ok target.root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ),
          position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position →
          TargetFlagAt (recentParticipation state altair
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
          pending ∈ recentPending state before
            (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)))) →
      advanceSlot config other state = .ok after →
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      target.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
    intro parent parentState state after child childBlock other stored walk childHeld
      childParent epochP shape kept advanced lastSlot
    have epochSeed := kept.2.1.trans seedEpochEq
    have counted : GENESIS_EPOCH + 1 < getCurrentEpoch state :=
      UInt64.lt_of_lt_of_le targetLate (by rw [epochSeed]; exact seedLower)
    obtain ⟨total, totalOk⟩ := seed_total_of_advance advanced lastSlot counted
    obtain ⟨rootOk, enough, votedW⟩ := weighAt parent parentState state total stored walk
      ⟨parent, parentState, stored, shape.imp_right fun ⟨slot, le, ok⟩ =>
        ⟨checks, slot, child, childBlock, childHeld, childParent, le, ok⟩⟩
      (shape.imp_right fun ⟨slot, _, ok⟩ => ⟨slot, ok⟩) epochP kept totalOk
    have result := seed_advanceSlot_justifies positive window advanced lastSlot counted _ rootOk
      totalOk enough votedW
    rwa [listEpoch state epochSeed] at result
  -- The tip keeps the seed's votes, or has justified the target.
  have tipWalk := Store.getAncestor_of_isAncestor_of_lt preGloas seedHeld tipAbove
  have voting := sourceOk
  unfold Store.getVotingSource at voting
  simp only [bind_ok_iff] at voting
  obtain ⟨tipBlock, tipRead, tipEpoch, tipEpochOk, voting⟩ := voting
  have tipKnown := Store.block_ok_iff.mp tipRead
  obtain ⟨tipState, tipStored, -⟩ := reachable.blockStatesFromParents tipKnown
  have anchorBelow : anchorBlock.slot ≤ seedBlock.slot :=
    reachable.anchorSlot_le (UInt64.le_of_eq anchorSlot) seedHeld
  rcases seed_carry reachable sound preGloas positive window
      (seed := ⟨seed, .pending⟩) anchorBelow seedStored near seedRead weigh
      (node := ⟨tip, .pending⟩) tipStored tipWalk with kept | justified
  swap
  · exact UInt64.le_trans justified (realizedLeSource tipKnown tipStored
      (Store.isAncestor_self (node := ⟨tip, .pending⟩) tipKnown) sourceOk)
  -- The tip is of the seed's epoch, so its source is its pull-up, which weighs the votes.
  have tipEpochState := kept.2.1.trans seedEpochEq
  have tipSlot := reachable.blockState_slot_eq anchorSlot tipKnown tipStored
  have epochSame := Except.ok.inj (tipEpochOk.symm.trans storeEpoch)
  subst tipEpoch
  have tipEarly : computeEpochAtSlot preset tipBlock.slot < current := by
    have eq : computeEpochAtSlot preset tipBlock.slot = getCurrentEpoch tipState := by
      simp only [getCurrentEpoch, tipSlot]
    rw [eq, tipEpochState]
    exact late
  simp only [tipEarly, ↓reduceIte] at voting
  cases entry : store.unrealizedJustifications[tip]? with
  | none => simp [entry, throw, throwThe, MonadExceptOf.throw] at voting
  | some checkpoint =>
    simp only [entry, pure, Except.pure, Except.ok.injEq] at voting
    subst source
    rcases reachable.unrealizedJustification_origin entry with ⟨-, held⟩ |
      ⟨st, pulled, held, run, same⟩
    · rw [tipStored, Option.some.injEq] at held
      rw [held] at tipEpochState
      rw [tipEpochState] at anchorBefore
      exact absurd seedLower (UInt64.not_le.mpr anchorBefore)
    · rw [tipStored, Option.some.injEq] at held
      subst st
      have counted : GENESIS_EPOCH + 1 < getCurrentEpoch tipState :=
        UInt64.lt_of_lt_of_le targetLate (by rw [tipEpochState]; exact seedLower)
      obtain ⟨total, totalOk⟩ := seed_total_of_justified run counted
      obtain ⟨rootOk, enough, votedW⟩ := weighAt tip tipState tipState total tipStored
        tipWalk ⟨tip, tipState, tipStored, .inl rfl⟩ (.inl rfl) kept.2.1 kept totalOk
      have result := seed_processJustificationAndFinalization_justifies run counted _ rootOk
        totalOk enough votedW
      rw [listEpoch tipState tipEpochState] at result
      rw [same]
      exact result

end Models.Network

end EthLib.Consensus

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-! ## Voting sources and viable leaves -/

/-- A voting source of a forward-reachable store is no later than its justified checkpoint. -/
private theorem votingSource_le_justified
    {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : 0 < config.SLOT_DURATION_MS)
    (anchorLower : getCurrentEpoch anchorState ≤ store.justifiedCheckpoint.epoch)
    {tip : Root} {source : Checkpoint}
    (read : store.getVotingSource config tip = .ok source) :
    source.epoch ≤ store.justifiedCheckpoint.epoch := by
  have reached := forward.reachable
  unfold Store.getVotingSource at read
  simp only [bind_ok_iff] at read
  obtain ⟨block, blockOk, current, currentOk, read⟩ := read
  split at read
  · rename_i older
    cases entry : store.unrealizedJustifications[tip]? with
    | none => simp [entry] at read
    | some value =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at read
      subst source
      rcases (reached.unrealizedJustification_origin entry).imp And.left id with anchorEpoch |
        ⟨state, pulled, held, run, same⟩
      · rw [anchorEpoch]
        exact anchorLower
      · rw [same]
        have epochRead := currentOk
        unfold Store.getCurrentStoreEpoch at epochRead
        obtain ⟨slot, slotOk, epochEq⟩ := bind_ok_iff.mp epochRead
        simp only [pure, Except.pure, Except.ok.injEq] at epochEq
        subst epochEq
        exact forward.justified_le_of_pulledUp sound positive slots slotOk
          (Store.block_ok_iff.mp blockOk) held run older
  · cases held : store.blockStates[tip]? with
    | none => simp [held] at read
    | some state =>
      simp only [held, pure, Except.pure, Except.ok.injEq] at read
      subst source
      exact reached.justified_le_of_blockState sound held

/-- The viability read of a leaf is `true` from its two checks.

The read is known to succeed, so the numeric arm does not overflow. -/
private theorem isViableLeaf_true {store : Store preset fork} {leaf : Root} {verdict : Bool}
    {epoch : Epoch} {source : Checkpoint}
    (read : store.isViableLeaf config ⟨leaf, .pending⟩ = .ok verdict)
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (sourceOk : store.getVotingSource config leaf = .ok source)
    (justified : store.justifiedCheckpoint.epoch = GENESIS_EPOCH ∨
      source.epoch = store.justifiedCheckpoint.epoch ∨ epoch.toNat ≤ source.epoch.toNat + 2)
    (finalized : store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
      store.getCheckpointBlock leaf store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root) :
    verdict = true := by
  unfold Store.isViableLeaf at read
  simp only [epochOk, sourceOk, bind, Except.bind] at read
  have finalTrue : ∀ fb, store.getCheckpointBlock leaf store.finalizedCheckpoint.epoch = .ok fb →
      (decide (store.finalizedCheckpoint.epoch = GENESIS_EPOCH) ||
        decide (store.finalizedCheckpoint.root = fb)) = true := by
    intro fb fbOk
    rcases finalized with genesis | finalRead
    · simp [genesis]
    · rw [finalRead, Except.ok.injEq] at fbOk
      simp [fbOk]
  by_cases shortcut : store.justifiedCheckpoint.epoch = GENESIS_EPOCH ∨
      source.epoch = store.justifiedCheckpoint.epoch
  · simp only [shortcut, ↓reduceIte, pure, Except.pure] at read
    cases fin : store.getCheckpointBlock leaf store.finalizedCheckpoint.epoch with
    | error err => simp [fin] at read
    | ok fb =>
      simp only [fin, Except.ok.injEq] at read
      rw [← read, finalTrue fb fin]
      rfl
  · have recent : epoch.toNat ≤ source.epoch.toNat + 2 := by
      rcases justified with h | h | h
      · exact absurd (.inl h) shortcut
      · exact absurd (.inr h) shortcut
      · exact h
    simp only [shortcut, ↓reduceIte] at read
    cases addition : addChecked source.epoch 2 with
    | error err => simp [addition, Except.mapError] at read
    | ok bound =>
      have boundValue := (addChecked_ok_iff.mp addition).2
      change bound.toNat = source.epoch.toNat + 2 at boundValue
      have within : epoch ≤ bound := UInt64.le_iff_toNat_le.mpr (by omega)
      cases fin : store.getCheckpointBlock leaf store.finalizedCheckpoint.epoch with
      | error err =>
        simp [addition, fin, Except.mapError, pure, Except.pure] at read
      | ok fb =>
        simp only [addition, fin, Except.mapError, pure, Except.pure, Except.ok.injEq] at read
        rw [← read, finalTrue fb fin]
        simp [within]

/-! ## The justified test above the root -/

/-- A held block above a root, each of whose descendants passes the justified test of fork choice.

That test is the justified half of `isViableLeaf`. -/
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
    (anchored : ∀ w ∈ J, e.start w = anchor) (agree : HonestBlocksAgree (e := e) time)
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

/-- A slot of an earlier epoch is before the first slot of a later epoch. -/
private theorem slot_le_of_epoch_lt (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {slot : Slot}
    {epoch : Epoch} (earlier : computeEpochAtSlot preset slot < epoch) :
    slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  have lt := UInt64.lt_iff_toNat_lt.mp earlier
  simp only [computeEpochAtSlot, UInt64.toNat_div] at lt
  have := (Nat.div_lt_iff_lt_mul positive).mp lt
  omega

/-- A checkpoint read on a head above a block, at an epoch after the block's, is above the block. -/
private theorem above_of_read {store : Store preset fork} (before : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {head root checkpoint : Root}
    {rootBlock : BeaconBlock preset fork} {epoch : Epoch}
    (rootKnown : store.blocks[root]? = some rootBlock)
    (supports : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (read : store.getCheckpointBlock head epoch = .ok checkpoint)
    (later : computeEpochAtSlot preset rootBlock.slot < epoch) :
    store.isAncestor ⟨checkpoint, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  have rootWalk := Store.getAncestor_of_isAncestor_of_lt before rootKnown supports
  have split := read
  unfold Store.getCheckpointBlock at split
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at split
  obtain ⟨boundary, boundaryOk, reached, boundaryWalk, reachedRoot⟩ := split
  have boundaryOk := mapError_ok_iff.mp boundaryOk
  have blockBelow : rootBlock.slot ≤ boundary := by
    have startNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have lt := UInt64.lt_iff_toNat_lt.mp later
    simp only [computeEpochAtSlot, UInt64.toNat_div] at lt
    have := (Nat.div_lt_iff_lt_mul positive).mp lt
    apply UInt64.le_iff_toNat_le.mpr
    rw [startNat]
    omega
  have reachedPending := Store.getAncestor_pending_of_lt before rfl boundaryWalk
  have reachedEq : reached = ⟨checkpoint, .pending⟩ := by
    obtain ⟨r, s⟩ := reached
    simp only at reachedRoot reachedPending
    rw [reachedRoot, reachedPending]
  rw [reachedEq] at boundaryWalk
  have through := Store.getAncestor_trans blockBelow boundaryWalk
  rw [rootWalk] at through
  exact Store.isAncestor_of_getAncestor through.symm

/-- Two blocks above each other are the same block, before Gloas. -/
private theorem eq_of_isAncestor_antisymm {store : Store preset fork} (before : fork < .glamsterdam)
    {a b : Root} {aBlock bBlock : BeaconBlock preset fork}
    (aFound : store.blocks[a]? = some aBlock) (bFound : store.blocks[b]? = some bBlock)
    (up : store.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true)
    (down : store.isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true) : a = b := by
  obtain ⟨aBlock', aFound', le⟩ := Store.slot_le_of_isAncestor bFound up
  rw [aFound, Option.some.injEq] at aFound'
  subst aBlock'
  obtain ⟨bBlock', bFound', ge⟩ := Store.slot_le_of_isAncestor aFound down
  rw [bFound, Option.some.injEq] at bFound'
  subst bBlock'
  have walk := Store.getAncestor_of_isAncestor_of_lt before bFound up
  rw [Store.getAncestor_of_le aFound ge, Except.ok.injEq] at walk
  exact congrArg ForkChoiceNode.root walk

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
    (roots : HeldBlockStateRootsNonzero (e := e) time) (agree : HonestBlocksAgree (e := e) time)
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
  have rootRead := headAbove
  unfold Store.isAncestor at rootRead
  obtain ⟨callerBlock, callerOk, -⟩ := bind_ok_iff.mp rootRead
  have callerFound := Store.block_ok_iff.mp callerOk
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
  have callRecent : (computeEpochAtSlot preset callSlot').toNat ≤
      (computeEpochAtSlot preset callerBlock.slot).toNat + 1 := by
    obtain ⟨b, t, bOk, tOk, lt⟩ := Store.slot_lt_of_mem_getAncestorRoots walk (by simp)
      (show root ∈ chain ++ root :: later by simp)
    rw [Store.block_ok_iff.mpr callerFound, Except.ok.injEq] at bOk
    subst bOk
    have sEq : sEpoch = computeEpochAtSlot preset t.slot := by
      simpa [Store.getBlockEpoch, tOk, bind, Except.bind, pure, Except.pure] using sEpochOk.symm
    subst sEq
    have mono := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lt))
    rw [slotEpochNat] at recent ⊢
    rw [slotEpochNat] at recent ⊢
    omega
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
    strict (eq_of_isAncestor_antisymm preGloas rootFound justifiedFound descends up)
  -- A read of the justified checkpoint on the caller's head above the root contradicts it too.
  have viaCaller (read : ((e.world n).state u).getCheckpointBlock head.root
      ((e.world k).state w).justifiedCheckpoint.epoch =
        .ok ((e.world k).state w).justifiedCheckpoint.root) : False := by
    have up := above_of_read preGloas positive callerFound headAbove read above
    exact close (Store.isAncestor_of_same_blocks reachedW preGloas oneBlock callerFound
      (reachedU.anchorSlot_le (UInt64.le_of_eq anchorSlot) callerFound)
      ⟨_, justifiedFound⟩ up)
  -- An honest vote for it from the call's slot on is cast on a head above the root.
  have viaDuty := fun {v} (honest : v ∈ J) {k' data} duty target after before =>
    let window := duty_window_of_slot_le (k' := k') (data := data) anchored fits callBeginOk
      receiver ready currentOk honest duty after before
    justified_descends_of_duty anchorStore anchored anchorSlot anchorBoundary preGloas roots agree
      caller callerFound callerBound covers high receiver atTime ⟨_, justifiedFound⟩
      (slot_le_of_epoch_lt positive above) honest duty target (atCall.trans_le window.1) window.2
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
  obtain ⟨-, block0, -, held0, -, -⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read0
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
    pinned u caller n head.root state total _ voters callerBound ⟨head, headOk, rfl⟩
      stateOk totalOk callEpochOk target' anc fin targetOk' ancStored finRead finAnchor
      (fun v hv => ⟨(members v hv).1, (members v hv).2.1⟩) large w
      receiver k current (Nat.zero_le _) receiverBound ready currentOk cpEpoch
      (cpEpoch ▸ afterAnchor)
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
    (roots : HeldBlockStateRootsNonzero (e := e) time) (agree : HonestBlocksAgree (e := e) time)
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
  have read := inputs.2.1
  unfold Store.isAncestor at read
  obtain ⟨callerBlock, callerOk, -⟩ := bind_ok_iff.mp read
  have callerFound := Store.block_ok_iff.mp callerOk
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
  have up := justified_descends_of_duty anchorStore anchored anchorSlot anchorBoundary preGloas
    roots agree caller callerFound callerBound covers high receiver atTime
    ⟨justifiedBlock, justifiedFound⟩ (slot_le_of_epoch_lt positive above) honest duty target
    (atCall.trans_le low') high'
  exact strict (eq_of_isAncestor_antisymm preGloas rootFound justifiedFound descends up)

/-! ## A late receiver of a root before the call's epoch -/

/-- A collision names a root where the two stores hold different blocks. -/
private theorem findBlockCollision_held {first second : Store preset fork} {roots : List Root}
    {root : Root} {left right : BeaconBlock preset fork}
    (found : Store.findBlockCollision first second roots = some (root, left, right)) :
    first.blocks[root]? = some left ∧ second.blocks[root]? = some right ∧ left ≠ right := by
  induction roots with
  | nil => simp [Store.findBlockCollision] at found
  | cons head tail ih =>
    simp only [Store.findBlockCollision] at found
    split at found
    · rename_i b₁ b₂ h₁ h₂
      split at found
      · exact ih found
      · rename_i ne
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact ⟨h₁, h₂, ne⟩
    · exact ih found

/-- The start of a later slot is more than one delay after the start of an earlier slot. -/
private theorem delay_before_later_slot {Δ : ℕ}
    (fits : DelayFits fork config genesisTimeMs Δ)
    {slot current : Slot} {begin currentBegin : UInt64} (later : slot < current)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (currentOk : computeTimeAtSlotMs config genesisTimeMs current = .ok currentBegin) :
    begin.toNat + Δ < currentBegin.toNat := by
  have lt := UInt64.lt_iff_toNat_lt.mp later
  have bound := current.toNat_lt
  have nextOk : addChecked slot 1 = .ok (slot + 1) :=
    addChecked_ok_iff.mpr ⟨by simp only [UInt64.toNat_one]; omega,
      by rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)⟩
  have nextNat : (slot + 1).toNat = slot.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨following, followingOk, _, followingLe⟩ := exists_timeAtSlotMs_of_le
    (UInt64.le_iff_toNat_le.mpr (by rw [nextNat]; omega)) currentOk
  obtain ⟨due, dueOk⟩ := fits.1
  have fit := fits.2 slot (slot + 1) begin due following nextOk beginOk dueOk followingOk
  have le := UInt64.le_iff_toNat_le.mp followingLe
  omega

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
    (anchorParent : AnchorParentAbsent (e := e) time) (agree : HonestBlocksAgree (e := e) time)
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
  have callRecent : (computeEpochAtSlot preset callSlot).toNat ≤
      (computeEpochAtSlot preset callerBlock.slot).toNat + 1 := by
    obtain ⟨cEpoch, -, -, sEpoch, cEpochOk, -, -, sEpochOk, recent, -⟩ := inputs.1
    rw [callEpochOk, Except.ok.injEq] at cEpochOk
    subst cEpoch
    obtain ⟨b, t, bOk, tOk, lt⟩ := Store.slot_lt_of_mem_getAncestorRoots walk (by simp)
      (show root ∈ chain ++ root :: later by simp)
    rw [Store.block_ok_iff.mpr callerFound, Except.ok.injEq] at bOk
    subst bOk
    have sEq : sEpoch = computeEpochAtSlot preset t.slot := by
      simpa [Store.getBlockEpoch, tOk, bind, Except.bind, pure, Except.pure] using sEpochOk.symm
    subst sEq
    have mono := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lt))
    rw [slotEpochNat] at recent ⊢
    rw [slotEpochNat] at recent ⊢
    omega
  -- The caller's head realized the root's epoch.
  obtain ⟨headState, headStored, headAbove, headRealized⟩ :=
    realizedHead root rootMem _ callerBlock callEpochOk callerFound previous
  obtain ⟨headBlock, headKnown, -⟩ := Store.slot_le_of_isAncestor callerFound headAbove
  -- The receiver's slot starts more than one delay after the call.
  have genesisOf (v : ValidatorIndex) (hv : v ∈ J) (i : ℕ) :
      ((e.world i).state v).genesisTimeMs = genesisTimeMs := by
    have clock := (e.clock_bounds v i).1
    rw [anchored v hv] at clock
    exact clock.trans anchorClock
  obtain ⟨currentBegin, currentBeginOk, currentBeginLe⟩ :=
    slotStart_le_clock (genesisOf w receiver k) currentOk (UInt64.le_refl _)
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
  have delay := delay_before_later_slot fits callBefore callBeginOk currentBeginOk
  -- The receiver's finality is held, as the anchor state's root is not zero.
  obtain ⟨anchorKey, -, anchorFound⟩ := reachedW.anchor_known
  have nonzero := roots w receiver k receiverBound anchorKey anchorBlock anchorFound
  have held (r : Root) (contains : ((e.world k).state w).blocks.contains r) :
      ∃ b, ((e.world k).state w).blocks[r]? = some b := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?] at contains
    exact Option.isSome_iff_exists.mp contains
  have finalizedKnown : ∃ finalizedBlock, ((e.world k).state w).blocks[
      ((e.world k).state w).finalizedCheckpoint.root]? = some finalizedBlock := by
    rcases reachedW.checkpoints_known sound (UInt64.le_of_eq anchorSlot) positive window
        (checkpoint := ((e.world k).state w).finalizedCheckpoint) (by simp) with
      ⟨-, -, contains⟩ | ⟨-, contains⟩ | zero
    · exact held _ contains
    · exact held _ contains
    · rw [reachedW.anchorState_root, Except.ok.injEq] at zero
      exact absurd zero nonzero
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
  obtain ⟨headHeld, -⟩ | ⟨a, ha, b, hb, i, j, hi, hj, r, ⟨r', left, right⟩, found⟩ :=
    e.blocks_of_partiallySynchronous sync preGloas admitted anchorStore anchored caller receiver
      late receiverBound ready finalizedKnown headKnown finalRead
  swap
  · obtain ⟨leftFound, rightFound, different⟩ := findBlockCollision_held found
    exact absurd (agree a ha b hb i j hi hj r' left right leftFound rightFound) different
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
  have upper := votingSource_le_justified forwardW sound positive slots anchorLower sourceOk
  have sameEpoch : source.epoch = ((e.world k).state w).justifiedCheckpoint.epoch :=
    UInt64.le_antisymm upper (UInt64.le_trans justifiedLe (UInt64.le_trans headRealized lower))
  exact .inr (.inl sameEpoch)

/-! ## A late receiver of a root of the call's epoch -/

/-- The pin reserve contains the quorum reserve. -/
private theorem quorumReserve_le_pinReserve (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    quorumReserve config state ancestor ≤ pinReserve config state ancestor finalizedState := by
  unfold pinReserve
  dsimp only
  exact Nat.le_add_right _ _

/-- The boundary of the epoch after an epoch is before a slot two epochs on. -/
private theorem lc_next_boundary {epoch : Epoch} {current : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (late : epoch.toNat + 1 < (computeEpochAtSlot preset current).toNat) :
    ∃ (next : Epoch) (boundary : Slot),
      addChecked epoch 1 = .ok next ∧ computeStartSlotAtEpoch preset next = .ok boundary ∧
      boundary < current := by
  have curNat : (computeEpochAtSlot preset current).toNat =
      current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  rw [curNat] at late
  have twoBelow : (epoch.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat ≤ current.toNat :=
    (Nat.le_div_iff_mul_le positive).mp (by omega)
  have split : (epoch.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat =
      (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    ring
  have fits : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat < current.toNat := by omega
  have currentFits := current.toNat_lt
  have nextFits : epoch.toNat + 1 < 2 ^ 64 := by
    have := Nat.le_mul_of_pos_right (epoch.toNat + 1) positive
    omega
  have nextNat : (epoch + 1).toNat = epoch.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt nextFits
  have nextOk : addChecked epoch 1 = .ok (epoch + 1) :=
    addChecked_ok_iff.mpr ⟨by rw [UInt64.toNat_one]; exact nextFits,
      by rw [nextNat, UInt64.toNat_one]⟩
  have boundaryNat : (UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)).toNat =
      (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have boundaryOk : computeStartSlotAtEpoch preset (epoch + 1) =
      .ok (UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)) :=
    computeStartSlotAtEpoch_ok_iff.mpr ⟨by rw [nextNat]; omega, by rw [boundaryNat, nextNat]⟩
  exact ⟨epoch + 1, _, nextOk, boundaryOk,
    UInt64.lt_iff_toNat_lt.mpr (by rw [boundaryNat]; exact fits)⟩

/-- A head's checkpoint read passes to another store, at each block above a block of its epoch.

The block is on the head's chain, and the two stores agree on their blocks. -/
private theorem lc_checkpoint_read {A B : Store preset fork}
    (reachedA : Store.Reachable config anchorState anchorBlock A)
    (reachedB : Store.Reachable config anchorState anchorBlock B)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (same : ∀ (r : Root) b c, A.blocks[r]? = some b → B.blocks[r]? = some c → b = c)
    (before : fork < .glamsterdam) {head origin x checkpoint : Root} {epoch : Epoch}
    {originBlock : BeaconBlock preset fork}
    (headRead : A.getCheckpointBlock head epoch = .ok checkpoint)
    (originHeld : A.blocks[origin]? = some originBlock)
    (onChain : A.isAncestor ⟨head, .pending⟩ ⟨origin, .pending⟩ = .ok true)
    (originEpoch : computeEpochAtSlot preset originBlock.slot = epoch)
    (above : B.isAncestor ⟨x, .pending⟩ ⟨origin, .pending⟩ = .ok true) :
    B.getCheckpointBlock x epoch = .ok checkpoint := by
  obtain ⟨boundary, checkpointBlock, boundaryOk, checkpointHeld, checkpointLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock before headRead
  have early : boundary ≤ originBlock.slot := by
    have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    rw [UInt64.le_iff_toNat_le, boundaryNat, ← originEpoch]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  have walk := Store.getAncestor_of_isAncestor_of_lt before originHeld onChain
  have through := Store.getAncestor_trans early walk
  have originRead : A.getCheckpointBlock origin epoch = .ok checkpoint := by
    simp only [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind]
      at headRead ⊢
    rw [← through]
    exact headRead
  obtain ⟨received, receivedHeld⟩ : ∃ b, B.blocks[origin]? = some b := by
    have read := above
    unfold Store.isAncestor at read
    obtain ⟨b, found, _⟩ := bind_ok_iff.mp read
    exact ⟨b, Store.block_ok_iff.mp found⟩
  have sameOrigin := same origin originBlock received originHeld receivedHeld
  subst sameOrigin
  have aboveAnchor : anchorBlock.slot ≤ boundary :=
    UInt64.le_trans (reachedA.anchorSlot_le (UInt64.le_of_eq anchorSlot) checkpointHeld)
      checkpointLe
  have receiverRead := Store.getCheckpointBlock_of_same_blocks reachedB same boundaryOk
    aboveAnchor ⟨originBlock, receivedHeld⟩ originRead
  exact Store.getCheckpointBlock_of_isAncestor (node := ⟨x, .pending⟩) before receivedHeld above
    boundaryOk early receiverRead

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
    (roots : HeldBlockStateRootsNonzero (e := e) time) (agree : HonestBlocksAgree (e := e) time)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (drift : QuorumDriftWithin (e := e) horizon time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (included : TargetIncluded (e := e) time)
    (family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
      ((e.world i).state w).finalizedCheckpoint.epoch =
      .ok ((e.world i).state w).finalizedCheckpoint.root)
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
      ∃ block, s.blocks[b]? = some block := by
    unfold Store.isAncestor at h
    obtain ⟨block, found, -⟩ := bind_ok_iff.mp h
    exact ⟨block, Store.block_ok_iff.mp found⟩
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
  -- An epoch-start call confirms its finalized root, which is older than the call's epoch.
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
    have finalRoot := inputs.2.2.2.2.1 callSlot _ _ callSlotOk startTrue epochOk rootEpochOkN rfl
    have read := family u caller n n le_rfl callerBound
    obtain ⟨boundary, finalBlock, boundaryOk, finalKnown, finalBefore, -⟩ :=
      Store.isAncestor_of_getCheckpointBlock preGloas read
    rw [← finalRoot, rootFoundN, Option.some.injEq] at finalKnown
    rw [← finalKnown] at finalBefore
    have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have slotLe := UInt64.le_iff_toNat_le.mp finalBefore
    have rootEpochNat := slotEpochNat rootBlock.slot
    rw [sameEpoch] at rootEpochNat
    have bound := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (show rootBlock.slot.toNat ≤
        ((e.world n).state u).finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat
        by omega)
    rw [Nat.mul_div_cancel _ positive] at bound
    have after := UInt64.lt_iff_toNat_lt.mp callEpochs.2
    rcases (forwardOf u caller n).finalized_add_two_le_or_anchor sound slots
        (UInt64.le_of_eq anchorSlot) epochOk with old | atAnchor
    · omega
    · have := UInt64.le_iff_toNat_le.mp atAnchor
      omega
  -- The call's slot and the next epoch's boundary start before the receiver's time.
  obtain ⟨callSlot', callBegin, callSlotOk', callBeginOk, atCall⟩ := id atSlot
  cases Except.ok.inj (callSlotOk'.symm.trans callSlotOk)
  have genesisK : ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
    rw [(e.clock_bounds w k).1, anchored w receiver]
    exact (getForkchoiceStore_timeMs anchorStore).1.trans anchorGenesis
  obtain ⟨currentBegin, currentBeginOk, currentBeginLe⟩ :=
    slotStart_le_clock genesisK currentOk (UInt64.le_refl _)
  rw [ready.1, atTime] at currentBeginLe
  have callLt : callSlot < current := UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_div_lt_div
    (c := preset.SLOTS_PER_EPOCH.toNat) (by rw [← slotEpochNat, ← slotEpochNat]; omega))
  have callBefore := delay_before_later_slot fits callLt callBeginOk currentBeginOk
  have callBeforeT : (e.world n).time < T := by omega
  obtain ⟨next, boundary, nextOk, boundaryOk, boundaryLt⟩ := lc_next_boundary positive lateNat
  obtain ⟨begin, beginOk, -, -⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt boundaryLt) currentBeginOk
  have beginBefore := delay_before_later_slot fits boundaryLt beginOk currentBeginOk
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
    Store.isAncestor_of_getCheckpointBlock preGloas targetRead
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
      lc_checkpoint_read reachedQ reachedN anchorSlot sameQN preGloas targetRead originHeldQ
        originBelow originEpochNat headAboveOrigin, rfl⟩
  have nextOk' : addChecked target.epoch 1 = .ok next := targetEpoch ▸ nextOk
  have windowRead := rollover target next boundary begin targetN nextOk' boundaryOk beginOk beginLe
  -- The current-target step at the record's call names the honest voters of the target.
  obtain ⟨pulled', total, voters, pulledOk', totalOk, twoThirds, members⟩ :=
    Execution.honestTargetVotes_signed_of_checked slots positive (by omega) preGloas fits prompt
      votes windows fit roots agree anchorStore anchorSlot anchorBoundary anchored caller readyQ
      atSlotQ headQOk checkQ count targetOk originEpochQ originBelow nextOk' boundaryOk beginOk
      beginLe coverage windowRead
  cases Except.ok.inj (pulledOk'.symm.trans pulledOk)
  -- Assumption 3: a seed above the root carries the voters' target votes.
  have receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have rootEpochK : ((e.world k).state w).getBlockEpoch root = .ok target.epoch := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr rootFound, sameEpoch, targetEpoch, bind,
      Except.bind, pure, Except.pure]
  have rootReadK := lc_checkpoint_read reachedQ reachedK anchorSlot sameQK preGloas targetRead
    originHeldQ originBelow originEpochNat rootAboveOriginK
  obtain ⟨seed, seedBlock, seedState, seedHeld, seedStored, seedAbove, seedLower, seedUpper,
      seedRead, seedVotes⟩ :=
    included u caller q n qLe callerBound headQ pulled total target voters headQOk pulledOk
      targetOk totalOk (targetEpoch ▸ epochQ) (targetEpoch ▸ epochOk) (by omega) next boundary
      begin nextOk' boundaryOk beginOk (fun v hv => ⟨(members v hv).1, (members v hv).2.2⟩)
      w receiver k (computeEpochAtSlot preset current) receiverBound (by omega) ready
      receiverEpochOk (by omega) root target.epoch rootEpochK (UInt64.le_refl _) rootReadK
      (by rw [atTime]; exact covers)
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
    have pulledEpoch := pulled_epoch forwardQ positive epochQ pulledOk
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
    have checkRead := lc_checkpoint_read reachedQ reachedK anchorSlot sameQK preGloas targetRead
      originHeldQ originBelow originEpochNat (aboveOriginOf above)
    have epochWEq : getCurrentEpoch W = computeEpochAtSlot preset seedBlock.slot :=
      epochW.trans seedEpochEq
    have drifted := drift u caller q headQ.root pulled anc target qBound pulledOk targetOk
      ancStored w receiver k P Ps W receiverBound stored checkRead shape
      (by rw [epochWEq]; exact seedLower) (by rw [epochWEq]; omega)
      (UInt64.le_trans (by rw [epochWEq]; exact UInt64.le_of_lt seedLate) receiverHorizon)
      voters totalW total (fun v member => ⟨(members v member).2.1, clean v member⟩) totalWOk
      totalOk
    have reserveLe := quorumReserve_le_pinReserve config pulled anc fin
    exact ⟨by omega, clean⟩
  have sourceLower := fun tip source above read =>
    seed_source_lower reachedK sound anchorSlot preGloas positive window (by omega) seedHeld
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
  have upper := votingSource_le_justified forwardK sound positive slots anchorLower sourceOk
  have jLe : ((e.world k).state w).justifiedCheckpoint.epoch ≤ target.epoch := by
    rw [targetEpoch, ← sameEpoch]
    exact justifiedLe
  have sourceEq : source.epoch = ((e.world k).state w).justifiedCheckpoint.epoch :=
    UInt64.le_antisymm upper (UInt64.le_trans jLe lower)
  exact .inr (.inl sourceEq)

/-! ## The root in the filtered tree -/

/-- An up-to-date honest receiver passes the justified test above the root.

The proof splits on the receiver's epoch, and on the root's epoch against the call's. -/
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
    (anchorParent : AnchorParentAbsent (e := e) time) (agree : HonestBlocksAgree (e := e) time)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (drift : QuorumDriftWithin (e := e) horizon time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (included : TargetIncluded (e := e) time)
    (family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
      ((e.world i).state w).finalizedCheckpoint.epoch =
      .ok ((e.world i).state w).finalizedCheckpoint.root)
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
  have read := inputs.2.1
  unfold Store.isAncestor at read
  obtain ⟨callerBlock, callerOk, -⟩ := bind_ok_iff.mp read
  have callerFound := Store.block_ok_iff.mp callerOk
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
      selected pinned signed drift unslashed anchorGenesis included family caller upToDate atSlot
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
    (anchorParent : AnchorParentAbsent (e := e) time) (agree : HonestBlocksAgree (e := e) time)
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
    · rcases forward.finalized_add_two_le_or_anchor sound slots (UInt64.le_of_eq anchorSlot)
          epochOk with old | old
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
    (anchorParent : AnchorParentAbsent (e := e) time) (agree : HonestBlocksAgree (e := e) time)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (pinned : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    (drift : QuorumDriftWithin (e := e) horizon time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (included : TargetIncluded (e := e) time)
    (family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
      ((e.world i).state w).finalizedCheckpoint.epoch =
      .ok ((e.world i).state w).finalizedCheckpoint.root)
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
      included family heldReads caller upToDate atSlot headOk rollover inputs walk realized
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
    Store.exists_leaf_above_through (lower := lower) preGloas rootFound topFound rootPath topPath
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
  rw [read, isViableLeaf_true read epochOk votingOk (sourceOk leaf voting epoch leafTop epochOk
    votingOk) (.inr (finalized_read_above_root slots positive preGloas fits windows params ring
        anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon roots anchorParent
        agree selected pinned signed heldReads caller atSlot headOk inputs walk realized low high
        covers receiver atTime ready tree descends strict leafRoot))]

/-- At a time T, the confirmed root of a call stays in the filtered tree of honest stores.

This is a per-time step toward Theorem 3 of #2058.

It holds at each up-to-date honest store at T whose justified block the root strictly descends from.

The other case is a held state whose justification conflicts with a store's finality.

Honest heads must descend from the root up to T, and from the walk's start up to the horizon.

The call's checks give a root with a recent realized justification, on the head's chain.

The proof finds a viable leaf above the root, from two facts about each leaf.

Its voting source is at least the store's justified epoch, by the receiver's epoch.

An early receiver gets it from the root's realized justification.

A late receiver of the call's epoch gets it from a seed that includes the target's honest votes.

`TargetIncluded` gives that seed, from the voters that the current-target step names.

A late receiver of an earlier root gets it from the call's head, which the store holds.

The leaf also reads the store's finalized checkpoint, through the root's realized justification.

`Execution.heldFinality_or_evidence` gives that read, or the evidence. -/
theorem Execution.rootInFilteredTree_of_checked [DecidablePred (· ∈ J)]
    {anchor : Store preset fork} {Δ time T : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ}
    {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
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
    (anchorParent : AnchorParentAbsent (e := e) time) (agree : HonestBlocksAgree (e := e) time)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
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
    (family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
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
    (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes ∨ HeldStateFinalityEvidence (e := e) pre time := by
  rcases Execution.heldFinality_or_evidence pre anchorStore anchored sound anchorSlot
      anchorBoundary slots inHorizon roots anchorParent params genesis upgrade enough floor with
    heldReads | evidence
  · exact .inl (root_mem_filtered_of_reads sync slots positive preGloas admitted fits prompt votes
      windows fit params ring anchorStore sound anchorSlot anchorBoundary anchored anchorOk
      inHorizon roots anchorParent agree selected pinned signed drift unslashed anchorGenesis
      included family heldReads caller upToDate atSlot headOk rollover inputs walk realized
      realizedHead low high startCovers covers receiver atTime ready tree descends strict)
  · exact .inr evidence

/-! ## The root held from the call on -/

/-- An honest vote before the call slot, for a block above the root, keeps the root held.

From the call to the horizon, every up-to-date honest store holds the root.

One other case is two honest stores that collide.

The last is a held state's justification that conflicts with a store's finality.

The root's realized justification is at most two epochs before the call's epoch.

The signer held the root at its deadline, and the deadline plus the delay is before the call.

Each receiver is up to date at the start of the call's slot, by prompt processing.

There its finality is the anchor's, or at most the root's realized justification.

A justification at or before the anchor epoch makes that finality the anchor checkpoint.

Otherwise `Execution.heldFinality_or_evidence` reads it on the justification's chain.

The root's chain passes through that justification, so the root reads it too.

Synchrony then delivers the root, and blocks persist to later times. -/
theorem Execution.rootHeld_of_honest_vote {Δ : ℕ} {anchor : Store preset fork} {time : ℕ}
    {horizon : Epoch} {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (fits : DelayFits fork config genesisTimeMs Δ)
    (admitted : BlocksAdmitted e 0 Δ time) (prompt : Prompt e time)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (anchorParent : AnchorParentAbsent (e := e) time) (params : DirectSafety.Parameters preset)
    (genesis : Genesis config checks g) (upgrade : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (floor : HeldTerminalStakeFloor (e := e) horizon time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {slot : Slot} {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atBegin : (e.world n).time = begin.toNat) (within : (e.world n).time ≤ time)
    {root : Root} {block : BeaconBlock preset fork} {rootState : BeaconState preset fork}
    (known : ((e.world n).state u).blocks[root]? = some block)
    (stored : ((e.world n).state u).blockStates[root]? = some rootState)
    (recent : (computeEpochAtSlot preset slot).toNat ≤
      rootState.currentJustifiedCheckpoint.epoch.toNat + 2)
    (vote : ∃ v ∈ J, ∃ i, (e.world i).time ≤ (e.world n).time ∧ ∃ m ∈ (e.world i).sent, ∃ data,
      (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.slot < slot ∧
      ((e.world n).state u).isAncestor ⟨data.beaconBlockRoot, .pending⟩ ⟨root, .pending⟩ =
        .ok true) :
    HonestHoldsFrom (e := e) root (e.world n).time time ∨ HonestCollision (e := e) time ∨
      HeldStateFinalityEvidence (e := e) pre time := by
  -- Every held state reads every honest finality at or below its justification.
  rcases Execution.heldFinality_or_evidence pre anchorStore anchored sound anchorSlot
      anchorBoundary slots inHorizon roots anchorParent params genesis upgrade enough floor with
    reads | evidence
  swap
  · exact .inr (.inr evidence)
  by_cases collide : HonestCollision (e := e) time
  · exact .inr (.inl collide)
  left
  -- Without a collision, honest stores up to the time agree on every shared root.
  have agree := (Store.blocks_agree_or_collision
    (fun x : ValidatorIndex × ℕ => (e.world x.2).state x.1)
    (fun x => x.1 ∈ J ∧ (e.world x.2).time ≤ time)).resolve_right fun found => by
      obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, evidence, collision⟩ := found
      exact collide ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, collision⟩
  have forwardOf := e.forwardReachable
    (fun x hx => (anchored x hx) ▸ Store.ForwardReachable.anchor anchorStore)
  have reached (w : ValidatorIndex) (hw : w ∈ J) (k : ℕ) := (forwardOf k w hw).reachable
  have anchorLe : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  obtain ⟨v, honest, i, voteTime, m, sent, data, signed, early, descends⟩ := vote
  -- The signer held its head, the voted block, at the deadline of the vote.
  obtain ⟨k, before, maySign⟩ := e.exists_maySign_of_signed sent signed honest
  obtain ⟨_, _, deadline, signerGenesis, _, honestData, _⟩ := maySign
  obtain ⟨head, headBlock, _, _, _, headHeld, _, _, made⟩ := honestData
  have dataRoot := (getAttestationData_eq_ok_iff.mp made).2.2.2.1
  have kTime : (e.world k).time ≤ (e.world n).time :=
    (e.monotone_time before.le).trans voteTime
  have same := agree (u, n) ⟨caller, within⟩ (v, k) ⟨honest, kTime.trans within⟩
  -- So the signer held the root then.
  have signerDescends := Store.isAncestor_of_same_blocks (reached v honest k) preGloas same known
    ((reached u caller n).anchorSlot_le anchorLe known) ⟨headBlock, dataRoot ▸ headHeld⟩ descends
  obtain ⟨signerBlock, signerKnown⟩ :
      ∃ b : BeaconBlock preset fork, ((e.world k).state v).blocks[root]? = some b := by
    simp only [Store.isAncestor, bind, Except.bind] at signerDescends
    cases held : ((e.world k).state v).block root with
    | error => simp [held] at signerDescends
    | ok b => exact ⟨b, Store.block_ok_iff.mp held⟩
  -- The deadline of the vote, plus the delay, is before the call.
  have late : (e.world k).time + Δ ≤ (e.world n).time := by
    rw [atBegin]
    exact fits.deadline_add_le deadline (computeSlotAtTimeMs_computeTimeAtSlotMs slots beginOk)
      early
  -- Every honest store runs on the model's genesis, as the signer's does.
  have genesisOf (w : ValidatorIndex) (hw : w ∈ J) (j : ℕ) :
      ((e.world j).state w).genesisTimeMs = genesisTimeMs := by
    have left := (e.clock_bounds v k).1
    have right := (e.clock_bounds w j).1
    rw [anchored v honest] at left
    rw [anchored w hw] at right
    exact right.trans (left.symm.trans signerGenesis)
  -- A receiver up to date at the start of the call's slot holds the root.
  have receipt (w : ValidatorIndex) (receiver : w ∈ J) (r : ℕ)
      (atCall : (e.world r).time = begin.toNat)
      (current : UpToDate config checks sources (e.world r).time ((e.world r).view w)
        ((e.world r).state w)) :
      ∃ b : BeaconBlock preset fork, ((e.world r).state w).blocks[root]? = some b := by
    have rBound : (e.world r).time ≤ time := atCall ▸ atBegin ▸ within
    have reachedW := reached w receiver r
    have clockEq : ((e.world r).state w).timeMs = begin :=
      UInt64.toNat_inj.mp (current.1.trans atCall)
    have slotOk : ((e.world r).state w).getCurrentSlot config = .ok slot := by
      unfold Store.getCurrentSlot
      rw [genesisOf w receiver r, clockEq]
      exact mapError_ok_iff.mpr (computeSlotAtTimeMs_computeTimeAtSlotMs slots beginOk)
    have epochOk : ((e.world r).state w).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset slot) := by
      simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
    -- The receiver's finality is held, as the anchor state's root is not zero.
    obtain ⟨anchorKey, -, anchorFound⟩ := reachedW.anchor_known
    have nonzero := roots w receiver r rBound anchorKey anchorBlock anchorFound
    have held (r' : Root) (contains : ((e.world r).state w).blocks.contains r') :
        ∃ b, ((e.world r).state w).blocks[r']? = some b := by
      rw [Std.TreeMap.contains_eq_isSome_getElem?] at contains
      exact Option.isSome_iff_exists.mp contains
    have finalizedKnown : ∃ finalizedBlock, ((e.world r).state w).blocks[
        ((e.world r).state w).finalizedCheckpoint.root]? = some finalizedBlock := by
      rcases reachedW.checkpoints_known sound anchorLe positive window
          (checkpoint := ((e.world r).state w).finalizedCheckpoint) (by simp) with
        ⟨-, -, contains⟩ | ⟨-, contains⟩ | zero
      · exact held _ contains
      · exact held _ contains
      · rw [reachedW.anchorState_root, Except.ok.injEq] at zero
        exact absurd zero nonzero
    -- The caller reads the receiver's finality on the root's chain.
    have callerRead : ((e.world n).state u).getCheckpointBlock root
        ((e.world r).state w).finalizedCheckpoint.epoch =
          .ok ((e.world r).state w).finalizedCheckpoint.root := by
      -- The finality is the anchor's, or at most the root's realized justification.
      have finalLe : ((e.world r).state w).finalizedCheckpoint.epoch ≤
            getCurrentEpoch anchorState ∨
          ((e.world r).state w).finalizedCheckpoint.epoch ≤
            rootState.currentJustifiedCheckpoint.epoch := by
        rcases (forwardOf r w receiver).finalized_add_two_le_or_anchor sound slots anchorLe
            epochOk with lag | low
        · exact .inr (UInt64.le_iff_toNat_le.mpr (by omega))
        · exact .inl low
      by_cases jAnchor : rootState.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch anchorState
      · -- The finality is the anchor checkpoint, read from any held root.
        have atAnchor := finalLe.elim id (fun le => UInt64.le_trans le jAnchor)
        obtain ⟨epochEq, rootHash⟩ := reachedW.finalized_eq_anchor_of_epoch_le atAnchor
        rw [epochEq]
        exact (reached u caller n).getCheckpointBlock_anchor anchorSlot anchorBoundary
          (anchorParent u caller n within) known rootHash
      have later : getCurrentEpoch anchorState < rootState.currentJustifiedCheckpoint.epoch :=
        UInt64.not_le.mp jAnchor
      have belowJustified : ((e.world r).state w).finalizedCheckpoint.epoch ≤
          rootState.currentJustifiedCheckpoint.epoch :=
        finalLe.elim (fun le => UInt64.le_of_lt (UInt64.lt_of_le_of_lt le later)) id
      have justifiedRead :=
        reads w receiver u caller r n rBound within root rootState stored later belowJustified
      have rootRead : ((e.world n).state u).getCheckpointBlock root
          rootState.currentJustifiedCheckpoint.epoch =
            .ok rootState.currentJustifiedCheckpoint.root := by
        obtain ⟨callerKey, -, callerAnchor⟩ := (reached u caller n).anchor_known
        rcases (reached u caller n).getCheckpointBlock_of_blockState sound anchorLe positive window
            stored (.inl (by simp)) later with ⟨ok, -⟩ | zero
        · exact ok
        · rw [(reached u caller n).anchorState_root, Except.ok.injEq] at zero
          exact absurd zero (roots u caller n within callerKey anchorBlock callerAnchor)
      rw [Store.getCheckpointBlock_trans preGloas rootRead belowJustified]
      exact justifiedRead
    -- So the signer reads it too.
    have signerFinal : ((e.world k).state v).getCheckpointBlock root
        ((e.world r).state w).finalizedCheckpoint.epoch =
          .ok ((e.world r).state w).finalizedCheckpoint.root := by
      have read := callerRead
      simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq] at read
      obtain ⟨boundary, boundaryOk, ancestor, walk, -⟩ := read
      obtain ⟨reachedBlock, reachedFound, reachedLe⟩ := Store.getAncestor_le walk
      exact Store.getCheckpointBlock_of_same_blocks (reached v honest k) same boundaryOk
        (UInt64.le_trans ((reached u caller n).anchorSlot_le anchorLe reachedFound) reachedLe)
        ⟨signerBlock, signerKnown⟩ callerRead
    rcases e.blocks_of_partiallySynchronous sync preGloas admitted anchorStore anchored honest
        receiver (by simp only [Nat.max_zero]; omega) rBound current finalizedKnown signerKnown
        signerFinal with ⟨found, -⟩ | found
    · exact ⟨signerBlock, found⟩
    · exact absurd found collide
  intro w receiver j atLeast atMost current
  by_cases sameTime : (e.world j).time = begin.toNat
  · exact receipt w receiver j sameTime current
  -- Otherwise the receiver was up to date at the start of the call's slot, before `j`.
  have started : e.startTime ≤ begin.toNat := atBegin ▸ e.monotone_time (Nat.zero_le n)
  obtain ⟨r, atCall, upToDate⟩ :=
    (prompt w receiver slot begin beginOk started (atBegin ▸ within)).1
  obtain ⟨b, found⟩ := receipt w receiver r atCall upToDate
  have order : r ≤ j := by
    by_contra! after
    have back : (e.world j).time ≤ (e.world r).time := e.monotone_time after.le
    omega
  exact ⟨b, e.blocks_of_le order found⟩

end EthLib.Consensus.Models.Network
