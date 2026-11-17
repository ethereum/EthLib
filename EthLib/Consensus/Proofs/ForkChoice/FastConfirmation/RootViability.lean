module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin

/-!
# Root viability: the current target

An up-to-date honest store may accept the current-target test of the fast confirmation rule.

Honest validators then sign that target with two thirds of the active balance of its head state.

The honest count and the coverage of honest heads by a block of the epoch are assumed.

So is the caller's committee read at the start of the next epoch.
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

/-- The caller's rollover read at the start of the epoch after the target's.

At that time the caller's up-to-date store has a head and reads its window over the target's epoch.

An honest voter that has not voted by the call needs a duty in the target's epoch.

`AssignmentWindowAgreement` gives that duty only through the past window of an actual head. -/
def RolloverWindowRead (u : ValidatorIndex) (target : Checkpoint) (first : Slot) (begin : ℕ) :
    Prop :=
  ∀ k epochStart last, (e.world k).time = begin →
    UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u) →
    computeStartSlotAtEpoch preset target.epoch = .ok epochStart →
    subChecked first 1 = .ok last →
    ∃ (hd : ForkChoiceNode) (participants : Std.TreeSet ValidatorIndex),
      ((e.world k).state u).getHead config = .ok hd ∧
      ((e.world k).state u).getCommitteesBetweenSlots hd.root epochStart last =
        .ok participants

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

/-- An active counted voter has a duty in the epoch, read from the rollover window. -/
private theorem duty_of_active {anchor : Store preset fork} {time : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (windows : AssignmentWindowAgreement (e := e) time)
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
    {hd : ForkChoiceNode} {participants : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world k).state u).getHead config = .ok hd)
    (slotOk : ((e.world k).state u).getCurrentSlot config = .ok boundary)
    (read : ((e.world k).state u).getCommitteesBetweenSlots hd.root first last = .ok participants)
    (descends : ((e.world k).state u).isAncestor hd ⟨origin, .pending⟩ = .ok true)
    {v : ValidatorIndex} (honest : v ∈ J)
    (active : v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset) :
    ∃ slot index, first ≤ slot ∧ slot ≤ last ∧ assignment.committee v slot = some index := by
  have forwardN := e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored) n u caller
  have forwardK := e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored) k u caller
  have pending := Store.getHead_pending preGloas headOk
  have nodeEq : hd = ⟨hd.root, .pending⟩ := by
    cases hd
    simp_all
  have originRead := descends
  unfold Store.isAncestor at originRead
  obtain ⟨otherOrigin, otherKnown, _⟩ := bind_ok_iff.mp originRead
  have otherKnown := Store.block_ok_iff.mp otherKnown
  obtain ⟨headBlock, headKnown, _⟩ := Store.slot_le_of_isAncestor otherKnown descends
  obtain ⟨headState, headStateHeld, _⟩ := forwardK.reachable.blockStatesFromParents headKnown
  have headStateOk := Store.blockState_ok_iff.mpr headStateHeld
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
  have member := Store.mem_getCommitteesBetweenSlots_of_active positive read headStateOk
    (by omega) (by rw [← nextNat, ← boundaryNat]; omega) activeAt
  have past : last < boundary := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have epochBoundary := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) boundaryOk
  have epochFirst := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) firstOk
  obtain ⟨slot, index, low, high, duty⟩ := (windows u caller k kBound hd boundary first last
    participants headOk slotOk past (fun found foundOk => by
      have le := headState_epoch_le forwardK slotOk foundOk
      rw [epochBoundary] at le
      rw [epochFirst]
      omega) read v honest).mp member
  exact ⟨slot, index, low, high, duty⟩

/-- A counted voter outside the past committees has no duty before the call's slot. -/
private theorem duty_after_call {time : ℕ} {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (windows : AssignmentWindowAgreement (e := e) time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (nBound : (e.world n).time ≤ time)
    {head : ForkChoiceNode} (headOk : ((e.world n).state u).getHead config = .ok head)
    {current first last : Slot} {participants : Std.TreeSet ValidatorIndex}
    (currentOk : ((e.world n).state u).getCurrentSlot config = .ok current)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset current) = .ok first)
    (lastOk : subChecked current 1 = .ok last)
    (participantsOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants)
    {v : ValidatorIndex} (honest : v ∈ J) (unseen : v ∉ participants)
    {slot : Slot} {index : CommitteeIndex} (low : first ≤ slot)
    (duty : assignment.committee v slot = some index) :
    current ≤ slot := by
  have forward := e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored) n u caller
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  have lastPos := (subChecked_ok_iff.mp lastOk).1
  simp only [UInt64.toNat_one] at lastNat lastPos
  have past : last < current := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have epochFirst := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) firstOk
  by_contra early
  have high : slot ≤ last := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp early)
    omega)
  exact unseen ((windows u caller n nBound head current first last participants headOk currentOk
    past (fun found foundOk => by
      have le := headState_epoch_le forward currentOk foundOk
      rw [epochFirst]
      omega) participantsOk v honest).mpr ⟨slot, index, low, high, duty⟩)

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

At the start of E + 1, the caller has a head and reads its committee window over epoch E.

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
    (windows : AssignmentWindowAgreement (e := e) time)
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
    (rollover : RolloverWindowRead (e := e) u target first begin.toNat) :
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
  obtain ⟨hd, rolloverParticipants, hdOk, rolloverRead⟩ :=
    rollover k epochStart (first - 1) atK readyK epochStartOk lastOk
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
      positive preGloas retained windows caller kBound
      (agree u caller u caller n k nBound kBound) originKnown originEpoch nextOk epochStartOk
      firstOk lastOk stateOk epochOk descends hdOk slotK rolloverRead hdDescends honest active
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
