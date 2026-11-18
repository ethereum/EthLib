module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.HeadTotality
import EthLib.Consensus.Proofs.ForkChoice.Network
import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery
import EthLib.Consensus.Proofs.HonestAggregation
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin

/-!
# Proofs: up-to-date honest stores have a head

Before Gloas, an up-to-date honest store can compute its head.

The exceptions are a collision of bounded honest stores, and direct-safety evidence from a store.

The head computation needs the state of the justified checkpoint once it weighs a child.

The store moves its justified checkpoint without storing that state, so the state needs a reason.

An honest validator signed a vote for the checkpoint, at a duty before the store's current slot.

That vote reaches the store by the start of the next slot, together with its head block.

The store then accepts it, which stores the target state, and an up-to-date store is a fixed point.

A checkpoint state, once stored, stays.

So the store holds the state, and the head follows from the stake ceiling and the boost's fit.

This is part of [#2060][issue], for the forks before Gloas.

[issue]: https://github.com/ethereum/EthLib/issues/2060
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- An up-to-date store that accepts an attestation of its view holds the state of its target.

The store is a fixed point of that move, and the move stores the target state. -/
private theorem UpToDate.checkpointState_of_accepted {time : ℕ}
    {view : Set (Message preset fork)} {store after : Store preset fork}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (upToDate : UpToDate config checks sources time view store)
    (seen : .attestation attestation ∈ view)
    (accepted : store.onAttestation config checks attestation false = .ok after)
    (reads : ReadsAttestation config checks store attestation indexed) :
    ∃ state, store.checkpointState attestation.data.target = .ok state := by
  have fixed : after = store := upToDate.2 after (.attestation seen accepted)
  obtain ⟨withTarget, stored, result⟩ := Store.onAttestation_eq_of_reads accepted reads
  obtain ⟨withTarget', targetState, stored', found, -⟩ := reads
  rw [stored, Except.ok.injEq] at stored'
  subst stored'
  have same : store.checkpointStates = withTarget.checkpointStates := by
    rw [← fixed, result]
    rfl
  exact ⟨targetState, by simpa [Store.checkpointState, same] using found⟩


variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- A store keeps the state of each checkpoint at every later event. -/
private theorem Execution.checkpointStates_of_le (w : ValidatorIndex) {n k : ℕ} (later : n ≤ k)
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (found : ((e.world n).state w).checkpointStates[checkpoint]? = some state) :
    ((e.world k).state w).checkpointStates[checkpoint]? = some state := by
  induction k, later using Nat.le_induction with
  | base => exact found
  | succ k _ ih =>
    rcases e.state_succ k w with same | ⟨_, moved⟩
    · exact same ▸ ih
    · exact moved.checkpointStates_of_found ih

/-- A justified checkpoint no later than the anchor's is the anchor's, whose state stays held. -/
private theorem Execution.justifiedState_of_anchor {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {w : ValidatorIndex} (honest : w ∈ J) (k : ℕ)
    (early : ((e.world k).state w).justifiedCheckpoint.epoch ≤ anchor.justifiedCheckpoint.epoch) :
    ∃ state, ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state := by
  have initial : (e.world 0).state w = anchor := by
    rw [e.world_zero]
    exact start w honest
  -- The justified checkpoint only moves to a later epoch, so it is still the anchor's.
  have same : ((e.world k).state w).justifiedCheckpoint = anchor.justifiedCheckpoint := by
    have advances := (e.checkpointsAdvance_of_le w (Nat.zero_le k)).1
    rw [initial] at advances
    rcases advances with same | later
    · exact same
    · exact absurd early (UInt64.not_le.mpr later)
  obtain ⟨anchorRoot, hashed, -, -, justified, -⟩ := getForkchoiceStore_anchor anchored
  obtain ⟨anchorRoot', hashed', states⟩ := getForkchoiceStore_checkpointStates anchored
  rw [hashed, Except.ok.injEq] at hashed'
  subst hashed'
  have held : anchor.checkpointStates[anchor.justifiedCheckpoint]? = some anchorState := by
    rw [states, justified]
    simp
  refine ⟨anchorState, ?_⟩
  have kept := e.checkpointStates_of_le w (Nat.zero_le k)
    (checkpoint := anchor.justifiedCheckpoint) (by rw [initial]; exact held)
  rw [same]
  simp [Store.checkpointState, kept, pure, Except.pure]

/-- Before Gloas, an up-to-date honest store holds the state of its justified checkpoint.

Otherwise bounded honest stores collide, or a store's finalized checkpoints give evidence.

The evidence is that of direct safety, relative to the anchor. -/
private theorem Execution.justifiedState_or_evidence {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam) {last : ℕ} (admitted : BlocksAdmitted e 0 Δ last)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e last)
    (votes : ValidatedDutyVotes (e := e) last) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (signed : JustifiedHonestlySigned (e := e) anchor.justifiedCheckpoint.epoch 0 last)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    {horizon : Epoch} (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last) :
    (∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ∃ state, ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
        .ok state) ∨
    (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ last ∧ (e.world j).time ≤ last ∧
      ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
        some evidence) ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  classical
  -- With no honest event in time, every store claim is vacuous.
  by_cases some : ∃ u ∈ J, ∃ n, (e.world n).time ≤ last
  swap
  · push Not at some
    exact .inl fun w honest k inTime => absurd inTime (Nat.not_le.mpr (some w honest k))
  obtain ⟨u, uHonest, n₀, n₀Time⟩ := some
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  rcases e.finalizedFamily_or_historical_evidence anchored start sound anchorSlot anchorBoundary
      slots bounded roots absent parameters genesis pre heldEarly enough terminal uHonest
      n₀Time with chain | evidence
  swap
  · exact .inr (.inr evidence)
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ last) with agree | collision
  swap
  · obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, collision, found⟩ := collision
    exact .inr (.inl ⟨a, ha, b, hb, i, j, hi, hj, r, collision, found⟩)
  have oneBlock (v : ValidatorIndex) (hv : v ∈ J) (w : ValidatorIndex) (hw : w ∈ J)
      (n k : ℕ) (hn : (e.world n).time ≤ last) (hk : (e.world k).time ≤ last) :=
    agree (v, n) ⟨hv, hn⟩ (w, k) ⟨hw, hk⟩
  have forward := fun w (hw : w ∈ J) j => e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) j w hw
  have startLe : ∀ j, e.startTime ≤ (e.world j).time := fun j => by
    simpa [e.world_zero, World.initial] using e.monotone_time (Nat.zero_le j)
  by_cases noCollision : ¬ ∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ last ∧
      (e.world j).time ≤ last ∧ ∃ r evidence,
        Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] = some evidence
  swap
  · exact .inr (.inl (not_not.mp noCollision))
  left
  intro w hw k hk upToDate
  by_cases early :
      ((e.world k).state w).justifiedCheckpoint.epoch ≤ anchor.justifiedCheckpoint.epoch
  · exact e.justifiedState_of_anchor anchored start hw k early
  have later := UInt64.not_le.mp early
  -- An honest validator signed the justified checkpoint before the store's current slot.
  obtain ⟨current, currentOk, -, -⟩ := (forward w hw k).slots_le_current slots
    (UInt64.le_of_eq anchorSlot)
  obtain ⟨v, hv, i, iLe, m, sent, data, member, target, before⟩ :=
    signed w hw k current (Nat.zero_le _) hk upToDate currentOk later
  obtain ⟨k', k'Lt, duty⟩ := e.exists_maySign_of_signed sent member hv
  obtain ⟨committeeIndex, assigned, deadline, -, -, honestData, -⟩ := duty
  have k'Le : (e.world k').time ≤ (e.world k).time :=
    (e.monotone_time (Nat.le_of_lt k'Lt)).trans iLe
  obtain ⟨n, attestation, indexed, vote, committees⟩ :=
    votes v hv data.slot committeeIndex _ assigned deadline (startLe k') (k'Le.trans hk)
  -- The duty's timing: its slot, the next slot, and that slot's start before the store's time.
  have genesisOf : ∀ j, ((e.world j).state w).genesisTimeMs = genesisTimeMs := by
    intro j
    have left := (e.clock_bounds v n).1
    have right := (e.clock_bounds w j).1
    rw [start v hv] at left
    rw [start w hw] at right
    exact right.trans (left.symm.trans vote.genesis)
  have deadlineCopy := deadline
  obtain ⟨slotTime, due, slotTimeOk, dueOk, -⟩ := deadlineCopy
  have nextFits : data.slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := UInt64.lt_iff_toNat_lt.mp before
    have := current.toNat_lt
    simp only [UInt64.toNat_one]
    omega
  have nextOk := addChecked_of_lt nextFits
  have nextLe : data.slot + 1 ≤ current := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp before
    rw [(addChecked_ok_iff.mp nextOk).2]
    simp only [UInt64.toNat_one]
    omega)
  obtain ⟨followingTime, followingTimeOk, followingLe⟩ :=
    slotStart_le_clock (genesisOf k) currentOk nextLe
  rw [upToDate.1] at followingLe
  have dueLt := fits.due_lt_slot nextOk slotTimeOk followingTimeOk dueOk
  have beforeBoundary := fits.before_boundary nextOk slotTimeOk followingTimeOk deadline
  -- The duty vote carries the signed data, so its target is the justified checkpoint.
  obtain ⟨dataSlot, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, notFuture⟩ :=
    vote.data_head anchored (UInt64.le_of_eq anchorSlot) start hv deadline dueOk dueLt
  have signedEpoch : data.target.epoch = computeEpochAtSlot preset data.slot := by
    obtain ⟨_, _, _, _, _, _, _, _, made⟩ := honestData
    exact target_epoch_eq_of_getAttestationData made
  obtain ⟨voteSent, voteSigned⟩ := vote.signed_sent anchored start hv
  have sameData : attestation.data = data :=
    e.data_eq_of_signed_of_target_epoch slots voteSent sent voteSigned member hv
      (dataEpoch.trans signedEpoch.symm)
  have targetEq : attestation.data.target = ((e.world k).state w).justifiedCheckpoint :=
    sameData ▸ target
  -- The vote arrives at the next slot's start, or at the store's own event at that time.
  obtain ⟨-, boundary, boundaryTime, boundaryCurrent⟩ :=
    e.exists_duty_boundaries fits (prompt.of_le (followingLe.trans hk)) hw nextOk slotTimeOk
      followingTimeOk deadline (startLe k')
  obtain ⟨arrival, arrivalLe, arrivalTime, arrivalCurrent⟩ : ∃ arrival, arrival ≤ k ∧
      (e.world arrival).time = followingTime.toNat ∧
      UpToDate config checks sources (e.world arrival).time ((e.world arrival).view w)
        ((e.world arrival).state w) := by
    by_cases same : followingTime.toNat = (e.world k).time
    · exact ⟨k, le_refl _, same.symm, upToDate⟩
    · refine ⟨boundary, ?_, boundaryTime, boundaryCurrent⟩
      by_contra h
      have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
      dsimp at bad
      omega
  have arrivalBound : (e.world arrival).time ≤ last := by omega
  have nTime : (e.world n).time = (e.world k').time := vote.atTime
  have nBound : (e.world n).time ≤ last := by omega
  have late : (e.world n).time + Δ ≤ (e.world arrival).time := by
    obtain ⟨_, _, startOk', dueOk', timeEq⟩ := deadline
    rw [slotTimeOk, Except.ok.injEq] at startOk'
    rw [dueOk, Except.ok.injEq] at dueOk'
    subst startOk' dueOk'
    omega
  have arrivalSlot : ((e.world arrival).state w).getCurrentSlot config = .ok (data.slot + 1) := by
    unfold Store.getCurrentSlot
    rw [genesisOf arrival]
    have clock : ((e.world arrival).state w).timeMs = followingTime :=
      UInt64.toNat_inj.mp (arrivalCurrent.1.trans arrivalTime)
    rw [clock]
    exact mapError_ok_iff.mpr (computeSlotAtTimeMs_computeTimeAtSlotMs slots followingTimeOk)
  -- The voter's head reads the finalized checkpoint that the receiver holds at arrival.
  have targetRead := vote.data_target anchored anchorSlot anchorBoundary start hv
    (roots v hv n nBound)
  obtain ⟨targetBoundary, targetBlock, targetBoundaryOk, targetKnown, -, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas targetRead
  have chainRead := chain w hw arrival k arrivalLe hk
  rw [← targetEq] at chainRead
  obtain ⟨finalBoundary, finalBlock, finalBoundaryOk, finalKnown, finalLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas chainRead
  have aboveAnchor : anchorBlock.slot ≤ finalBoundary := UInt64.le_trans
    ((forward w hw k).reachable.anchorSlot_le (UInt64.le_of_eq anchorSlot) finalKnown) finalLe
  have voterRead := Store.getCheckpointBlock_of_same_blocks (forward v hv n).reachable
    (oneBlock w hw v hv k n hk nBound) finalBoundaryOk aboveAnchor ⟨targetBlock, targetKnown⟩
    chainRead
  have finalLeTarget : ((e.world arrival).state w).finalizedCheckpoint.epoch ≤
      attestation.data.target.epoch := by
    rw [targetEq]
    exact UInt64.le_trans (e.checkpointsAdvance_of_le w arrivalLe).2.epoch_le
      ((forward w hw k).reachable.finalized_le_justified sound)
  have headCheckpoint : ((e.world n).state v).getCheckpointBlock attestation.data.beaconBlockRoot
      ((e.world arrival).state w).finalizedCheckpoint.epoch =
        .ok ((e.world arrival).state w).finalizedCheckpoint.root := by
    rw [Store.getCheckpointBlock_trans preGloas targetRead finalLeTarget]
    exact voterRead
  -- So the head reaches the receiver by arrival, with its checkpoint blocks.
  obtain ⟨_, finalized, _, finalizedKnown, _, _⟩ := Store.isAncestor_of_getCheckpointBlock
    preGloas (chain w hw arrival arrival (le_refl _) arrivalBound)
  rcases e.blocks_of_partiallySynchronous sync preGloas admitted anchored start hv hw
      (by simpa using late) arrivalBound arrivalCurrent ⟨finalized, finalizedKnown⟩
      (dataRoot ▸ headKnown) headCheckpoint with ⟨votedKnown, transport⟩ | collision
  swap
  · exact absurd collision noCollision
  have receiverRead := transport _ _ finalLeTarget targetRead
  rcases vote.accepted_at_next_slot preGloas anchored start hv hw committees dataSlot dataEpoch
      nextOk arrivalSlot arrivalBound nBound votedKnown notFuture receiverRead with
    ⟨⟨after, accepted⟩, reads⟩ | collision
  swap
  · exact absurd collision noCollision
  -- The receiver is a fixed point at arrival, so it already holds the target state, and keeps it.
  have seen := e.mem_view_of_send sync vote.sends hv hw (k := arrival) (by simpa using late)
  obtain ⟨state, stateOk⟩ := UpToDate.checkpointState_of_accepted arrivalCurrent seen accepted reads
  refine ⟨state, ?_⟩
  rw [← targetEq]
  have kept := e.checkpointStates_of_le w arrivalLe (Store.checkpointState_ok_iff.mp stateOk)
  exact Store.checkpointState_ok_iff.mpr kept

/-- Every up-to-date honest store in the interval whose viable nodes can be computed has a head. -/
def HonestHeadsExist (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (nodes : List ForkChoiceNode), first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
    ∃ hd, ((e.world k).state w).getHead config = .ok hd

/-- Before Gloas, every up-to-date honest store whose viable nodes can be computed has a head.

Otherwise bounded honest stores collide, or a store's finalized checkpoints give evidence.

The evidence is that of direct safety, relative to the anchor.

The store holds the state of its justified checkpoint, through an honest vote for it.

The stake ceiling and the fit of the proposer boost keep every weight below `2^64`. -/
theorem Execution.honestHeadsExist_or_evidence {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (preGloas : fork < .glamsterdam) {last : ℕ} (admitted : BlocksAdmitted e 0 Δ last)
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e last)
    (votes : ValidatedDutyVotes (e := e) last) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (signed : JustifiedHonestlySigned (e := e) anchor.justifiedCheckpoint.epoch 0 last)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    {horizon : Epoch} (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) last)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17)) (first : ℕ) :
    HonestHeadsExist (e := e) first last ∨
    (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ last ∧ (e.world j).time ≤ last ∧
      ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
        some evidence) ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  rcases e.justifiedState_or_evidence sync slots preGloas admitted fits prompt votes anchored start
      anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre heldEarly
      enough terminal with states | alternative
  · left
    intro w hw k nodes _ inTime upToDate tree
    obtain ⟨state, stateOk⟩ := states w hw k inTime upToDate
    exact Store.getHead_exists preGloas
      (e.forwardReachable (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) k w
        hw) (UInt64.le_of_eq anchorSlot) (absent w hw k inTime) positive scoreFits tree stateOk
      (ceiling w hw k _ state inTime stateOk)
  · exact .inr alternative

end EthLib.Consensus.Models.Network
