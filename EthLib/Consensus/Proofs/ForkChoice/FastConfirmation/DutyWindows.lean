module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
import EthLib.Consensus.Proofs.ForkChoice.CommitteeAgreement
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Duty windows of honest votes

An honest vote is cast at the deadline of its duty, so its slot fixes when its signer read a head.

A duty inside the stretch that a root covers was read on a head above the root.

A justified checkpoint signed in such a duty descends from the root, unless two stores collide.
-/

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A slot no later than a store's current slot starts by the store's clock.

The store must follow the model's time of genesis. -/
public theorem slotStart_le_clock {store : Store preset fork}
    (genesisEq : store.genesisTimeMs = genesisTimeMs) {current target : Slot}
    (currentOk : store.getCurrentSlot config = .ok current) (before : target ≤ current) :
    ∃ targetTime, computeTimeAtSlotMs config genesisTimeMs target = .ok targetTime ∧
      targetTime.toNat ≤ store.timeMs.toNat := by
  have read := mapError_ok_iff.mp currentOk
  change computeSlotAtTimeMs config _ _ = .ok current at read
  rw [genesisEq] at read
  exact slotStart_le_of_slotAtTime read before

/-- An honest duty lies between the call and a store's time.

Its slot is at or after the call's slot and before the store's current slot.

So the duty starts at or after the call's time.

The signer signs at its deadline, before the next slot starts, so before the store's clock. -/
public theorem duty_window_of_slot_le {anchor : Store preset fork} {Δ : ℕ}
    {callSlot current : Slot} {callStart : UInt64} {w v : ValidatorIndex} {k k' : ℕ}
    {data : AttestationData}
    (start : ∀ w ∈ J, e.start w = anchor) (fits : DelayFits fork config genesisTimeMs Δ)
    (callStartOk : computeTimeAtSlotMs config genesisTimeMs callSlot = .ok callStart)
    (receiver : w ∈ J)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current) (honest : v ∈ J)
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k').time ((e.world k').view v) ((e.world k').state v) data)
    (after : callSlot ≤ data.slot) (before : data.slot < current) :
    callStart.toNat ≤ (e.world k').time ∧ (e.world k').time < (e.world k).time := by
  obtain ⟨_, -, deadline, genesis, -, -, -⟩ := duty
  have deadlineCopy := deadline
  obtain ⟨dutyStart, due, dutyStartOk, -, timeEq⟩ := deadlineCopy
  obtain ⟨callStart', callStartOk', -, callLe⟩ := exists_timeAtSlotMs_of_le after dutyStartOk
  rw [callStartOk, Except.ok.injEq] at callStartOk'
  subst callStart'
  -- The deadline and the delay fall before the next slot, which starts by the store's clock.
  obtain ⟨nextOk, following, followingOk, followingLe⟩ := Store.nextSlotStart_le_clock
    (e.genesisTimeMs_eq_of_honest start honest genesis receiver k) currentOk before
  have bound := fits.before_boundary nextOk dutyStartOk followingOk deadline
  refine ⟨?_, ?_⟩
  · have := UInt64.le_iff_toNat_le.mp callLe
    omega
  · rw [← upToDate.1]
    omega

/-- An honest duty's signer reads the duty's target on a head above a covered root.

The duty falls inside the stretch that the root is covered over.

An honest store holds the target's block. -/
public theorem signerHead_of_duty {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {time first T : ℕ}
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    {root : Root} (covers : HonestHeadsCover (e := e) root first T)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k k' : ℕ}
    {data : AttestationData}
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k').time ((e.world k').view v) ((e.world k').state v) data)
    (low : first ≤ (e.world k').time) (lt : (e.world k').time < T)
    (k'Bound : (e.world k').time ≤ time) {checkpointBlock : BeaconBlock preset fork}
    (checkpointKnown : ((e.world k).state w).blocks[data.target.root]? = some checkpointBlock) :
    ∃ head, ((e.world k').state v).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
      ((e.world k').state v).getCheckpointBlock head data.target.epoch = .ok data.target.root := by
  obtain ⟨_, -, -, -, current, honestData, -⟩ := duty
  have reachedV := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k' v
    honest
  have reachedW := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k w
    receiver
  obtain ⟨signerHead, signerHeadOk, targetRead⟩ := honestData.target_read reachedV anchorSlot
    anchorBoundary (roots v honest k' k'Bound) reachedW checkpointKnown
  have supports := covers (e.world k').time low lt v honest k' signerHead rfl current signerHeadOk
  rw [Store.isAncestor_getHead_root signerHeadOk] at supports
  exact ⟨signerHead.root, supports, targetRead⟩

/-- A store's justified checkpoint descends from a root, given an honest duty vote for it.

The duty falls between the call and the store's time.

The root's block is at or before the first slot of the checkpoint's epoch.

The coverage at the duty puts the signer's head above the root.

The checkpoint is that head's block at the first slot of its epoch, so it sits above the root.

The store agrees with the signer on that walk, as honest stores agree on blocks.

Otherwise two honest stores collide on a block. -/
public theorem justified_descends_of_duty {anchor : Store preset fork} {time T : ℕ}
    {root : Root} {u : ValidatorIndex} {n : ℕ} {block : BeaconBlock preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (caller : u ∈ J) (callerHeld : ((e.world n).state u).blocks[root]? = some block)
    (callerTime : (e.world n).time ≤ time)
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) (high : T ≤ time)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = T)
    (justifiedKnown : ∃ b, ((e.world k).state w).blocks[
      ((e.world k).state w).justifiedCheckpoint.root]? = some b)
    (blockLe : block.slot.toNat ≤
      ((e.world k).state w).justifiedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {v : ValidatorIndex} (honest : v ∈ J) {k' : ℕ} {data : AttestationData}
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k').time ((e.world k').view v) ((e.world k').state v) data)
    (target : data.target = ((e.world k).state w).justifiedCheckpoint)
    (afterCall : (e.world n).time ≤ (e.world k').time)
    (beforeStore : (e.world k').time < (e.world k).time) :
    ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      HonestCollision (e := e) time := by
  rcases e.blocksAgree_or_collision time with agree | collision
  swap
  · exact .inr collision
  refine .inl ?_
  have k'Bound : (e.world k').time ≤ time := by omega
  have reachedV := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k' v
    honest
  have reachedW := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k w
    receiver
  -- The store holds its justified block, which is the signer's target.
  obtain ⟨justifiedBlock, justifiedKnown⟩ := justifiedKnown
  rw [← target] at justifiedKnown blockLe ⊢
  obtain ⟨head, supports, targetRead⟩ := signerHead_of_duty anchored start anchorSlot
    anchorBoundary roots covers honest receiver duty afterCall (by omega) k'Bound
    justifiedKnown
  -- The signer holds the root, as the same block as the caller.
  have rootRead := supports
  unfold Store.isAncestor at rootRead
  obtain ⟨b', b'Ok, -⟩ := bind_ok_iff.mp rootRead
  have b'Found := Store.block_ok_iff.mp b'Ok
  rw [agree v honest u caller k' n k'Bound callerTime root b' block b'Found callerHeld] at b'Found
  -- The target is the head's ancestor at the first slot of its epoch, which is above the block.
  have up := Store.isAncestor_of_getCheckpointBlock_above b'Found supports targetRead
      blockLe
  -- The store agrees with the signer on the walk.
  exact Store.isAncestor_of_same_blocks reachedW
    (agree v honest w receiver k' k k'Bound (by omega)) b'Found
    (reachedV.anchorSlot_le (UInt64.le_of_eq anchorSlot) b'Found) ⟨_, justifiedKnown⟩ up

/-- A counted voter outside the past committees has no duty before the call's slot. -/
public theorem duty_after_call {time : ℕ} {anchor : Store preset fork}
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
      have le := forward.headState_epoch_le currentOk foundOk
      rw [epochFirst]
      omega) participantsOk v honest).mpr ⟨slot, index, low, high, duty⟩)

/-- The first slot of a vote's target epoch is at or before the vote's slot. -/
public theorem boundary_le_of_duty {v : ValidatorIndex} {time : ℕ}
    {view : Set (Message preset fork)} {store : Store preset fork} {data : AttestationData}
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      time view store data)
    {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset data.target.epoch = .ok boundary) :
    boundary ≤ data.slot := by
  obtain ⟨_, -, -, -, -, made, -⟩ := duty
  obtain ⟨_, _, _, _, _, _, _, _, dataOk⟩ := made
  have epoch := target_epoch_eq_of_getAttestationData dataOk
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  rw [UInt64.le_iff_toNat_le, firstNat, epoch]
  exact Nat.div_mul_le_self _ _

end EthLib.Consensus.Models.Network
