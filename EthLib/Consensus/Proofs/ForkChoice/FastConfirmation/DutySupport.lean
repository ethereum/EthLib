module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Supporters
public import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Honest duty votes support a previously safe prefix

Signed-message provenance constrains the latest accepted vote, not just the delivered duty vote.

The safe interval follows the head-chain condition of [arXiv 2405.00549v4, Lemma 2][fcr].

[fcr]: https://arxiv.org/abs/2405.00549v4
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

/-- A latest honest vote supports the safe prefix, or bounded honest stores name a collision. -/
private theorem mem_supportersOf_of_latest_rank {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ}
    (preGloas : fork < .glamsterdam)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k : ℕ}
    {message : LatestMessage fork}
    (latest : ((e.world k).state w).latestMessages[v]? = some message)
    (counted : v ∉ ((e.world k).state w).equivocatingIndices)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) (bounded : (e.world k).time ≤ last)
    {due : UInt64} (dueOk : getAttestationDueMs config fork = .ok due)
    (inSlot : due < config.SLOT_DURATION_MS)
    {epoch : Epoch} {begin : Slot} {beginTime : UInt64} {first : ℕ}
    (beginOk : computeStartSlotAtEpoch preset epoch = .ok begin)
    (beginTimeOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (fresh : first ≤ beginTime.toNat) (rank : epoch ≤ message.rank) {root : Root}
    (safe : ∀ earlier, first ≤ earlier → earlier < (e.world k).time →
      ∀ u ∈ J, ∀ n head, (e.world n).time = earlier →
      UpToDate config checks sources (e.world n).time ((e.world n).view u)
        ((e.world n).state u) →
      ((e.world n).state u).getHead config = .ok head →
      ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (aboveAnchor : anchorBlock.slot ≤ rootBlock.slot) {state : BeaconState preset fork}
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ last ∧ (e.world m).time ≤ last ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ last) with agree | collision
  swap
  · obtain ⟨⟨u, n⟩, ⟨hu, hn⟩, ⟨v, m⟩, ⟨hv, hm⟩, root, collision, found⟩ := collision
    exact .inr ⟨u, hu, v, hv, n, m, hn, hm, root, collision, found⟩
  have oneBlock (v : ValidatorIndex) (hv : v ∈ J) (u : ValidatorIndex) (hu : u ∈ J)
      (n k : ℕ) (hn : (e.world n).time ≤ last) (hk : (e.world k).time ≤ last) :=
    agree (v, n) ⟨hv, hn⟩ (u, k) ⟨hu, hk⟩
  left
  obtain ⟨attestation, m, seen, rfl, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchored start receiver latest
  obtain ⟨n, earlier, duty⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent k w seen) signed honest
  obtain ⟨committee, _, deadline, genesis, current, honestData, _⟩ := duty
  obtain ⟨startTime, due', startOk, dueOk', timeEq⟩ := deadline
  have dueEq := Except.ok.inj (dueOk'.symm.trans dueOk)
  subst due'
  obtain ⟨head, block, headState, headState', headOk, _, _, _, made⟩ := honestData
  have epochEq := target_epoch_eq_of_getAttestationData made
  have epochRank : epoch ≤ attestation.data.target.epoch := by
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  have beginLe : begin ≤ attestation.data.slot := by
    have floor := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (UInt64.le_iff_toNat_le.mp epochRank)
    rw [epochEq, computeEpochAtSlot, UInt64.toNat_div] at floor
    rw [UInt64.le_iff_toNat_le, (computeStartSlotAtEpoch_ok_iff.mp beginOk).2]
    exact floor.trans (Nat.div_mul_le_self _ _)
  obtain ⟨beginTime', beginOk', _, timeLe⟩ := exists_timeAtSlotMs_of_le beginLe startOk
  have same := Except.ok.inj (beginOk'.symm.trans beginTimeOk)
  subst beginTime'
  have firstLe : first ≤ (e.world n).time := by
    have timeLe := UInt64.le_iff_toNat_le.mp timeLe
    omega
  have before : (e.world n).time < (e.world k).time := by
    apply lt_of_le_of_ne (e.monotone_time earlier.le)
    intro sameTime
    have genesisEq : ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
      have left := (e.clock_bounds v n).1
      have right := (e.clock_bounds w k).1
      rw [start v honest] at left
      rw [start w receiver] at right
      exact right.trans (left.symm.trans genesis)
    have sameClock : ((e.world k).state w).timeMs = ((e.world n).state v).timeMs :=
      UInt64.toNat_inj.mp (upToDate.1.trans (sameTime.symm.trans current.1.symm))
    have slotOk : ((e.world k).state w).getCurrentSlot config =
        .ok attestation.data.slot := by
      unfold Store.getCurrentSlot
      rw [genesisEq, sameClock]
      exact mapError_ok_iff.mpr (computeSlotAtTimeMs_inside startOk
        (current.1.trans timeEq) inSlot)
    obtain ⟨slot, slotOk', past⟩ := origin.past
    have eq := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst slot
    exact UInt64.lt_irrefl _ past
  obtain ⟨_, _, _, dataRoot, _, _⟩ := getAttestationData_eq_ok_iff.mp made
  have supported := safe _ firstLe before v honest n head rfl current headOk
  obtain ⟨sourceBlock, sourceKnown⟩ :
      ∃ b, ((e.world n).state v).blocks[root]? = some b := by
    unfold Store.isAncestor at supported
    simp only [bind_ok_iff] at supported
    obtain ⟨b, found, _⟩ := supported
    exact ⟨b, Store.block_ok_iff.mp found⟩
  have sameBlock := oneBlock v honest w receiver n k
    ((e.monotone_time earlier.le).trans bounded) bounded root sourceBlock rootBlock sourceKnown
    known
  subst sourceBlock
  have reached := e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) k w receiver
  obtain ⟨tip, tipKnown, _⟩ := origin.voted
  have descends := Store.isAncestor_of_same_blocks reached preGloas
    (oneBlock v honest w receiver n k ((e.monotone_time earlier.le).trans bounded) bounded)
    sourceKnown known aboveAnchor ⟨tip, dataRoot ▸ tipKnown⟩ supported
  have pending := Store.getHead_pending preGloas headOk
  have headEq : head = ⟨attestation.data.beaconBlockRoot, .pending⟩ := by
    cases head
    simp_all
  rw [headEq] at descends
  have check : ((e.world k).state w).voteCountsFor ⟨root, .pending⟩ v = true := by
    apply Store.voteCountsFor_of_check _ latest (by simpa using counted)
    simpa only [Store.getSupportedNode_of_lt preGloas, bind, Except.bind,
      LatestMessage.ofAttestation] using descends
  simp only [List.mem_toFinset, List.mem_map] at active
  obtain ⟨entry, member, eq⟩ := active
  simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨entry, ⟨member, eq ▸ check⟩, eq⟩

/-- Finality compatibility admits the head, covers the prefix, or names a store collision. -/
private theorem blocks_or_justified_covers {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam) {last : ℕ}
    (admitted : BlocksAdmitted e 0 Δ last)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ last →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {n arrival endpoint : ℕ} (later : arrival ≤ endpoint)
    (bounded : (e.world endpoint).time ≤ last)
    (late : (e.world n).time + Δ ≤ (e.world arrival).time)
    (upToDate : UpToDate config checks sources (e.world arrival).time
      ((e.world arrival).view w) ((e.world arrival).state w))
    {head : ForkChoiceNode} {root : Root} {headBlock rootBlock : BeaconBlock preset fork}
    (headKnown : ((e.world n).state v).blocks[head.root]? = some headBlock)
    (sourceKnown : ((e.world n).state v).blocks[root]? = some rootBlock)
    (known : ((e.world endpoint).state w).blocks[root]? = some rootBlock)
    (supports : ((e.world n).state v).isAncestor head ⟨root, .pending⟩ = .ok true)
    (compatible : (∃ boundary,
      computeStartSlotAtEpoch preset ((e.world arrival).state w).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ rootBlock.slot ∧
      ((e.world endpoint).state w).getCheckpointBlock root
        ((e.world arrival).state w).finalizedCheckpoint.epoch =
          .ok ((e.world arrival).state w).finalizedCheckpoint.root) ∨
      ((e.world endpoint).state w).isAncestor
        ⟨((e.world arrival).state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) :
    (((e.world arrival).state w).blocks[head.root]? = some headBlock ∨
      ((e.world endpoint).state w).isAncestor
        ⟨((e.world endpoint).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ last ∧ (e.world m).time ≤ last ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ last) with agree | collision
  swap
  · obtain ⟨⟨u, n⟩, ⟨hu, hn⟩, ⟨v, m⟩, ⟨hv, hm⟩, root, collision, found⟩ := collision
    exact .inr ⟨u, hu, v, hv, n, m, hn, hm, root, collision, found⟩
  have oneBlock (v : ValidatorIndex) (hv : v ∈ J) (u : ValidatorIndex) (hu : u ∈ J)
      (n k : ℕ) (hn : (e.world n).time ≤ last) (hk : (e.world k).time ≤ last) :=
    agree (v, n) ⟨hv, hn⟩ (u, k) ⟨hu, hk⟩
  have arrivalBound := (e.monotone_time later).trans bounded
  rcases compatible with ⟨boundary, boundaryOk, belowRoot, checkpoint⟩ | covered
  · have finalRead := chain w receiver arrival arrival (le_refl _) arrivalBound
    obtain ⟨_, finalized, _, finalizedKnown, _, _⟩ :=
      Store.isAncestor_of_getCheckpointBlock preGloas finalRead
    have aboveAnchor : anchorBlock.slot ≤ boundary := by
      obtain ⟨_, _, _, _, _, initial, _, _⟩ := getForkchoiceStore_anchor anchored
      have epochs := (e.checkpointsAdvance_of_le w (Nat.zero_le arrival)).2.epoch_le
      simp only [Execution.world_zero, World.initial, start w receiver, initial] at epochs
      have floor := (computeStartSlotAtEpoch_ok_iff.mp
        (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot)).2
      have rounded : anchorState.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH =
          anchorState.slot := by
        apply epoch_floor_eq_of_sub_eq_zero
        simpa [isStartSlotAtEpoch, computeSlotsSinceEpochStart, anchorSlot,
          computeStartSlotAtEpoch_computeEpochAtSlot, Except.mapError, bind, Except.bind,
          pure, Except.pure] using anchorBoundary
      rw [rounded] at floor
      rw [anchorSlot, UInt64.le_iff_toNat_le,
        (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2, floor]
      exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp epochs)
    have sourceReached := e.reachable
      (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) n v honest
    have sourceCheckpoint := Store.getCheckpointBlock_of_same_blocks sourceReached
      (oneBlock w receiver v honest endpoint n bounded (by
        have clock := e.monotone_time later
        dsimp at clock
        omega)) boundaryOk aboveAnchor
      ⟨rootBlock, sourceKnown⟩ checkpoint
    have headCheckpoint := Store.getCheckpointBlock_of_isAncestor preGloas sourceKnown
      supports boundaryOk belowRoot sourceCheckpoint
    rcases e.blocks_of_partiallySynchronous sync preGloas admitted anchored start
      honest receiver (by simpa using late) arrivalBound upToDate ⟨finalized, finalizedKnown⟩
      headKnown headCheckpoint with delivered | collision
    · exact .inl (.inl delivered.1)
    · exact .inr collision
  · apply Or.inl ∘ Or.inr
    have checkpoint := chain w receiver arrival endpoint later bounded
    obtain ⟨_, finalized, _, held, _, descends⟩ :=
      Store.isAncestor_of_getCheckpointBlock preGloas checkpoint
    exact Store.isAncestor_trans_of_lt preGloas held known descends covered

/-- An epoch of honest votes gives support, justification coverage, or a store collision.

Each honest vote it assumes also passes the committee check in its target state.

A compatible finalized checkpoint gives the finality check of block validation.

The hypothesis on delayed blocks gives the rest of the block handler.

The root is assumed to fit each finalized checkpoint seen since the safe interval starts.

Finalized-prefix compatibility and nonzero state roots of held blocks are assumed. -/
private theorem Execution.mem_supportersOf_of_duty_epoch_core {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {first time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ∀ v ∈ J, ∀ slot committeeIndex deadline,
      assignment.committee v slot = some committeeIndex →
      IsAttestationDeadline fork config genesisTimeMs slot deadline →
      e.startTime ≤ deadline → deadline ≤ time →
      ∃ n attestation indexed, VoteAt e v slot committeeIndex deadline n attestation indexed ∧
        ∀ withTarget targetState,
          ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
            .ok withTarget →
          withTarget.checkpointState attestation.data.target = .ok targetState →
          checkAttestationCommittees targetState attestation = .ok ())
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (_sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (started : e.startTime ≤ first)
    {horizon : Epoch}
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (_inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {epoch : Epoch} {begin next : Slot} {beginTime endTime : UInt64}
    (beginOk : computeStartSlotAtEpoch preset epoch = .ok begin)
    (nextOk : addChecked begin preset.SLOTS_PER_EPOCH = .ok next)
    (beginTimeOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endTimeOk : computeTimeAtSlotMs config genesisTimeMs next = .ok endTime)
    (fresh : first ≤ beginTime.toNat) (complete : endTime.toNat ≤ time) {root : Root}
    (safe : ∀ earlier, first ≤ earlier → earlier < time → ∀ u ∈ J, ∀ n head,
      (e.world n).time = earlier →
      UpToDate config checks sources (e.world n).time ((e.world n).view u)
        ((e.world n).state u) →
      ((e.world n).state u).getHead config = .ok head →
      ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (rootFinal : ∀ k' ≤ k, first ≤ (e.world k').time →
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ rootBlock.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true)
    {state : BeaconState preset fork} {v : ValidatorIndex} (honest : v ∈ J)
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset)
    (duty : ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
      assignment.committee v slot = some committeeIndex) :
    (v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ time ∧ (e.world m).time ≤ time ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agree | collision
  swap
  · obtain ⟨⟨u, n⟩, ⟨hu, hn⟩, ⟨v, m⟩, ⟨hv, hm⟩, root, collision, found⟩ := collision
    exact .inr ⟨u, hu, v, hv, n, m, hn, hm, root, collision, found⟩
  have oneBlock (v : ValidatorIndex) (hv : v ∈ J) (u : ValidatorIndex) (hu : u ∈ J)
      (n k : ℕ) (hn : (e.world n).time ≤ time) (hk : (e.world k).time ≤ time) :=
    agree (v, n) ⟨hv, hn⟩ (u, k) ⟨hu, hk⟩
  have forward := fun u hu j => e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) j u hu
  have rootAbove := (forward w receiver k).reachable.anchorSlot_le
    (UInt64.le_of_eq anchorSlot) known
  obtain ⟨slot, committee, beginLe, slotLt, assigned⟩ := duty
  obtain ⟨followingSlot, slotTime, followingTime, deadline, n, attestation, indexed,
      nextSlotOk, slotTimeOk, followingTimeOk, deadlineOk, firstLe, beforeBoundary,
      boundaryLe, vote, committees⟩ := e.exists_voteAt_of_duty_interval votes fits
    beginTimeOk endTimeOk started fresh complete honest beginLe slotLt assigned
  obtain ⟨due, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextSlotOk slotTimeOk followingTimeOk dueOk
  obtain ⟨dataSlot, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, notFuture⟩ :=
    vote.data_head anchored (UInt64.le_of_eq anchorSlot) start honest deadlineOk dueOk dueLt
  have supports := safe deadline firstLe (by omega) v honest n head vote.atTime
    (vote.atTime.symm ▸ vote.upToDate) headOk
  have sourceKnown : ((e.world n).state v).blocks[root]? = some rootBlock := by
    have test := supports
    unfold Store.isAncestor at test
    simp only [bind_ok_iff] at test
    obtain ⟨block, held, _⟩ := test
    have held := Store.block_ok_iff.mp held
    have eq := oneBlock v honest w receiver n k (by rw [vote.atTime]; omega) (by omega)
      root block rootBlock held known
    exact eq ▸ held
  have genesis : ∀ j, ((e.world j).state w).genesisTimeMs = genesisTimeMs := by
    intro j
    have left := (e.clock_bounds v n).1
    have right := (e.clock_bounds w j).1
    rw [start v honest] at left
    rw [start w receiver] at right
    exact right.trans (left.symm.trans vote.genesis)
  obtain ⟨⟨pre, preTime, preLate, preCurrent⟩, ⟨boundary, boundaryTime, boundaryCurrent⟩⟩ :=
    e.exists_duty_boundaries fits (prompt.of_le boundaryLe) receiver nextSlotOk slotTimeOk
      followingTimeOk deadlineOk (started.trans firstLe)
  have preLe : pre ≤ k := by
    by_contra h
    have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp at bad
    omega
  rcases blocks_or_justified_covers sync preGloas admitted anchored start
      anchorSlot anchorBoundary chain honest receiver preLe (by omega)
      (by simpa [vote.atTime] using preLate) preCurrent headKnown sourceKnown known supports
      (rootFinal pre preLe (by omega) preCurrent) with delivered | collision
  swap
  · exact .inr collision
  rcases delivered with admittedHead | covered
  swap
  · exact .inl (.inr covered)
  have arrivalExists : ∃ arrival, pre ≤ arrival ∧ arrival ≤ k ∧
      (e.world arrival).time = followingTime.toNat ∧
      UpToDate config checks sources (e.world arrival).time ((e.world arrival).view w)
        ((e.world arrival).state w) := by
    by_cases same : followingTime.toNat = time
    · exact ⟨k, preLe, le_refl _, by omega, upToDate⟩
    · have boundaryBefore : boundary ≤ k := by
        by_contra h
        have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
        dsimp at bad
        omega
      have preBefore : pre ≤ boundary := by
        by_contra h
        have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
        dsimp at bad
        omega
      exact ⟨boundary, preBefore, boundaryBefore, boundaryTime, boundaryCurrent⟩
  obtain ⟨arrival, preArrival, arrivalLe, arrivalTime, arrivalCurrent⟩ := arrivalExists
  have currentOk : ((e.world arrival).state w).getCurrentSlot config = .ok followingSlot := by
    unfold Store.getCurrentSlot
    rw [genesis arrival]
    have clock : ((e.world arrival).state w).timeMs = followingTime :=
      UInt64.toNat_inj.mp (arrivalCurrent.1.trans arrivalTime)
    rw [clock]
    exact mapError_ok_iff.mpr (computeSlotAtTimeMs_computeTimeAtSlotMs slots followingTimeOk)
  have votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some headBlock := dataRoot ▸ e.blocks_of_le preArrival admittedHead
  have targetRead := vote.data_target anchored anchorSlot anchorBoundary start honest
    (nonzero v honest n (by rw [vote.atTime]; omega))
  obtain ⟨targetBoundary, targetBlock, targetBoundaryOk, targetKnown, targetLe, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas targetRead
  have targetAbove := (forward v honest n).reachable.anchorSlot_le
    (UInt64.le_of_eq anchorSlot) targetKnown
  have receiverRead := Store.getCheckpointBlock_of_same_blocks
    (forward w receiver arrival).reachable (oneBlock v honest w receiver n arrival
      (by rw [vote.atTime]; omega) (by omega))
    targetBoundaryOk (UInt64.le_trans targetAbove targetLe) ⟨headBlock, votedKnown⟩ targetRead
  have anchorEmpty := Store.getForkchoiceStore_equivocatingIndices anchored
  have counted := fun j member => e.equivocatingIndices_honest slots
    (fun u hu v hv => by simp [start u hu, anchorEmpty] at hv)
    j receiver v member honest
  rcases vote.recorded_at_next_slot (last := time) sync preGloas anchored start
      honest receiver committees dataSlot dataEpoch nextSlotOk currentOk (by omega)
      arrivalCurrent (counted arrival) arrivalLe (by omega) votedKnown notFuture receiverRead with
    ⟨latest, latestOk, rank⟩ | collision
  swap
  · exact .inr collision
  have dutyEpoch : computeEpochAtSlot preset slot = epoch := by
    have b := (computeStartSlotAtEpoch_ok_iff.mp beginOk).2
    have nx := (addChecked_ok_iff.mp nextOk).2
    have lo := UInt64.le_iff_toNat_le.mp beginLe
    have hi := UInt64.lt_iff_toNat_lt.mp slotLt
    apply UInt64.toNat_inj.mp
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
  exact (mem_supportersOf_of_latest_rank anchored start preGloas honest receiver
    latestOk (counted k) upToDate (by omega) dueOk dueLt beginOk beginTimeOk fresh
    (by simpa [dataEpoch, dutyEpoch] using rank)
    (fun earlier hfirst htime => safe earlier hfirst (by omega)) known rootAbove active).imp
      Or.inl id

/-- Restrict finalized-prefix compatibility to ordered events of one honest validator. -/
private theorem finalized_prefix_of_chain {anchor : Store preset fork} {time : ℕ} {horizon : Epoch}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (chain : ∀ u ∈ J, ∀ w ∈ J, ∀ n k, (e.world n).time ≤ time → (e.world k).time ≤ time →
      ∀ checkpoint : Checkpoint,
      (checkpoint = ((e.world k).state w).justifiedCheckpoint ∨
        checkpoint = ((e.world k).state w).unrealizedJustifiedCheckpoint) →
      ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch →
      checkpoint.epoch ≤ horizon →
      ((e.world k).state w).getCheckpointBlock checkpoint.root
        ((e.world n).state u).finalizedCheckpoint.epoch =
          .ok ((e.world n).state u).finalizedCheckpoint.root)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon) :
    ∀ u ∈ J, ∀ i j, i ≤ j → (e.world j).time ≤ time →
      ((e.world j).state u).getCheckpointBlock ((e.world j).state u).justifiedCheckpoint.root
        ((e.world i).state u).finalizedCheckpoint.epoch =
          .ok ((e.world i).state u).finalizedCheckpoint.root := by
  intro u hu i j le bounded
  have forward := e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) j u hu
  obtain ⟨current, currentOk, _, _⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have epochOk : ((e.world j).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  exact chain u hu u hu i j ((e.monotone_time le).trans bounded) bounded _ (.inl rfl)
    (UInt64.le_trans (e.checkpointsAdvance_of_le u le).2.epoch_le
      (forward.reachable.finalized_le_justified sound))
    (UInt64.le_trans (forward.justified_epoch_le_current sound slots
      (UInt64.le_of_eq anchorSlot) epochOk).1 (inHorizon u hu j _ bounded epochOk))

/-- An epoch of honest votes gives support, justification coverage, or a store collision. -/
theorem Execution.mem_supportersOf_of_duty_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {first time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ∀ v ∈ J, ∀ slot committeeIndex deadline,
      assignment.committee v slot = some committeeIndex →
      IsAttestationDeadline fork config genesisTimeMs slot deadline →
      e.startTime ≤ deadline → deadline ≤ time →
      ∃ n attestation indexed, VoteAt e v slot committeeIndex deadline n attestation indexed ∧
        ∀ withTarget targetState,
          ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
            .ok withTarget →
          withTarget.checkpointState attestation.data.target = .ok targetState →
          checkAttestationCommittees targetState attestation = .ok ())
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (started : e.startTime ≤ first)
    {horizon : Epoch}
    (chain : ∀ u ∈ J, ∀ w ∈ J, ∀ n k, (e.world n).time ≤ time → (e.world k).time ≤ time →
      ∀ checkpoint : Checkpoint,
      (checkpoint = ((e.world k).state w).justifiedCheckpoint ∨
        checkpoint = ((e.world k).state w).unrealizedJustifiedCheckpoint) →
      ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch →
      checkpoint.epoch ≤ horizon →
      ((e.world k).state w).getCheckpointBlock checkpoint.root
        ((e.world n).state u).finalizedCheckpoint.epoch =
          .ok ((e.world n).state u).finalizedCheckpoint.root)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {epoch : Epoch} {begin next : Slot} {beginTime endTime : UInt64}
    (beginOk : computeStartSlotAtEpoch preset epoch = .ok begin)
    (nextOk : addChecked begin preset.SLOTS_PER_EPOCH = .ok next)
    (beginTimeOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endTimeOk : computeTimeAtSlotMs config genesisTimeMs next = .ok endTime)
    (fresh : first ≤ beginTime.toNat) (complete : endTime.toNat ≤ time) {root : Root}
    (safe : ∀ earlier, first ≤ earlier → earlier < time → ∀ u ∈ J, ∀ n head,
      (e.world n).time = earlier →
      UpToDate config checks sources (e.world n).time ((e.world n).view u)
        ((e.world n).state u) →
      ((e.world n).state u).getHead config = .ok head →
      ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (rootFinal : ∀ k' ≤ k, first ≤ (e.world k').time →
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ rootBlock.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true)
    {state : BeaconState preset fork} {v : ValidatorIndex} (honest : v ∈ J)
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset)
    (duty : ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
      assignment.committee v slot = some committeeIndex) :
    (v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true) ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ time ∧ (e.world m).time ≤ time ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  exact e.mem_supportersOf_of_duty_epoch_core sync slots preGloas admitted votes fits prompt
    anchored sound anchorSlot anchorBoundary start started
    (finalized_prefix_of_chain anchored sound start slots anchorSlot chain inHorizon)
    inHorizon nonzero beginOk nextOk beginTimeOk endTimeOk fresh complete safe receiver atTime
    upToDate known rootFinal honest active duty

end EthLib.Consensus.Models.Network

namespace EthLib.Consensus.Store

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {store : Store preset fork}

/-- A viable node has a viable leaf below it, by descent through the shared child theorem. -/
private theorem viable_leaf_below (lower : store.ParentsBelow)
    (before : fork < .glamsterdam) {start : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (tree : store.filterNodeTree config start = .ok nodes) :
    ∀ node ∈ nodes, ∃ leaf ∈ nodes, store.isViableLeaf config leaf = .ok true ∧
      (blockTree lower).Ancestor (some node.root) (some leaf.root) := by
  intro node
  induction rank : store.nodeRank node using Nat.strongRecOn generalizing node with
  | _ rank ih =>
  intro member
  let children := (store.blocks.toList.filter fun (_, block) =>
    block.parentRoot = node.root).map fun (root, _) => (⟨root, .pending⟩ : ForkChoiceNode)
  have childrenOk : store.getNodeChildren node = .ok children := by
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    simp only [getNodeChildren, notGloas, false_and, ↓reduceDIte, ↓reduceIte,
      pure, Except.pure]
    rfl
  by_cases empty : children = []
  · exact ⟨node, member, filterNodeTree_leaf tree node member childrenOk
      (by simp [empty]), .refl _⟩
  obtain ⟨child, childMem, childIn⟩ := filterNodeTree_child tree node member childrenOk empty
  obtain ⟨pending, block, found, parent⟩ := (mem_getNodeChildren before childrenOk).mp childMem
  obtain ⟨parentBlock, parentFound⟩ := (filterNodeTree_mem tree node member).2.1
  have slots := lower child.root block parentBlock found (parent ▸ parentFound)
  have decrease : store.nodeRank child < store.nodeRank node := by
    simp only [nodeRank, found, parentFound, pending, ↓reduceIte]
    have lo := block.slot.toNat_lt
    have hi := parentBlock.slot.toNat_lt
    have strict := UInt64.lt_iff_toNat_lt.mp slots
    split <;> omega
  obtain ⟨leaf, leafIn, viable, above⟩ := ih _ (rank ▸ decrease) child rfl childIn
  exact ⟨leaf, leafIn, viable,
    (blockTree_isChild_iff.mpr ⟨block, found, parent⟩).ancestor.trans above⟩

end EthLib.Consensus.Store

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Viability places earlier finalized checkpoints below the root unless justification covers it. -/
private theorem rootFinal_or_justified_covers {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {last : ℕ}
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ last →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ last)
    (lower : ((e.world k).state w).ParentsBelow)
    {root : Root} {rootBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    {nodes : List ForkChoiceNode}
    (treeOk : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (covered : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ∀ k' ≤ k, ∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ rootBlock.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root := by
  rcases covered with covers | inTree
  · exact .inl covers
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have reached := e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) k w receiver
  have split {r c : Root} {ep : Epoch}
      (read : ((e.world k).state w).getCheckpointBlock r ep = .ok c) :
      ∃ boundary anc, computeStartSlotAtEpoch preset ep = .ok boundary ∧
        ((e.world k).state w).getAncestor ⟨r, .pending⟩ boundary = .ok anc ∧ anc.root = c := by
    unfold Store.getCheckpointBlock at read
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
    obtain ⟨boundary, boundaryOk, anc, walk, eq⟩ := read
    exact ⟨boundary, anc, mapError_ok_iff.mp boundaryOk, walk, eq⟩
  have walkTo {tip node : Root} {tipBlock nodeBlock : BeaconBlock preset fork}
      (tipFound : ((e.world k).state w).blocks[tip]? = some tipBlock)
      (nodeFound : ((e.world k).state w).blocks[node]? = some nodeBlock)
      (above : (Store.blockTree lower).Ancestor (some node) (some tip)) :
      ((e.world k).state w).getAncestor ⟨tip, .pending⟩ nodeBlock.slot = .ok ⟨node, .pending⟩ := by
    obtain ⟨anc, walk⟩ := Store.getAncestor_ok_of_orphans_le lower (slot := nodeBlock.slot)
      (node := ⟨tip, .pending⟩)
      (fun r b found orphan => reached.orphans_le (UInt64.le_of_eq anchorSlot) found orphan
        nodeFound) tipFound
    have ancRoot := Store.getAncestor_root_eq (lower := lower) (node := ⟨node, .pending⟩)
      nodeFound walk above
    have ancPending := Store.getAncestor_pending_of_lt preGloas rfl walk
    obtain ⟨r, s⟩ := anc
    simp only at ancRoot ancPending
    subst ancRoot ancPending
    exact walk
  set justified := ((e.world k).state w).justifiedCheckpoint
  have treeWalk : ((e.world k).state w).filterNodeTree config ⟨justified.root, .pending⟩ =
      .ok nodes := treeOk
  obtain ⟨justifiedIn, -, -⟩ := Store.filterNodeTree_mem treeWalk _ inTree
  obtain ⟨-, ⟨justifiedBlock, justifiedFound⟩, -⟩ :=
    Store.filterNodeTree_mem treeWalk _ justifiedIn
  have below := (Store.filterNodeTree_ancestor (lower := lower) preGloas treeWalk _ inTree).1
  by_cases same : root = justified.root
  · left
    subst same
    exact Store.isAncestor_self (node := ⟨justified.root, .pending⟩) known
  right
  have rootWalk := walkTo known justifiedFound below
  have descends : ((e.world k).state w).isAncestor ⟨root, .pending⟩
      ⟨justified.root, .pending⟩ = .ok true := by
    simp [Store.isAncestor, Store.block_ok_iff.mpr justifiedFound, rootWalk, later, bind,
      Except.bind, pure, Except.pure]
  obtain ⟨rootBlock', rootFound', justifiedLe⟩ :=
    Store.slot_le_of_isAncestor justifiedFound descends
  rw [known, Option.some.injEq] at rootFound'
  subst rootBlock'
  intro k' earlier
  have finalLe := (e.checkpointsAdvance_of_le w earlier).2.epoch_le
  have read := chain w receiver k' k earlier bounded
  obtain ⟨boundary, anc, boundaryOk, walk, ancRoot⟩ := split read
  refine ⟨boundary, boundaryOk, ?_⟩
  by_cases early : boundary ≤ justifiedBlock.slot
  · exact ⟨UInt64.le_trans early justifiedLe,
      Store.getCheckpointBlock_of_isAncestor preGloas justifiedFound descends boundaryOk early read⟩
  have late : justifiedBlock.slot ≤ boundary := UInt64.le_of_lt (UInt64.not_le.mp early)
  rw [Store.getAncestor_of_le justifiedFound late, Except.ok.injEq] at walk
  subst walk
  have finalRoot : ((e.world k').state w).finalizedCheckpoint.root = justified.root := ancRoot.symm
  have readNow := chain w receiver k k (le_refl _) bounded
  obtain ⟨boundaryNow, ancNow, boundaryNowOk, walkNow, ancNowRoot⟩ := split readNow
  have boundaryLe : boundary ≤ boundaryNow := by
    have h1 := computeStartSlotAtEpoch_ok_iff.mp boundaryOk
    have h2 := computeStartSlotAtEpoch_ok_iff.mp boundaryNowOk
    have h3 := UInt64.le_iff_toNat_le.mp finalLe
    apply UInt64.le_iff_toNat_le.mpr
    rw [h1.2, h2.2]
    exact Nat.mul_le_mul_right _ h3
  have lateNow : justifiedBlock.slot ≤ boundaryNow := UInt64.le_trans late boundaryLe
  rw [Store.getAncestor_of_le justifiedFound lateNow, Except.ok.injEq] at walkNow
  subst walkNow
  have notGenesis : ((e.world k).state w).finalizedCheckpoint.epoch ≠ GENESIS_EPOCH := by
    intro genesis
    have h := (computeStartSlotAtEpoch_ok_iff.mp boundaryNowOk).2
    rw [genesis] at h
    have zero : boundaryNow.toNat = 0 := by simpa [GENESIS_EPOCH] using h
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp early)
    have := UInt64.le_iff_toNat_le.mp boundaryLe
    omega
  obtain ⟨leaf, leafIn, viable, leafAbove⟩ :=
    Store.viable_leaf_below lower preGloas treeWalk _ inTree
  obtain ⟨-, ⟨leafBlock, leafFound⟩, -⟩ := Store.filterNodeTree_mem treeWalk _ leafIn
  have leafRead := (Store.isViableLeaf_finalized viable).resolve_left notGenesis
  obtain ⟨boundaryLeaf, ancLeaf, boundaryLeafOk, leafWalk, ancLeafRoot⟩ := split leafRead
  rw [boundaryNowOk, Except.ok.injEq] at boundaryLeafOk
  subst boundaryLeafOk
  have ancLeafPending := Store.getAncestor_pending_of_lt preGloas rfl leafWalk
  have ancLeafEq : ancLeaf = ⟨justified.root, .pending⟩ := by
    obtain ⟨r, s⟩ := ancLeaf
    have nowRoot : ((e.world k).state w).finalizedCheckpoint.root = justified.root :=
      ancNowRoot.symm
    simp only at ancLeafRoot ancLeafPending
    rw [ancLeafPending, ancLeafRoot, nowRoot]
  rw [ancLeafEq] at leafWalk
  have leafToRoot := walkTo leafFound known leafAbove
  have rootLate : boundaryNow < rootBlock.slot := by
    by_contra notLate
    have le := UInt64.not_lt.mp notLate
    have through := Store.getAncestor_trans le leafWalk
    rw [leafToRoot, Store.getAncestor_of_le justifiedFound justifiedLe, Except.ok.injEq] at through
    exact same (congrArg ForkChoiceNode.root through)
  refine ⟨UInt64.le_trans boundaryLe (UInt64.le_of_lt rootLate), ?_⟩
  have viaRoot := Store.getAncestor_trans
    (UInt64.le_trans boundaryLe (UInt64.le_of_lt rootLate)) leafToRoot
  have viaJustified := Store.getAncestor_trans boundaryLe leafWalk
  rw [Store.getAncestor_of_le justifiedFound late] at viaJustified
  rw [viaJustified] at viaRoot
  simp [Store.getCheckpointBlock, boundaryOk, ← viaRoot, finalRoot, Except.mapError, bind,
    Except.bind, pure, Except.pure]

open scoped Classical in
/-- An honest duty majority preserves the safe head chain, or bounded stores name a collision.

The parent safety induction supplies the visited parent; the head walk supplies its score read.

A compatible finalized checkpoint gives the finality check of block validation.

The hypothesis on delayed blocks gives the rest of the block handler.

Finalized-prefix compatibility, nonzero state roots and the absent anchor parent are assumed. -/
private theorem Execution.isAncestor_getHead_of_duty_epoch_core {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {first time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ∀ v ∈ J, ∀ slot committeeIndex deadline,
      assignment.committee v slot = some committeeIndex →
      IsAttestationDeadline fork config genesisTimeMs slot deadline →
      e.startTime ≤ deadline → deadline ≤ time →
      ∃ n attestation indexed, VoteAt e v slot committeeIndex deadline n attestation indexed ∧
        ∀ withTarget targetState,
          ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
            .ok withTarget →
          withTarget.checkpointState attestation.data.target = .ok targetState →
          checkAttestationCommittees targetState attestation = .ok ())
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (started : e.startTime ≤ first)
    {horizon : Epoch}
    (chain : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {root : Root}
    (safe : ∀ earlier, first ≤ earlier → earlier < time → ∀ u ∈ J, ∀ n head,
      (e.world n).time = earlier →
      UpToDate config checks sources (e.world n).time ((e.world n).view u)
        ((e.world n).state u) →
      ((e.world n).state u).getHead config = .ok head →
      ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    {block : BeaconBlock preset fork}
    (parentSafe : ∀ u ∈ J, ∀ n head, (e.world n).time = time →
      UpToDate config checks sources (e.world n).time ((e.world n).view u)
        ((e.world n).state u) →
      ((e.world n).state u).getHead config = .ok head →
      ((e.world n).state u).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (coverage : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    [DecidablePred (· ∈ J)]
    (margin : ∃ (epoch : Epoch) (begin next : Slot) (beginTime endTime : UInt64),
      computeStartSlotAtEpoch preset epoch = .ok begin ∧
      addChecked begin preset.SLOTS_PER_EPOCH = .ok next ∧
      computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime ∧
      computeTimeAtSlotMs config genesisTimeMs next = .ok endTime ∧
      first ≤ beginTime.toNat ∧ endTime.toNat ≤ time ∧
      Models.stake (fun v => balanceAt state v.toNat)
          ((unslashedActiveBalances state).map (·.1)).toFinset +
          ((e.world k).state w).boostScore config <
        2 * Models.stake (fun v => balanceAt state v.toNat)
          {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧
            ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
              assignment.committee v slot = some committeeIndex})
    (headOk : ((e.world k).state w).getHead config = .ok head) :
    ((e.world k).state w).isAncestor head ⟨root, .pending⟩ = .ok true ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ time ∧ (e.world m).time ≤ time ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  classical
  by_cases collision : ∃ u ∈ J, ∃ v ∈ J, ∃ n m,
      (e.world n).time ≤ time ∧ (e.world m).time ≤ time ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision
  · exact .inr collision
  left
  by_cases covered : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true
  · obtain ⟨justified, held, _⟩ := Store.slot_le_of_isAncestor known covered
    exact Store.isAncestor_trans_of_lt preGloas held
      known (Store.isAncestor_getHead_of_lt_gloas preGloas headOk) covered
  have reached := e.reachable
    (fun u hu => (start u hu) ▸ Store.Reachable.anchor anchored) k w receiver
  have lower := reached.parentsBelow (UInt64.le_of_eq anchorSlot)
    (anchorParent w receiver k (by omega))
  have rootFinal := (rootFinal_or_justified_covers anchored start anchorSlot
    preGloas chain receiver (by omega) lower known tree coverage).resolve_left covered
  have parentAbove := parentSafe w receiver k head atTime upToDate headOk
  have parentRead := parentAbove
  unfold Store.isAncestor at parentRead
  simp only [bind_ok_iff] at parentRead
  obtain ⟨parent, parentOk, _⟩ := parentRead
  obtain ⟨epoch, begin, next, beginTime, endTime, beginOk, nextOk, beginTimeOk, endTimeOk,
    fresh, complete, majority⟩ := margin
  apply Store.isAncestor_getHead_of_duty_support
    (fun v => ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
      assignment.committee v slot = some committeeIndex)
    (BeaconState.registryWithinLimit_of_lt preGloas state) lower preGloas stateOk tree
    (coverage.resolve_left covered) known (Store.block_ok_iff.mp parentOk) parentAbove ?_
    majority headOk
  intro v active honest duty
  rcases e.mem_supportersOf_of_duty_epoch_core sync slots preGloas admitted votes fits prompt
    anchored sound anchorSlot anchorBoundary start started chain inHorizon nonzero beginOk nextOk
    beginTimeOk endTimeOk fresh complete safe receiver atTime upToDate known
    (fun j le _ _ => Or.inl (rootFinal j le)) honest active duty with support | found
  · exact support.resolve_right covered
  · exact False.elim (collision found)

open scoped Classical in
/-- An honest-duty margin places the safe root on the head chain, or names a store collision. -/
theorem Execution.isAncestor_getHead_of_duty_epoch {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {first time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (votes : ∀ v ∈ J, ∀ slot committeeIndex deadline,
      assignment.committee v slot = some committeeIndex →
      IsAttestationDeadline fork config genesisTimeMs slot deadline →
      e.startTime ≤ deadline → deadline ≤ time →
      ∃ n attestation indexed, VoteAt e v slot committeeIndex deadline n attestation indexed ∧
        ∀ withTarget targetState,
          ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
            .ok withTarget →
          withTarget.checkpointState attestation.data.target = .ok targetState →
          checkAttestationCommittees targetState attestation = .ok ())
    (fits : DelayFits fork config genesisTimeMs Δ) (prompt : Prompt e time)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (started : e.startTime ≤ first)
    {horizon : Epoch}
    (chain : ∀ u ∈ J, ∀ w ∈ J, ∀ n k, (e.world n).time ≤ time → (e.world k).time ≤ time →
      ∀ checkpoint : Checkpoint,
      (checkpoint = ((e.world k).state w).justifiedCheckpoint ∨
        checkpoint = ((e.world k).state w).unrealizedJustifiedCheckpoint) →
      ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch →
      checkpoint.epoch ≤ horizon →
      ((e.world k).state w).getCheckpointBlock checkpoint.root
        ((e.world n).state u).finalizedCheckpoint.epoch =
          .ok ((e.world n).state u).finalizedCheckpoint.root)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {root : Root}
    (safe : ∀ earlier, first ≤ earlier → earlier < time → ∀ u ∈ J, ∀ n head,
      (e.world n).time = earlier →
      UpToDate config checks sources (e.world n).time ((e.world n).view u)
        ((e.world n).state u) →
      ((e.world n).state u).getHead config = .ok head →
      ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true)
    {block : BeaconBlock preset fork}
    (parentSafe : ∀ u ∈ J, ∀ n head, (e.world n).time = time →
      UpToDate config checks sources (e.world n).time ((e.world n).view u)
        ((e.world n).state u) →
      ((e.world n).state u).getHead config = .ok head →
      ((e.world n).state u).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (coverage : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    [DecidablePred (· ∈ J)]
    (margin : ∃ (epoch : Epoch) (begin next : Slot) (beginTime endTime : UInt64),
      computeStartSlotAtEpoch preset epoch = .ok begin ∧
      addChecked begin preset.SLOTS_PER_EPOCH = .ok next ∧
      computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime ∧
      computeTimeAtSlotMs config genesisTimeMs next = .ok endTime ∧
      first ≤ beginTime.toNat ∧ endTime.toNat ≤ time ∧
      Models.stake (fun v => balanceAt state v.toNat)
          ((unslashedActiveBalances state).map (·.1)).toFinset +
          ((e.world k).state w).boostScore config <
        2 * Models.stake (fun v => balanceAt state v.toNat)
          {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧
            ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
              assignment.committee v slot = some committeeIndex})
    (headOk : ((e.world k).state w).getHead config = .ok head) :
    ((e.world k).state w).isAncestor head ⟨root, .pending⟩ = .ok true ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ time ∧ (e.world m).time ≤ time ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  classical
  exact e.isAncestor_getHead_of_duty_epoch_core sync slots preGloas admitted votes fits prompt
    anchored sound anchorSlot anchorBoundary start started
    (finalized_prefix_of_chain anchored sound start slots anchorSlot chain inHorizon)
    inHorizon nonzero anchorParent safe parentSafe receiver atTime upToDate known stateOk tree
    coverage margin headOk

end EthLib.Consensus.Models.Network
