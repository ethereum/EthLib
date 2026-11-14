module

public import EthLib.Consensus.Proofs.Models.Network.ForkChoice
public import EthLib.Consensus.Proofs.ForkChoice.VoteRecords
public import EthLib.Consensus.Proofs.Time
public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Conditional delivery of accepted votes

Under synchrony, an honest receiver sees an honest vote one delay after it was sent.

An up-to-date receiver that accepts the attestation records its signer's vote.

The receiver retains a vote of at least that rank at every later event.

Acceptance and agreement on the indexed attestation are explicit hypotheses.

Synchrony alone does not establish handler success.

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
  obtain ⟨head, block, headState, state, headOk, found, stored, advanced, made⟩ := vote.honestData
  have stored' := Store.blockState_ok_iff.mp stored
  obtain ⟨-, boundary, -, dataRoot, -, epoch⟩ := getAttestationData_eq_ok_iff.mp made
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
  have firstOk : computeStartSlotAtEpoch preset attestation.data.target.epoch = .ok first := by
    rw [epoch]
    exact computeStartSlotAtEpoch_computeEpochAtSlot state.slot
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
  rw [dataRoot]
  unfold Store.getCheckpointBlock
  rw [firstOk]
  simp only [Except.mapError, bind, Except.bind]
  change (·.root) <$> ((e.world n).state v).getAncestor ⟨head.root, .pending⟩ first = _
  rcases getEpochBoundaryBlockRoot_eq_ok_iff.mp boundary with ⟨onBoundary, targetEq⟩ | ⟨-, read⟩
  · have eq : first = state.slot := div_mul_eq_self_iff.mpr onBoundary
    rw [eq, Store.getAncestor_of_le (node := ⟨head.root, .pending⟩) found headLe]
    simp [targetEq]
  · have read' : getBlockRootAtSlot state first = .ok attestation.data.target.root := by
      unfold getBlockRoot at read
      rw [← epoch, firstOk] at read
      exact read
    have firstAfter : anchorState.slot ≤ first := by
      have rounded : anchorState.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH =
          anchorState.slot := by
        apply epoch_floor_eq_of_sub_eq_zero
        simpa [isStartSlotAtEpoch, computeSlotsSinceEpochStart, anchorSlot,
          computeStartSlotAtEpoch_computeEpochAtSlot, Except.mapError, bind, Except.bind,
          pure, Except.pure] using anchorAtBoundary
      have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
        (Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
          (UInt64.le_iff_toNat_le.mp anchorLe))
      have a := (computeStartSlotAtEpoch_ok_iff.mp
        (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot)).2
      have b := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
      rw [rounded] at a
      simp only [computeEpochAtSlot, UInt64.toNat_div] at a
      rw [epoch] at b
      simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] at b
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    obtain ⟨targetBlock, targetKnown⟩ := known
    exact reachable.lookahead_history_ancestor (UInt64.le_of_eq anchorSlot) nonzero
      stored' targetKnown advanced read' firstAfter .pending

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

/-- A duty inside a complete slot interval has a valid committee vote before the delivery cutoff.

Each vote it assumes also passes the committee check in its target state. -/
theorem Execution.exists_voteAt_of_duty_interval {Δ : ℕ} {first time : ℕ}
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
    (fits : DelayFits fork config genesisTimeMs Δ)
    {begin last slot : Slot} {beginTime endTime : UInt64}
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
      ∀ withTarget targetState,
        ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
          .ok withTarget →
        withTarget.checkpointState attestation.data.target = .ok targetState →
        checkAttestationCommittees targetState attestation = .ok () := by
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
    votes v honest slot committeeIndex _ duty deadline
    (started.trans firstLe)
    (by have := fits.before_boundary nextOk startOk followingOk deadline; omega)
  exact ⟨slot + 1, startTime, following, _, n, attestation, indexed,
    nextOk, startOk, followingOk, deadline, firstLe,
    fits.before_boundary nextOk startOk followingOk deadline, by omega, vote, committees⟩

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
  obtain ⟨withTarget, targetState, stored, found, indexedOk, signed⟩ := reads
  have result : after =
      withTarget.updateLatestMessages indexed.attestingIndices.data.toList attestation := by
    unfold Store.onAttestation at accepted
    cases valid : store.validateOnAttestation config attestation false with
    | error err => simp [valid, bind, Except.bind] at accepted
    | ok value =>
      cases value
      simp only [valid, stored, found, indexedOk, signed, bind, Except.bind, Except.mapError,
        ↓reduceIte] at accepted
      cases committees : checkAttestationCommittees targetState attestation <;>
        simp_all [pure, Except.pure]
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

private theorem Store.exists_storeTargetCheckpointState {store : Store preset fork}
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
  have baseEq := e.blockStates_eq anchored honest receiver (start v honest) (start w receiver)
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

/-- A delivered duty is recorded and retained, or bounded honest stores name a collision. -/
theorem VoteAt.recorded_at_next_slot {Δ : ℕ} (sync : e.Synchronous Δ)
    (preGloas : fork < .glamsterdam) {anchor : Store preset fork}
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
    (epoch : attestation.data.target.epoch = computeEpochAtSlot preset slot)
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
      attestation.data.target.epoch ≤ message.rank) ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ last ∧ (e.world m).time ≤ last ∧
      ∃ root collision, EthLib.Consensus.Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  obtain ⟨_, target, _, targetKnown, _, _⟩ :=
    EthLib.Consensus.Store.isAncestor_of_getCheckpointBlock preGloas checkpoint
  have past : attestation.data.slot < next := UInt64.lt_iff_toNat_lt.mpr (by
    have sum := (addChecked_ok_iff.mp (dataSlot ▸ nextOk)).2
    simp only [UInt64.toNat_one] at sum
    omega)
  have valid := validateOnAttestation_of_facts currentOk
    ((epoch.trans (congrArg (computeEpochAtSlot preset) dataSlot).symm) ▸
      epoch_recent_at_next_slot (dataSlot ▸ nextOk))
    (epoch.trans (congrArg (computeEpochAtSlot preset) dataSlot).symm)
    targetKnown votedKnown (dataSlot ▸ notFuture)
    (fun gloas => False.elim (Nat.not_le_of_lt preGloas gloas)) checkpoint past
  rcases vote.accepted_of_target_known anchored start honest receiver committees
      (by have := vote.atTime; omega) arrivalBound targetKnown valid with
    ⟨⟨after, accepted⟩, reads⟩ | collision
  swap
  · exact .inr collision
  obtain ⟨message, latest, rank⟩ := vote.recorded_of_le sync honest receiver late upToDate
    accepted reads counted later
  refine .inl ⟨message, latest, ?_⟩
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank

end EthLib.Consensus.Models.Network
