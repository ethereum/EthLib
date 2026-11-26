module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.HeadTotality
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.RootViability
import EthLib.Consensus.Proofs.ForkChoice.Network
import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery
import EthLib.Consensus.Proofs.HonestAggregation
import EthLib.Consensus.Proofs.ForkChoice.StoreEntries
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin

/-!
# Proofs: up-to-date honest stores have a head

At every fork, an up-to-date honest store can compute its head.

The exceptions are a collision of bounded honest stores, and direct-safety evidence from a store.

This is part of [#2060][issue].

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

/-! ## The viable nodes can be computed -/

/-- A monadic flat map succeeds when it succeeds on each element. -/
private theorem flatMapM_exists_ok {α β ε : Type} {f : α → Except ε (List β)} :
    ∀ {xs : List α}, (∀ x ∈ xs, ∃ ys, f x = .ok ys) → ∃ ys, xs.flatMapM f = .ok ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, each => by
    obtain ⟨first, firstOk⟩ := each x List.mem_cons_self
    obtain ⟨rest, restOk⟩ :=
      flatMapM_exists_ok (xs := xs) fun y member => each y (List.mem_cons_of_mem x member)
    rw [List.flatMapM_cons]
    simp only [firstOk, restOk, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩

section ViableNodes

variable {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- Before Gloas, the voting source of a held block reads, at most the store's current epoch. -/
private theorem getVotingSource_le
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) {epoch : Epoch}
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch) {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    ∃ source, store.getVotingSource config root = .ok source ∧ source.epoch ≤ epoch := by
  have reachable := forward.reachable
  have holds : store.StatesHold := (reachable.ordered sound).2
  -- A held state's justification, pulled up or not, is no later than its epoch.
  have pulledLe : ∀ {r : Root} {state pulled : BeaconState preset fork},
      store.blockStates[r]? = some state → processJustificationAndFinalization state = .ok pulled →
      pulled.currentJustifiedCheckpoint.epoch ≤ epoch := fun stateFound pulledOk =>
    UInt64.le_trans (processJustificationAndFinalization_invariant (holds stateFound).ordered
      (holds stateFound).settled pulledOk).2.2.1
      (forward.blockState_epoch_le_current slots anchorSlot epochOk _ _ stateFound)
  have blockOk : store.block root = .ok block := Store.block_ok_iff.mpr found
  unfold Store.getVotingSource
  simp only [blockOk, epochOk, bind, Except.bind]
  split
  · have known : store.blocks.contains root := by
      rw [Std.TreeMap.contains_eq_isSome_getElem?, found]
      rfl
    obtain ⟨checkpoint, entry⟩ :=
      Option.isSome_iff_exists.mp (reachable.unrealizedJustification_isSome known)
    simp only [entry]
    refine ⟨checkpoint, rfl, ?_⟩
    rcases reachable.unrealizedJustification_origin entry with ⟨same, anchorHeld⟩ |
      ⟨state, pulled, stateFound, pulledOk, rfl⟩
    · rw [same]
      exact forward.blockState_epoch_le_current slots anchorSlot epochOk _ _ anchorHeld
    · exact pulledLe stateFound pulledOk
  · obtain ⟨state, stateFound, -⟩ := reachable.blockStatesFromParents found
    simp only [stateFound]
    refine ⟨_, rfl, ?_⟩
    exact UInt64.le_trans (UInt64.le_trans (holds stateFound).settled (getPreviousEpoch_le state))
      (forward.blockState_epoch_le_current slots anchorSlot epochOk _ _ stateFound)

/-- Before Gloas, the viability of a held leaf can be computed.

The current epoch must leave room for the voting source's two epochs of grace.

The checkpoint block of the leaf at the finalized epoch must read. -/
private theorem isViableLeaf_exists
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) {epoch : Epoch}
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (room : epoch.toNat + 2 < 2 ^ 64) {node : ForkChoiceNode}
    {block : BeaconBlock preset fork} (found : store.blocks[node.root]? = some block)
    (finalOk : ∃ checkpoint,
      store.getCheckpointBlock node.root store.finalizedCheckpoint.epoch = .ok checkpoint) :
    ∃ viable, store.isViableLeaf config node = .ok viable := by
  obtain ⟨source, sourceOk, sourceLe⟩ :=
    getVotingSource_le forward sound slots anchorSlot epochOk found
  obtain ⟨checkpoint, checkpointOk⟩ := finalOk
  have boundOk : addChecked source.epoch 2 = .ok (source.epoch + 2) := addChecked_of_lt (by
    have := UInt64.le_iff_toNat_le.mp sourceLe
    simp only [UInt64.reduceToNat]
    omega)
  unfold Store.isViableLeaf
  simp only [epochOk, sourceOk, checkpointOk, boundOk, bind, Except.bind, Except.mapError]
  split <;> exact ⟨_, rfl⟩

/-- The viable nodes of a forward-reachable store can be computed.

The store must hold its justified block.

The epoch of the latest 64-bit time plus the history of mixes must fit in 64 bits.

The history of mixes must span two epochs, the grace of a voting source. -/
private theorem getFilteredNodeTree_exists
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (seeds : (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (history : 2 ≤ preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (justifiedHeld : ∃ block, store.blocks[store.justifiedCheckpoint.root]? = some block) :
    ∃ nodes, store.getFilteredNodeTree config = .ok nodes := by
  have reachable := forward.reachable
  have lower := reachable.parentsBelow anchorSlot unknown
  obtain ⟨current, currentOk, -, -⟩ := forward.slots_le_current slots anchorSlot
  have epochOk : store.getCurrentStoreEpoch config = .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  -- The current epoch leaves room for two more epochs, by the fit of the seeds.
  have epochNat : (computeEpochAtSlot preset current).toNat =
      current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div]
  have currentLe := computeSlotAtTimeMs_le (mapError_ok_iff.mp currentOk)
  have epochLe : (computeEpochAtSlot preset current).toNat ≤
      (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) := by
    rw [epochNat, ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right currentLe
  have room : (computeEpochAtSlot preset current).toNat + 2 < 2 ^ 64 := by
    have := seeds
    omega
  -- The finalized epoch is between the anchor's epoch and the current one.
  have finalLe : store.finalizedCheckpoint.epoch ≤ computeEpochAtSlot preset current :=
    UInt64.le_trans (reachable.finalized_le_justified sound)
      (forward.justified_epoch_le_current sound slots anchorSlot epochOk).1
  have anchorLe : getCurrentEpoch anchorState ≤ store.finalizedCheckpoint.epoch := by
    rcases UInt64.le_total store.finalizedCheckpoint.epoch (getCurrentEpoch anchorState) with
      le | le
    · exact UInt64.le_of_eq (reachable.finalized_eq_anchor_of_epoch_le le).1.symm
    · exact le
  obtain ⟨boundary, boundaryOk⟩ : ∃ boundary,
      computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch = .ok boundary := by
    have fits : store.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
      have le := UInt64.le_iff_toNat_le.mp finalLe
      have := Nat.div_mul_le_self current.toNat preset.SLOTS_PER_EPOCH.toNat
      have := current.toNat_lt
      calc _ ≤ (computeEpochAtSlot preset current).toNat * preset.SLOTS_PER_EPOCH.toNat :=
            Nat.mul_le_mul_right _ le
        _ < 2 ^ 64 := by rw [epochNat]; omega
    unfold computeStartSlotAtEpoch
    exact ⟨_, mulChecked_of_lt fits⟩
  -- The anchor block, the lowest held block, sits at an epoch start at or below that boundary.
  have aboveAnchor : anchorBlock.slot ≤ boundary := by
    have floor := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot
    refine UInt64.le_trans (le_computeStartSlotAtEpoch_of_isStartSlotAtEpoch anchorBoundary
      anchorSlot floor) ?_
    rw [UInt64.le_iff_toNat_le, (computeStartSlotAtEpoch_ok_iff.mp floor).2,
      (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp anchorLe)
  obtain ⟨anchorRoot, -, anchorFound⟩ := reachable.anchor_known
  have orphansLe : ∀ (root : Root) (orphan : BeaconBlock preset fork),
      store.blocks[root]? = some orphan → store.blocks[orphan.parentRoot]? = none →
      orphan.slot ≤ boundary := fun _ _ found orphan =>
    UInt64.le_trans (reachable.orphans_le anchorSlot found orphan anchorFound)
      aboveAnchor
  -- Each held node computes its viable nodes, by descent on the rank.
  suffices held : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block →
      ∃ nodes, store.filterNodeTree config node = .ok nodes by
    obtain ⟨block, found⟩ := justifiedHeld
    exact held _ block found
  intro node
  induction hrank : store.nodeRank node using Nat.strong_induction_on generalizing node with
  | _ rank ih =>
  intro block found
  obtain ⟨children, childrenOk, heldChildren⟩ := Store.getNodeChildren_held lower found
  rw [Store.filterNodeTree, childrenOk]
  simp only [bind, Except.bind]
  split
  · obtain ⟨ancestor, walk⟩ := Store.getAncestor_ok_of_orphans_le lower orphansLe
      (node := ⟨node.root, .pending⟩) found
    obtain ⟨viable, viableOk⟩ := isViableLeaf_exists forward sound slots
      anchorSlot epochOk room found ⟨ancestor.root, by
        simp [Store.getCheckpointBlock, boundaryOk, walk, Except.mapError, bind, Except.bind,
          pure, Except.pure]⟩
    simp only [viableOk]
    exact ⟨_, rfl⟩
  · -- Each child is held, above its parent, so it ranks lower and recurses.
    have each : ∀ child ∈ children, ∃ below,
        (if _lower : store.nodeRank child < store.nodeRank node then
          store.filterNodeTree config child
        else throw (.parentSlotNotLower child.root)) = .ok below := by
      intro child member
      obtain ⟨childBlock, childFound, lowerRank⟩ := heldChildren child member
      simp only [lowerRank, ↓reduceDIte]
      exact ih _ (hrank ▸ lowerRank) child rfl childBlock childFound
    obtain ⟨viable, viableOk⟩ := flatMapM_exists_ok each
    simp only [viableOk]
    exact ⟨_, rfl⟩

end ViableNodes

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

/-- An up-to-date honest store holds the state of its justified checkpoint.

Otherwise bounded honest stores collide, or a store's finalized checkpoints give evidence.

The evidence is that of direct safety, relative to the anchor. -/
private theorem Execution.justifiedState_or_evidence {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    {last : ℕ} (admitted : BlocksAdmitted e 0 Δ last)
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
    HonestCollision (e := e) last ∨
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
  rcases e.blocksAgree_or_collision last with agree | collision
  swap
  · exact .inr (.inl collision)
  have noCollision := e.not_honestCollision_of_agree agree
  have forward := fun w (hw : w ∈ J) j => e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) j w hw
  have startLe : ∀ j, e.startTime ≤ (e.world j).time := fun j => by
    simpa [e.world_zero, World.initial] using e.monotone_time (Nat.zero_le j)
  left
  intro w hw k hk upToDate
  by_cases early :
      ((e.world k).state w).justifiedCheckpoint.epoch ≤ anchor.justifiedCheckpoint.epoch
  · exact e.justifiedState_of_anchor anchored start hw k early
  have later := UInt64.not_le.mp early
  -- An honest validator signed the justified checkpoint before the store's current slot.
  --
  -- It signed that vote at a duty.
  --
  -- That vote reaches the store by the start of the next slot, together with its head block.
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
  have genesisOf := e.genesisTimeMs_eq_of_honest start hv vote.genesis hw
  have deadlineCopy := deadline
  obtain ⟨slotTime, due, slotTimeOk, dueOk, -⟩ := deadlineCopy
  obtain ⟨nextOk, followingTime, followingTimeOk, followingLe⟩ :=
    Store.nextSlotStart_le_clock (genesisOf k) currentOk before
  rw [upToDate.1] at followingLe
  have dueLt := fits.due_lt_slot nextOk slotTimeOk followingTimeOk dueOk
  have beforeBoundary := fits.before_boundary nextOk slotTimeOk followingTimeOk deadline
  -- The duty vote carries the signed data, so its target is the justified checkpoint.
  obtain ⟨dataSlot, dataEpoch, head, headBlock, -, headKnown, dataRoot, notFuture⟩ :=
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
  have arrivalSlot : ((e.world arrival).state w).getCurrentSlot config = .ok (data.slot + 1) :=
    e.getCurrentSlot_of_slot_start slots (genesisOf arrival) followingTimeOk arrivalTime
      arrivalCurrent
  -- The voter's head reads the finalized checkpoint that the receiver holds at arrival.
  have targetRead := vote.data_target anchored anchorSlot anchorBoundary start hv
    (roots v hv n nBound)
  obtain ⟨targetBoundary, targetBlock, targetBoundaryOk, targetKnown, -, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock targetRead
  have chainRead := chain w hw arrival k arrivalLe hk
  rw [← targetEq] at chainRead
  obtain ⟨finalBoundary, finalBlock, finalBoundaryOk, finalKnown, finalLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock chainRead
  have aboveAnchor : anchorBlock.slot ≤ finalBoundary := UInt64.le_trans
    ((forward w hw k).reachable.anchorSlot_le (UInt64.le_of_eq anchorSlot) finalKnown) finalLe
  have voterRead := Store.getCheckpointBlock_of_same_blocks (forward v hv n).reachable
    (agree w hw v hv k n hk nBound) finalBoundaryOk aboveAnchor ⟨targetBlock, targetKnown⟩
    chainRead
  have finalLeTarget : ((e.world arrival).state w).finalizedCheckpoint.epoch ≤
      attestation.data.target.epoch := by
    rw [targetEq]
    exact UInt64.le_trans (e.checkpointsAdvance_of_le w arrivalLe).2.epoch_le
      ((forward w hw k).reachable.finalized_le_justified sound)
  have headCheckpoint : ((e.world n).state v).getCheckpointBlock attestation.data.beaconBlockRoot
      ((e.world arrival).state w).finalizedCheckpoint.epoch =
        .ok ((e.world arrival).state w).finalizedCheckpoint.root := by
    rw [Store.getCheckpointBlock_trans targetRead finalLeTarget]
    exact voterRead
  -- So the head reaches the receiver by arrival, with its checkpoint blocks.
  obtain ⟨_, finalized, _, finalizedKnown, _, _⟩ := Store.isAncestor_of_getCheckpointBlock
    (chain w hw arrival arrival (le_refl _) arrivalBound)
  rcases e.blocks_of_partiallySynchronous_of_anchorSlot sync (fun _ => UInt64.le_of_eq anchorSlot)
      admitted anchored hv hw (start v hv) (start w hw)
      (by simpa using late) arrivalBound arrivalCurrent ⟨finalized, finalizedKnown⟩
      (dataRoot ▸ headKnown) headCheckpoint with ⟨votedKnown, transport⟩ | collision
  swap
  · exact absurd collision noCollision
  have receiverRead := transport _ _ finalLeTarget targetRead
  -- From Gloas the vote's index names the payload of its head, which then reaches the receiver.
  have payload : ∀ gloas : .glamsterdam ≤ fork,
      ((e.world arrival).state w).validatePayloadVote gloas attestation headBlock = .ok () := by
    intro gloas
    rcases vote.validatePayloadVote_or_collision sync gloas (UInt64.le_of_eq anchorSlot) anchored
        hv hw (start v hv) (start w hw) (by rw [← nTime]; exact late) arrivalBound
        (fun _ _ mem accepted => arrivalCurrent.2 _ (.envelope mem accepted) ▸
          Store.onExecutionPayloadEnvelope_verified accepted) votedKnown with checked | collision
    · exact checked
    · exact absurd collision noCollision
  rcases vote.accepted_at_next_slot_of_payloadVote anchored start hv hw committees dataSlot
      nextOk arrivalSlot arrivalBound nBound votedKnown notFuture payload
      receiverRead with
    ⟨⟨after, accepted⟩, reads⟩ | collision
  swap
  · exact absurd collision noCollision
  -- The store then accepts the vote, which stores the target state.
  --
  -- An up-to-date store is a fixed point.
  --
  -- A checkpoint state, once stored, stays.
  --
  -- The receiver is a fixed point at arrival, so it already holds the target state, and keeps it.
  have seen := e.mem_view_of_send sync vote.sends hv hw (k := arrival) (by simpa using late)
  obtain ⟨state, stateOk⟩ := UpToDate.checkpointState_of_accepted arrivalCurrent seen accepted reads
  refine ⟨state, ?_⟩
  rw [← targetEq]
  have kept := e.checkpointStates_of_le w arrivalLe (Store.checkpointState_ok_iff.mp stateOk)
  exact Store.checkpointState_ok_iff.mpr kept

/-- An honest store that holds its justified state computes its viable nodes.

It is forward reachable from the anchor, which the head computation reads too.

The epoch of the latest 64-bit time plus the history of mixes must fit in 64 bits. -/
private theorem Execution.filteredTree_of_justifiedState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (sound : Invariant anchorState)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (seeds : (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (history : 2 ≤ preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {w : ValidatorIndex} (hw : w ∈ J) (k : ℕ)
    (unknown : ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {state : BeaconState preset fork}
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state) :
    Store.ForwardReachable config anchorState anchorBlock ((e.world k).state w) ∧
      ∃ nodes, ((e.world k).state w).getFilteredNodeTree config = .ok nodes := by
  have reached := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) k w hw
  have forward := reached.forwardReachable
  -- The justified block is held, as the store holds the justified state.
  obtain ⟨base, -, baseFound, -⟩ :=
    reached.checkpointStatesFromBlocks (Store.checkpointState_ok_iff.mp stateOk)
  exact ⟨forward, getFilteredNodeTree_exists forward sound slots anchorSlot anchorBoundary unknown
    seeds history (forward.reachable.known_of_blockState baseFound)⟩

/-- Every up-to-date honest store in the interval has a head. -/
def HonestHeadsExist (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ∃ hd, ((e.world k).state w).getHead config = .ok hd

/-- Before Gloas, every up-to-date honest store up to `last` has a head.

Otherwise two honest stores collide by `last`, or direct-safety evidence holds.

The evidence is relative to the anchor.

The claim holds from every start time. -/
theorem Execution.honestHeadsExist_or_evidence {Δ : ℕ} (sync : e.Synchronous Δ)
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
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) last)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    -- The epoch of the latest 64-bit time plus the history of mixes must fit in 64 bits.
    (seeds : (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64) (first : ℕ) :
    HonestHeadsExist (e := e) first last ∨
    HonestCollision (e := e) last ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  -- The head computation needs the state of the justified checkpoint once it weighs a child.
  --
  -- The store moves its justified checkpoint without storing that state.
  --
  -- So the state needs a reason.
  --
  -- The store holds the state of its justified checkpoint, through an honest vote for it.
  rcases e.justifiedState_or_evidence sync slots admitted fits prompt votes anchored start
      anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre heldEarly
      enough terminal with states | alternative
  · left
    have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
    have history : 2 ≤ preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := by
      have := parameters.lookahead
      omega
    intro w hw k _ inTime upToDate
    obtain ⟨state, stateOk⟩ := states w hw k inTime upToDate
    obtain ⟨forward, nodes, tree⟩ := e.filteredTree_of_justifiedState anchored start sound slots
      (UInt64.le_of_eq anchorSlot) anchorBoundary seeds history hw k (absent w hw k inTime)
      stateOk
    -- So the store holds the state.
    --
    -- The head follows from the stake ceiling and the boost's fit.
    --
    -- The stake ceiling and the fit of the proposer boost keep every weight below `2^64`.
    exact Store.getHead_exists preGloas forward (UInt64.le_of_eq anchorSlot) (absent w hw k inTime)
      parameters.slots scoreFits tree stateOk (ceiling w hw k _ state inTime stateOk)
  · exact .inr alternative

/-! ## From Gloas: active equivocators are registered or evidence holds -/

/-- A held block reads the store's finalized checkpoint when it comes from the block's state.

It may come from the state itself or from its pull-up, or be at the anchor's epoch. -/
private theorem finalized_read_of_held {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : Serialization.Ssz.SszType.hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0))
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state)
    (own : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch →
      store.finalizedCheckpoint = state.finalizedCheckpoint ∨
        ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
          store.finalizedCheckpoint = pulled.finalizedCheckpoint) :
    store.getCheckpointBlock root store.finalizedCheckpoint.epoch =
      .ok store.finalizedCheckpoint.root := by
  by_cases later : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch
  · have member : store.finalizedCheckpoint ∈ [state.currentJustifiedCheckpoint,
          state.previousJustifiedCheckpoint, state.finalizedCheckpoint] ∨
        ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
          store.finalizedCheckpoint ∈ [pulled.currentJustifiedCheckpoint,
            pulled.previousJustifiedCheckpoint, pulled.finalizedCheckpoint] := by
      rcases own later with same | ⟨pulled, ok, same⟩
      · exact .inl (by simp [same])
      · exact .inr ⟨pulled, ok, by simp [same]⟩
    rcases reachable.getCheckpointBlock_of_blockState sound (UInt64.le_of_eq anchorSlot) positive
      window held member later with ⟨read, -⟩ | zero
    · exact read
    · exact absurd zero nonzero
  · obtain ⟨epochEq, hashed⟩ := reachable.finalized_eq_anchor_of_epoch_le (UInt64.not_lt.mp later)
    obtain ⟨block, found⟩ := reachable.known_of_blockState held
    rw [epochEq]
    exact reachable.getCheckpointBlock_anchor anchorSlot boundary unknown found hashed

/-- Each held block reads, on its own chain, a finalized checkpoint its store held earlier.

That checkpoint is at the finalized epoch of the block's state or later.

The store starts at the anchor store and stays reachable from the anchor along its run. -/
private theorem Execution.heldFinalized_read {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : Serialization.Ssz.SszType.hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0))
    {w : ValidatorIndex} (start : e.start w = anchor)
    (reachable : ∀ i, Store.Reachable config anchorState anchorBlock ((e.world i).state w)) (n : ℕ)
    (unknown : ∀ k ≤ n, ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {root : Root} {state : BeaconState preset fork}
    (held : ((e.world n).state w).blockStates[root]? = some state) :
    ∃ i ≤ n, ((e.world i).state w).getCheckpointBlock root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root ∧
      state.finalizedCheckpoint.epoch ≤ ((e.world i).state w).finalizedCheckpoint.epoch := by
  induction n generalizing root state with
  | zero =>
    refine ⟨0, Nat.le_refl _, ?_, ((reachable 0).ordered_finalized sound).2 held⟩
    -- The anchor store's finalized checkpoint is at the anchor's epoch.
    refine finalized_read_of_held (reachable 0) sound anchorSlot boundary (unknown 0 le_rfl)
      positive window nonzero held fun later => absurd later ?_
    obtain ⟨anchorRoot, -, -, -, -, finalized, -⟩ := getForkchoiceStore_anchor anchored
    rw [e.world_zero]
    change ¬ getCurrentEpoch anchorState < (e.start w).finalizedCheckpoint.epoch
    rw [start, finalized]
    exact UInt64.lt_irrefl _
  | succ n ih =>
    by_cases old : ((e.world n).state w).blockStates[root]? = some state
    · obtain ⟨i, le, rest⟩ := ih (fun k le => unknown k (Nat.le_succ_of_le le)) old
      exact ⟨i, Nat.le_succ_of_le le, rest⟩
    refine ⟨n + 1, Nat.le_refl _, ?_, ((reachable (n + 1)).ordered_finalized sound).2 held⟩
    have reached := reachable (n + 1)
    have keep {s t : Store preset fork} (states : t.blockStates = s.blockStates)
        (before : s = (e.world n).state w) (after : t = (e.world (n + 1)).state w) : False := by
      subst s t
      exact old (states ▸ held)
    rcases e.state_succ n w with same | ⟨_, moved⟩
    · exact absurd (same ▸ held) old
    cases moved with
    | tick _ _ a => exact (keep (Store.onTick_frame a).2.2.2 rfl rfl).elim
    | blockAttestation _ _ _ _ a => exact (keep (Store.onAttestation_frame a).2.2.1 rfl rfl).elim
    | blockAttesterSlashing _ _ _ _ a =>
      exact (keep (Store.onAttesterSlashing_frame a).2.2.1 rfl rfl).elim
    | attestation _ a => exact (keep (Store.onAttestation_frame a).2.2.1 rfl rfl).elim
    | attesterSlashing _ a => exact (keep (Store.onAttesterSlashing_frame a).2.2.1 rfl rfl).elim
    | payloadAttestation _ a =>
      exact (keep (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.2 rfl rfl).elim
    | envelope _ a => exact (keep (Store.onExecutionPayloadEnvelope_frame a).2.2 rfl rfl).elim
    | inclusionList _ a => exact (keep (Store.onInclusionList_frame a).2.2 rfl rfl).elim
    | @block signed _ added =>
      have original := added
      rcases Store.onBlock_pulledUp added with same | ⟨blockRoot, inserted, pulled, base, now,
          hashed, fresh, blocks, states, run, -, -, baseFinalized, -, moved⟩
      · exact absurd (same ▸ held) old
      have heldAt := held
      rw [states, Std.TreeMap.getElem?_insert] at heldAt
      split at heldAt
      · rename_i same
        cases heldAt
        obtain rfl : blockRoot = root := Std.LawfulEqCmp.eq_of_compare same
        -- The new finalized checkpoint is the old one, the state's, or its pull-up's.
        have adopted : ((e.world (n + 1)).state w).finalizedCheckpoint = base.finalizedCheckpoint ∨
            ((e.world (n + 1)).state w).finalizedCheckpoint = pulled.finalizedCheckpoint := by
          rcases moved with ⟨-, eq⟩ | ⟨-, eq⟩ <;> rw [eq]
          · exact (Store.updateCheckpoints_finalizedCheckpoint _ _ _).imp_left
              (·.trans (by simp))
          · exact .inl (by simp)
        have own := finalized_read_of_held reached sound anchorSlot boundary
          (unknown (n + 1) le_rfl) positive window nonzero held
        rcases adopted with eq | eq
        · rcases baseFinalized with kept | eq'
          · rw [eq, kept]
            obtain ⟨-, ⟨finalizedSlot, startOk, lt⟩, parentRead⟩ :=
              Store.onBlock_checks hashed fresh original
            rcases Store.onBlock_same_or_insert original with same | ⟨-, -, -, -, pre, -, preFound,
                -, -⟩
            · exact absurd (same ▸ held) old
            obtain ⟨parent, parentKnown⟩ := (reachable n).known_of_blockState preFound
            have grows := fun {r : Root} {b : BeaconBlock preset fork}
                (f : ((e.world n).state w).blocks[r]? = some b) =>
              Store.onBlock_blocks_of_found added f
            have found : ((e.world (n + 1)).state w).blocks[blockRoot]? = some signed.message := by
              rw [blocks]
              simp
            have parentFound := grows parentKnown
            have parentLower := reached.parentsBelow (UInt64.le_of_eq anchorSlot)
              (unknown (n + 1) le_rfl) _ _ _ found parentFound
            have unfoldRead : ∀ r, ((e.world (n + 1)).state w).getCheckpointBlock r
                ((e.world n).state w).finalizedCheckpoint.epoch =
                  (·.root) <$> ((e.world (n + 1)).state w).getAncestor ⟨r, .pending⟩
                    finalizedSlot := by
              intro r
              simp only [Store.getCheckpointBlock, startOk, Except.mapError, bind, Except.bind]
              rfl
            rw [unfoldRead, Store.getAncestor_step found (UInt64.not_le.mpr lt) parentFound
              parentLower, Store.getAncestor_root _ .pending, ← unfoldRead]
            exact Store.getCheckpointBlock_of_blocks grows parentRead
          · exact own fun _ => .inl (eq.trans eq')
        · exact own fun _ => .inr ⟨pulled, run, eq⟩
      · exact absurd heldAt old

/-- Each honest store's justified state registers the active equivocators of its held blocks. -/
private def HonestActiveEquivocatorsRegistered (last : ℕ) : Prop :=
  ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ last →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ActiveEquivocatorsRegistered ((e.world k).state w) state

/-- Honest justified states register the equivocators active in held blocks, or evidence holds.

The evidence is relative to the anchor. -/
private theorem Execution.activeEquivocatorsRegistered_or_evidence {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS)
    {horizon : Epoch} {last : ℕ} (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last) :
    HonestActiveEquivocatorsRegistered (e := e) last ∨
      HistoricalDirectSafetyEvidence (e := e) pre last := by
  -- With no honest event in time, every store claim is vacuous.
  by_cases some : ∃ u ∈ J, ∃ n, (e.world n).time ≤ last
  swap
  · push Not at some
    exact .inl fun w honest k _ inTime => absurd inTime (Nat.not_le.mpr (some w honest k))
  obtain ⟨u, uHonest, n₀, n₀Time⟩ := some
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  -- Each justified checkpoint reads every earlier finalized checkpoint of its store.
  rcases e.finalizedFamily_or_historical_evidence anchored start sound anchorSlot anchorBoundary
      slots bounded roots absent parameters genesis pre heldEarly enough terminal uHonest
      n₀Time with chain | evidence
  swap
  · exact .inr evidence
  left
  intro w hw k state time stateOk root block held blockFound heldFound index _ validator
    registered active
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := parameters.slots
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have forward := e.forwardReachableWith
    (fun v hv => (start v hv) ▸ Store.ForwardReachableWith.anchor anchored) k w hw
  have nonzero : Serialization.Ssz.SszType.hashTreeRoot anchorState ≠
      .ok (Vector.replicate 32 0) := by
    rw [forward.reachable.anchorState_root]
    exact fun same => e.anchor_stateRoot_nonzero anchored start roots uHonest n₀Time
      (Except.ok.inj same)
  -- The held block reads a finalized checkpoint of an earlier store, at or past its finality.
  obtain ⟨j, jLe, read, finalLe⟩ := e.heldFinalized_read anchored sound anchorSlot
    anchorBoundary positive window nonzero (start w hw)
    (fun i => e.reachable (fun v hv => (start v hv) ▸ Store.Reachable.anchor anchored) i w hw) k
    (fun j le => absent w hw j ((e.monotone_time le).trans time)) heldFound
  have sourceWalk := Store.getCheckpointBlock_of_blocks
    (fun found => e.blocks_of_le jLe found) read
  -- The justified checkpoint reads the same checkpoint.
  have walk := chain w hw j k jLe time
  obtain ⟨base, target, baseFound, targetOk, advanced⟩ := e.checkpointStates_fixedChecks anchored
    start hw (Store.checkpointState_ok_iff.mp stateOk)
  obtain ⟨justifiedBlock, justifiedFound⟩ := forward.reachable.known_of_blockState baseFound
  obtain ⟨startSlot, -, startOk, -, -, -⟩ := Store.isAncestor_of_getCheckpointBlock read
  have epochLe : ((e.world j).state w).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch :=
    UInt64.le_trans (e.checkpointsAdvance_of_le w jLe).2.epoch_le
      (forward.reachable.finalized_le_justified sound)
  have bound : startSlot ≤ max justifiedBlock.slot target := by
    have one := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
    have two := (computeStartSlotAtEpoch_ok_iff.mp targetOk).2
    have le := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (UInt64.le_iff_toNat_le.mp epochLe)
    rw [UInt64.le_iff_toNat_le, toNat_max]
    omega
  exact forward.registered_of_shared_checkpoint (UInt64.le_of_eq anchorSlot) sound
    (UInt64.lt_iff_toNat_lt.mpr positive) walk justifiedFound startOk bound baseFound advanced
    sourceWalk blockFound heldFound finalLe registered active

/-! ## From Gloas: up-to-date honest stores have a head -/

/-- Honest justified states up to time `last` bound each weight of the weak-head test by `cap`.

Each set of their validators that are active or known to the store to equivocate weighs at most it.

It is an assumption on the run, and a cap at least the supply of ether satisfies it.
-/
def CheckpointHeadWeightCeiling (cap last : ℕ) : Prop :=
  ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ last →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ((e.world k).state w).HeadWeightAtMost cap state

/-- From Gloas, an up-to-date honest store up to `last` has a head.

Otherwise two honest stores collide by `last`, or direct-safety evidence holds.

The evidence is relative to the anchor.

The claim holds from every start time. -/
theorem Execution.honestHeadsExist_or_evidence_of_gloas {Δ : ℕ} (sync : e.Synchronous Δ)
    (gloas : .glamsterdam ≤ fork) {last : ℕ} (admitted : BlocksAdmitted e 0 Δ last)
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
    -- The proposer boost and the head reads must fit the cap of `2 * 10^17` Gwei.
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    -- The committee windows must fit.
    (fit : config.CommitteeWindowsFit preset)
    (weights : config.HeadWeightsFit preset (2 * 10 ^ 17))
    -- The anchor's registry must leave room up to the horizon.
    (room : AnchorRegistryRoom preset anchorState horizon)
    -- Every honest justified state must bound each weight of the weak-head test.
    --
    -- The bound is `2 * 10^17` Gwei.
    --
    -- Those weights are stakes of sets of its validators that are active or known to equivocate.
    (heads : CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) last) (first : ℕ) :
    HonestHeadsExist (e := e) first last ∨
    HonestCollision (e := e) last ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  have slots : 0 < config.SLOT_DURATION_MS := UInt64.lt_trans (by decide) weights.slots
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  -- The store holds the state of its justified checkpoint, through an honest vote for it.
  rcases e.justifiedState_or_evidence sync slots admitted fits prompt votes anchored start
      anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre heldEarly
      enough terminal with states | alternative
  swap
  · exact .inr alternative
  -- The justified state registers the equivocators that the head reads count.
  rcases e.activeEquivocatorsRegistered_or_evidence anchored start anchorSlot anchorBoundary slots
      bounded roots absent parameters genesis pre heldEarly enough terminal with
    registered | evidence
  swap
  · exact .inr (.inr evidence)
  have registries := e.honestRegistries_of_room slots gloas anchored start
    (UInt64.le_of_eq anchorSlot) sound bounded room
  left
  have history : 2 ≤ preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := by
    have := parameters.lookahead
    omega
  intro w hw k _ inTime upToDate
  obtain ⟨state, stateOk⟩ := states w hw k inTime upToDate
  obtain ⟨held, within⟩ := registries w hw k inTime
  obtain ⟨forward, nodes, tree⟩ := e.filteredTree_of_justifiedState anchored start sound slots
    (UInt64.le_of_eq anchorSlot) anchorBoundary fit.seeds history hw k (absent w hw k inTime)
    stateOk
  exact Store.getHead_exists_of_gloas gloas forward (UInt64.le_of_eq anchorSlot)
    (absent w hw k inTime) fit scoreFits weights tree stateOk (within state stateOk) held
    (heads w hw k state inTime stateOk) (registered w hw k state inTime stateOk)

/-- An up-to-date honest store up to `last` has a head, at every fork.

Otherwise two honest stores collide by `last`, or direct-safety evidence holds.

The evidence is relative to the anchor.

The claim holds from every start time. -/
theorem Execution.honestHeadsExist_or_evidence_of_gated {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) {last : ℕ} (admitted : BlocksAdmitted e 0 Δ last)
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
    -- Before Gloas the claim rests on the active-stake ceiling and the seed bound.
    --
    -- The claim takes those two at every fork.
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) last)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (seeds : (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    -- From Gloas the claim rests on the anchor's registry room.
    (room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon)
    -- From Gloas the claim also needs the head-weight and committee-window bundles.
    (weights : .glamsterdam ≤ fork → config.HeadWeightsFit preset (2 * 10 ^ 17))
    -- From Gloas the claim also rests on a bound on each weight of the weak-head test.
    (supply : .glamsterdam ≤ fork → CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) last)
    (fit : .glamsterdam ≤ fork → config.CommitteeWindowsFit preset) (first : ℕ) :
    HonestHeadsExist (e := e) first last ∨
    HonestCollision (e := e) last ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  by_cases gloas : .glamsterdam ≤ fork
  · exact e.honestHeadsExist_or_evidence_of_gloas sync gloas admitted fits prompt votes anchored
      start anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre heldEarly
      enough terminal scoreFits (fit gloas) (weights gloas) (room gloas) (supply gloas) first
  · exact e.honestHeadsExist_or_evidence sync slots (Nat.lt_of_not_le gloas) admitted fits prompt
      votes anchored start anchorSlot anchorBoundary signed roots absent bounded parameters genesis
      pre heldEarly enough terminal ceiling scoreFits seeds first

/-- The caller of a checked call reads its head at each rollover up to `last`.

Otherwise two honest stores collide by `last`, or direct-safety evidence holds.

The evidence is relative to the anchor. -/
theorem Execution.callRolloverRead_or_evidence {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) {last : ℕ} (admitted : BlocksAdmitted e 0 Δ last)
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
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (seeds : (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    {u : ValidatorIndex} (caller : u ∈ J) (n : ℕ) (head : Root)
    -- From Gloas the claim needs the anchor's registry room.
    (room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon)
    -- From Gloas the claim also needs the head-weight and committee-window bundles.
    (weights : .glamsterdam ≤ fork → config.HeadWeightsFit preset (2 * 10 ^ 17))
    -- From Gloas the claim also needs the bound on each weight of the weak-head test.
    (supply : .glamsterdam ≤ fork → CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) last)
    (fit : .glamsterdam ≤ fork → config.CommitteeWindowsFit preset) :
    -- The steps of a checked call that read the caller's head take this read.
    --
    -- With it, an accepted current-target test has its honest signers up to these alternatives.
    --
    -- A confirmed root stays in the filtered tree up to these alternatives and the step's evidence.
    --
    -- That evidence is held-state finality evidence or cross-store justified evidence.
    CallRolloverRead (e := e) u n head last ∨
    HonestCollision (e := e) last ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  rcases e.honestHeadsExist_or_evidence_of_gated sync slots admitted fits prompt votes anchored
      start anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre heldEarly
      enough terminal ceiling scoreFits seeds room weights supply fit 0 with heads | alternative
  swap
  · exact .inr alternative
  -- At each rollover the caller is up to date, so it has a head.
  left
  intro _ _ _ begin _ _ _ _ beginLe k atTime upToDate
  exact heads u caller k (Nat.zero_le _) (atTime ▸ beginLe) upToDate

/-- At a time T, the confirmed root of a call is in the filtered tree of an honest store.

The store is up to date, and the root strictly descends from its justified block.

Otherwise two honest stores collide, or direct-safety or accountable-safety evidence holds.

The caller's head read at each rollover is derived, not assumed. -/
theorem Execution.rootInFilteredTree_of_checked_or_evidence [DecidablePred (· ∈ J)]
    {anchor : Store preset fork} {Δ time T : ℕ} {anchorEpoch horizon : Epoch} {margin : ℕ}
    {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (admitted : BlocksAdmitted e 0 Δ time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (votes : ValidatedDutyVotes (e := e) time)
    (windows : AssignmentWindowAgreement (e := e) time)
    (fit : config.CommitteeWindowsFit preset)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (inHorizon : HonestStoreEpochsBounded (e := e) horizon time)
    -- From Gloas, the anchor's registry must leave room for pending deposits.
    --
    -- The room covers the deposits of each epoch from the anchor's to the horizon.
    (room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon)
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
    -- The caller's head read rests on the active-stake ceiling and the proposer-score bound.
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    -- From Gloas it also rests on the head-weight bundle and on each weak-head weight.
    (weights : .glamsterdam ≤ fork → config.HeadWeightsFit preset (2 * 10 ^ 17))
    (supply : .glamsterdam ≤ fork → CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    {chain later : List Root} (headOk : ((e.world n).state u).getHead config = .ok head)
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
      HistoricalDirectSafetyEvidence (e := e) pre time ∨
        HeldStateFinalityEvidence (e := e) pre time ∨
          CrossStoreJustifiedEvidence (e := e) pre time := by
  have sound := (DirectSafety.run_justified_separated pre genesis).1
  rcases e.callRolloverRead_or_evidence sync slots admitted fits prompt votes anchorStore anchored
      anchorSlot anchorBoundary (anchorOk ▸ signed) roots anchorParent inHorizon params genesis pre
      upgrade enough floor ceiling scoreFits fit.seeds caller n head.root room weights supply
      (fun _ => fit) with rollover | collision | historical
  · rcases e.rootInFilteredTree_of_checked pre sync slots admitted fits prompt votes windows fit
        ring anchorStore sound anchorSlot anchorBoundary anchored anchorOk inHorizon room roots
        anchorParent pinned signed drift unslashed floor anchorGenesis params genesis upgrade
        enough included caller upToDate atSlot headOk rollover inputs walk realized realizedHead
        low high startCovers covers receiver atTime ready tree descends strict with
      member | collision | held | cross
    · exact .inl member
    · exact .inr (.inl collision)
    · exact .inr (.inr (.inr (.inl held)))
    · exact .inr (.inr (.inr (.inr cross)))
  · exact .inr (.inl collision)
  · exact .inr (.inr (.inl historical))

/-- An accepted current-target test has active honest signers with two thirds of the active balance.

Each votes for the target before the next epoch.

Otherwise two honest stores collide, or direct-safety evidence holds.

The caller's head read at each rollover and, from Gloas, the registry bound are derived. -/
theorem Execution.honestTargetVotes_signed_of_checked_or_evidence {anchor : Store preset fork}
    {Δ time : ℕ} {margin : ℕ} (slots : 0 < config.SLOT_DURATION_MS)
    (fits : DelayFits fork config genesisTimeMs Δ)
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
    (beginLe : begin.toNat ≤ time)
    (covers : HonestHeadsCover (e := e) origin (e.world n).time (begin.toNat + 1))
    -- The caller's head read at each rollover rests on these, up to the two alternatives.
    (sync : e.Synchronous Δ) (admitted : BlocksAdmitted e 0 Δ time)
    (signed : JustifiedHonestlySigned (e := e) anchor.justifiedCheckpoint.epoch 0 time)
    (absent : AnchorParentAbsent (e := e) time) {horizon : Epoch}
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    -- From Gloas the anchor's registry room also bounds the registries of held block states.
    (room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon)
    (weights : .glamsterdam ≤ fork → config.HeadWeightsFit preset (2 * 10 ^ 17))
    (supply : .glamsterdam ≤ fork → CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) time) :
    (∃ (state : BeaconState preset fork) (total : Gwei) (voters : Finset ValidatorIndex),
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state ∧
      getTotalActiveBalance state = .ok total ∧
      2 * total.toNat + margin ≤ 3 * stake (fun v => balanceAt state v.toNat) voters ∧
      ∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧ SignsTarget e v target (begin.toNat - 1)) ∨
      HonestCollision (e := e) time ∨ HistoricalDirectSafetyEvidence (e := e) pre time := by
  have sound := (DirectSafety.run_justified_separated pre genesis).1
  have retained := parameters.lookahead
  have registries : .glamsterdam ≤ fork → ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      HeldRegistriesWithinLimit ((e.world k).state w) := fun h w hw k hk =>
    (e.honestRegistries_of_room slots h anchored start (UInt64.le_of_eq anchorSlot) sound
      bounded (room h) w hw k hk).1
  rcases e.callRolloverRead_or_evidence sync slots admitted fits prompt votes anchored start
      anchorSlot anchorAtBoundary signed nonzero absent bounded parameters genesis pre heldEarly
      enough terminal ceiling scoreFits fit.seeds caller n head.root room weights supply
      (fun _ => fit) with read | collision | historical
  · exact (e.honestTargetVotes_signed_of_checked slots retained registries fits prompt votes
      windows fit nonzero anchored anchorSlot anchorAtBoundary start caller upToDate atSlotStart
      headOk justified count targetOk originEpochOk descends nextOk firstOk beginOk beginLe covers
      (read target nextEpoch first begin targetOk nextOk firstOk beginOk beginLe)).imp_right .inl
  · exact .inr (.inl collision)
  · exact .inr (.inr historical)

end EthLib.Consensus.Models.Network
