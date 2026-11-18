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

/-- Before Gloas, the viable nodes of a forward-reachable store can be computed.

The store must hold its justified block, and the parameters of the committee windows must fit.

The history of mixes must span two epochs, the grace of a voting source. -/
private theorem getFilteredNodeTree_exists (preGloas : fork < .glamsterdam)
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (fit : config.CommitteeWindowsFit preset)
    (history : 2 ≤ preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (justifiedHeld : ∃ block, store.blocks[store.justifiedCheckpoint.root]? = some block) :
    ∃ nodes, store.getFilteredNodeTree config = .ok nodes := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have reachable := forward.reachable
  have lower := reachable.parentsBelow (UInt64.le_of_eq anchorSlot) unknown
  obtain ⟨current, currentOk, -, -⟩ := forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
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
    have := fit.seeds
    omega
  -- The finalized epoch is between the anchor's epoch and the current one.
  have finalLe : store.finalizedCheckpoint.epoch ≤ computeEpochAtSlot preset current :=
    UInt64.le_trans (reachable.finalized_le_justified sound)
      (forward.justified_epoch_le_current sound slots (UInt64.le_of_eq anchorSlot) epochOk).1
  have anchorLe : getCurrentEpoch anchorState ≤ store.finalizedCheckpoint.epoch := by
    rcases UInt64.le_total store.finalizedCheckpoint.epoch (getCurrentEpoch anchorState) with
      le | le
    · exact UInt64.le_of_eq (reachable.finalized_eq_anchor_of_epoch_le le).1.symm
    · exact le
  have positive := fit.positive
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
      (UInt64.le_of_eq anchorSlot) floor) ?_
    rw [UInt64.le_iff_toNat_le, (computeStartSlotAtEpoch_ok_iff.mp floor).2,
      (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp anchorLe)
  obtain ⟨anchorRoot, -, anchorFound⟩ := reachable.anchor_known
  have orphansLe : ∀ (root : Root) (orphan : BeaconBlock preset fork),
      store.blocks[root]? = some orphan → store.blocks[orphan.parentRoot]? = none →
      orphan.slot ≤ boundary := fun _ _ found orphan =>
    UInt64.le_trans (reachable.orphans_le (UInt64.le_of_eq anchorSlot) found orphan anchorFound)
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
  obtain ⟨children, childrenOk⟩ : ∃ children, store.getNodeChildren node = .ok children := by
    simp [Store.getNodeChildren, notGloas, pure, Except.pure]
  rw [Store.filterNodeTree, childrenOk]
  simp only [bind, Except.bind]
  split
  · obtain ⟨ancestor, walk⟩ := Store.getAncestor_ok_of_orphans_le lower orphansLe
      (node := ⟨node.root, .pending⟩) found
    obtain ⟨viable, viableOk⟩ := isViableLeaf_exists forward sound slots
      (UInt64.le_of_eq anchorSlot) epochOk room found ⟨ancestor.root, by
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
      obtain ⟨childPending, childBlock, childFound, parentRoot⟩ :=
        (Store.mem_getNodeChildren preGloas childrenOk).mp member
      have below : block.slot < childBlock.slot := lower _ childBlock block childFound
        (parentRoot ▸ found)
      have lowerRank : store.nodeRank child < store.nodeRank node := by
        simp only [Store.nodeRank, childFound, found, childPending, ↓reduceIte]
        have := UInt64.lt_iff_toNat_lt.mp below
        have := childBlock.slot.toNat_lt
        split <;> omega
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
    nextSlotStart_le_clock (genesisOf k) currentOk before
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
  have arrivalSlot : ((e.world arrival).state w).getCurrentSlot config = .ok (data.slot + 1) :=
    e.getCurrentSlot_of_slot_start slots (genesisOf arrival) followingTimeOk arrivalTime
      arrivalCurrent
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

/-- Before Gloas, an up-to-date honest store up to `last` with a readable filtered tree has a head.

Otherwise two honest stores collide by `last`, or direct-safety evidence holds.

The evidence is relative to the anchor.

The claim holds from every start time. -/
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
    HonestCollision (e := e) last ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  -- The store holds the state of its justified checkpoint, through an honest vote for it.
  rcases e.justifiedState_or_evidence sync slots preGloas admitted fits prompt votes anchored start
      anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre heldEarly
      enough terminal with states | alternative
  · left
    intro w hw k nodes _ inTime upToDate tree
    obtain ⟨state, stateOk⟩ := states w hw k inTime upToDate
    -- The stake ceiling and the fit of the proposer boost keep every weight below `2^64`.
    exact Store.getHead_exists preGloas
      (e.forwardReachable (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) k w
        hw) (UInt64.le_of_eq anchorSlot) (absent w hw k inTime) positive scoreFits tree stateOk
      (ceiling w hw k _ state inTime stateOk)
  · exact .inr alternative

/-- Before Gloas, the caller of a checked call reads its head at each rollover up to `last`.

Otherwise two honest stores collide by `last`, or direct-safety evidence holds.

The evidence is relative to the anchor. -/
theorem Execution.callRolloverRead_or_evidence {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (history : 2 ≤ preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
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
    (fit : config.CommitteeWindowsFit preset)
    {u : ValidatorIndex} (caller : u ∈ J) (n : ℕ) (head : Root) :
    CallRolloverRead (e := e) u n head last ∨
    HonestCollision (e := e) last ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  rcases e.justifiedState_or_evidence sync slots preGloas admitted fits prompt votes anchored start
      anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre heldEarly
      enough terminal with states | alternative
  swap
  · exact .inr alternative
  rcases e.honestHeadsExist_or_evidence sync slots fit.positive preGloas admitted fits prompt votes
      anchored start anchorSlot anchorBoundary signed roots absent bounded parameters genesis pre
      heldEarly enough terminal ceiling scoreFits 0 with heads | alternative
  swap
  · exact .inr alternative
  -- At each rollover the caller is up to date, so it holds its justified state and has a head.
  left
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  intro _ _ _ begin _ _ _ _ beginLe k atTime upToDate
  have inTime : (e.world k).time ≤ last := atTime ▸ beginLe
  have forward := e.forwardReachable
    (fun w hw => (start w hw) ▸ Store.ForwardReachable.anchor anchored) k u caller
  have reached := e.forwardReachableWith
    (fun w hw => (start w hw) ▸ Store.ForwardReachableWith.anchor anchored) k u caller
  -- The justified block is held, as the store holds the justified state.
  obtain ⟨state, stateOk⟩ := states u caller k inTime upToDate
  obtain ⟨base, -, baseFound, -⟩ :=
    reached.checkpointStatesFromBlocks (Store.checkpointState_ok_iff.mp stateOk)
  obtain ⟨nodes, tree⟩ := getFilteredNodeTree_exists preGloas forward sound slots anchorSlot
    anchorBoundary (absent u caller k inTime) fit history
    (forward.reachable.known_of_blockState baseFound)
  exact heads u caller k nodes (Nat.zero_le _) inTime upToDate tree

end EthLib.Consensus.Models.Network
