module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# The confirmed root is held from the call on

An honest vote before the call's slot, for a block above the root, shows that its signer held it.

Synchrony then delivers the root to every up-to-date honest store from the call on.
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

/-- An honest vote before the call's slot, for a block above the root, keeps the root held.

Every up-to-date honest store holds the root from the call up to `time`.

Otherwise two honest stores collide, or a held state's justification conflicts with a finality. -/
theorem Execution.rootHeld_of_honest_vote {Δ : ℕ} {anchor : Store preset fork} {time : ℕ}
    {horizon : Epoch} {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
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
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := params.slots
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := params.roots
    omega
  -- Every held state reads every honest finality at or below its justification.
  rcases Execution.heldFinality_or_evidence pre anchorStore anchored sound anchorSlot
      anchorBoundary slots inHorizon roots anchorParent params genesis upgrade enough floor with
    reads | evidence
  swap
  · exact .inr (.inr evidence)
  -- Honest stores up to the time agree on every shared root, or two of them collide.
  rcases e.blocksAgree_or_collision time with agree | collide
  swap
  · exact .inr (.inl collide)
  left
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
  have same := agree u caller v honest n k within (kTime.trans within)
  -- So the signer held the root then.
  have signerDescends := Store.isAncestor_of_same_blocks (reached v honest k) preGloas same known
    ((reached u caller n).anchorSlot_le anchorLe known) ⟨headBlock, dataRoot ▸ headHeld⟩ descends
  obtain ⟨signerBlock, signerKnown⟩ := Store.held_of_isAncestor signerDescends
  -- The deadline of the vote, plus the delay, is before the call.
  have late : (e.world k).time + Δ ≤ (e.world n).time := by
    rw [atBegin]
    exact fits.deadline_add_le deadline (computeSlotAtTimeMs_computeTimeAtSlotMs slots beginOk)
      early
  -- Every honest store runs on the model's genesis, as the signer's does.
  have genesisOf (w : ValidatorIndex) (hw : w ∈ J) :=
    e.genesisTimeMs_eq_of_honest anchored honest signerGenesis hw
  -- A receiver up to date at the start of the call's slot holds the root.
  have receipt (w : ValidatorIndex) (receiver : w ∈ J) (r : ℕ)
      (atCall : (e.world r).time = begin.toNat)
      (current : UpToDate config checks sources (e.world r).time ((e.world r).view w)
        ((e.world r).state w)) :
      ∃ b : BeaconBlock preset fork, ((e.world r).state w).blocks[root]? = some b := by
    have rBound : (e.world r).time ≤ time := atCall ▸ atBegin ▸ within
    have reachedW := reached w receiver r
    have slotOk : ((e.world r).state w).getCurrentSlot config = .ok slot :=
      e.getCurrentSlot_of_slot_start slots (genesisOf w receiver r) beginOk atCall current
    have epochOk : ((e.world r).state w).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset slot) := by
      simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
    -- The receiver's finality is held, as the anchor state's root is not zero.
    obtain ⟨anchorKey, -, anchorFound⟩ := reachedW.anchor_known
    have nonzero := roots w receiver r rBound anchorKey anchorBlock anchorFound
    have finalizedKnown := reachedW.finalized_known sound anchorLe positive window nonzero
    -- The caller reads the receiver's finality on the root's chain.
    have callerRead : ((e.world n).state u).getCheckpointBlock root
        ((e.world r).state w).finalizedCheckpoint.epoch =
          .ok ((e.world r).state w).finalizedCheckpoint.root := by
      -- The finality is the anchor's, or at most the root's realized justification.
      have finalLe : ((e.world r).state w).finalizedCheckpoint.epoch ≤
            getCurrentEpoch anchorState ∨
          ((e.world r).state w).finalizedCheckpoint.epoch ≤
            rootState.currentJustifiedCheckpoint.epoch := by
        rcases (forwardOf r w receiver).finalized_add_two_le_or_anchor sound slots epochOk with
          lag | low
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
      rw [Store.getCheckpointBlock_trans rootRead belowJustified]
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
    obtain ⟨found, -⟩ := (e.blocks_of_partiallySynchronous sync preGloas admitted anchorStore
      anchored honest receiver (by simp only [Nat.max_zero]; omega) rBound current finalizedKnown
      signerKnown signerFinal).resolve_right (e.not_honestCollision_of_agree agree)
    exact ⟨signerBlock, found⟩
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
