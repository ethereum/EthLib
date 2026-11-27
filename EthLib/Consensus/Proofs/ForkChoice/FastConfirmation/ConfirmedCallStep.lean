module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedCalls
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HonestHeads
public import EthLib.Consensus.Proofs.ForkChoice.HeadTotality
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ReceiverExits
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.RootViability
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetCount
import EthLib.Consensus.Proofs.ForkChoice.JustifiedVotes
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedWalk
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalCoverage
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDrift
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# The confirmed roots of the calls of one validator

After consecutive calls of the rule by one honest validator, its last confirmed root covers heads.

It is on every up-to-date honest head from the slot after the last call to a horizon.

Otherwise two honest stores collide, or accountable-safety evidence holds.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models Serialization.Ssz SszType ConfirmedCalls

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-! ## The finalized order of honest stores -/

/-- A block of an honest store reaches each up-to-date honest receiver a delay later.

The sender's read at the block must give the finalized checkpoint of the receiver.

The receiver then holds the block with the sender's state for it.

Honest stores must agree on their blocks, and hold no state of a block with a zero state root. -/
private theorem carrier_delivered {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {m k : ℕ}
    (mBound : (e.world m).time ≤ last) (late : (e.world m).time + Δ ≤ (e.world k).time)
    (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (known : ((e.world m).state u).blocks[root]? = some block)
    (stored : ((e.world m).state u).blockStates[root]? = some state)
    (final : ((e.world m).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root) :
    ((e.world k).state w).blocks[root]? = some block ∧
      ((e.world k).state w).blockStates[root]? = some state := by
  have reachedW := e.reachable (fun x hx => (start x hx).symm ▸ Store.Reachable.anchor anchored)
    k w receiver
  -- The receiver holds its finalized block, as the anchor state's root is not zero.
  have finalizedKnown := reachedW.finalized_known sound (UInt64.le_of_eq anchorSlot) positive
    window (e.anchor_stateRoot_nonzero anchored start nonzero receiver bounded)
  rcases e.blocks_of_partiallySynchronous_of_anchorSlot sync (fun _ => UInt64.le_of_eq anchorSlot)
      admitted anchored sender receiver (start u sender) (start w receiver)
      (by simpa using late) bounded upToDate finalizedKnown known final with
    ⟨held, -⟩ | ⟨a, ha, b, hb, i, j, hi, hj, _, ⟨r, left, right⟩, found⟩
  · -- The receiver's state for the block is the sender's.
    obtain ⟨post, postFound, -, -⟩ := reachedW.blockStatesFromParents held
    have same := e.blockStates_eq anchored (start u sender) (start w receiver)
      (agree u sender w receiver m k mBound bounded) stored postFound
    subst post
    exact ⟨held, postFound⟩
  · obtain ⟨leftFound, rightFound, different⟩ := Store.findBlockCollision_held found
    exact absurd (agree a ha b hb i j hi hj r left right leftFound rightFound) different

/-- A delay after an event of an honest store, each up-to-date honest store has justified its epoch.

That epoch is the one of the finalized checkpoint of the sender at the event. -/
private theorem finalizedOrder {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    -- The finalized checkpoint of each receiver must be read at the justified root of each sender.
    (crossFinal : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (late : (e.world n).time + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) :
    ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachable (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored)
      i v honest
  have reachedU := (forward u sender n).reachable
  have reachedW := (forward w receiver k).reachable
  have nBound : (e.world n).time ≤ last := by omega
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  -- The receiver may have finalized the epoch already.
  by_cases covered : ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).finalizedCheckpoint.epoch
  · exact UInt64.le_trans covered (reachedW.finalized_le_justified sound)
  have below := UInt64.not_le.mp covered
  have finalLe := reachedU.finalized_le_justified sound
  have later : getCurrentEpoch anchorState < ((e.world n).state u).justifiedCheckpoint.epoch :=
    UInt64.lt_of_le_of_lt reachedW.anchor_le_finalized (UInt64.lt_of_lt_of_le below finalLe)
  have notZero := anchorState_hash_nonzero anchored start nonzero sender nBound
  -- The sender reads the receiver's finalized checkpoint at its justified root.
  have crossRead := crossFinal w receiver u sender k n bounded nBound
    (UInt64.le_of_lt (UInt64.lt_of_lt_of_le below finalLe))
  -- A held block that reads the sender's justified checkpoint reaches the receiver.
  have carry {root : Root} {state : BeaconState preset fork} {block : BeaconBlock preset fork}
      (known : ((e.world n).state u).blocks[root]? = some block)
      (stored : ((e.world n).state u).blockStates[root]? = some state)
      (read : ((e.world n).state u).getCheckpointBlock root
        ((e.world n).state u).justifiedCheckpoint.epoch =
          .ok ((e.world n).state u).justifiedCheckpoint.root) :
      ((e.world k).state w).blocks[root]? = some block ∧
        ((e.world k).state w).blockStates[root]? = some state := by
    refine carrier_delivered sync positive window admitted anchored sound anchorSlot start
      nonzero agree sender receiver nBound late bounded upToDate known stored ?_
    rw [Store.getCheckpointBlock_trans read
      (UInt64.le_of_lt (UInt64.lt_of_lt_of_le below finalLe))]
    exact crossRead
  obtain ⟨currentU, currentUOk⟩ := (forward u sender n).exists_getCurrentSlot slots
  -- The sender's justified checkpoint comes from the anchor, a held state, or its pull-up.
  --
  -- The block of that state reaches the receiver, whose justified epoch is then at least as late.
  rcases (forward u sender n).justified_origins_epoch positive slots currentUOk with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ |
      ⟨root, block, state, pulled, known, stored, run, same, earlier⟩
  · rw [same] at later
    exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨block, known⟩ := reachedU.known_of_blockState stored
    have read := (reachedU.getCheckpointBlock_of_blockState sound aligned positive window stored
      (.inl (by simp [same])) later).resolve_right notZero
    obtain ⟨_, held⟩ := carry known stored read.1
    rw [same] at finalLe
    exact UInt64.le_trans finalLe (reachedW.justified_le_of_blockState sound held)
  · have read := (reachedU.getCheckpointBlock_of_blockState sound aligned positive window stored
      (.inr ⟨pulled, run, by simp [same]⟩) later).resolve_right notZero
    obtain ⟨blockHeld, stateHeld⟩ := carry known stored read.1
    -- The receiver's clock is at or after the sender's.
    obtain ⟨currentW, currentWOk⟩ := (forward w receiver k).exists_getCurrentSlot slots
    have slotLe := e.currentSlot_le_of_time_le start sender receiver (by omega) upToDate
      currentUOk currentWOk
    have epochLe : computeEpochAtSlot preset currentU ≤ computeEpochAtSlot preset currentW :=
      UInt64.le_iff_toNat_le.mpr (epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp slotLe))
    rw [same] at finalLe
    exact UInt64.le_trans finalLe ((forward w receiver k).justified_le_of_pulledUp sound positive
      slots currentWOk blockHeld stateHeld run (UInt64.lt_of_lt_of_le earlier epochLe))

/-! ## The observed start of a call -/

/-- A delay after an earlier call, each up-to-date honest store has justified the observed epoch.

That epoch is the one of the caller's unrealized justified checkpoint at the earlier call. -/
private theorem observedOrder {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor)
    (aboveAnchor : ∀ epoch : Epoch, getCurrentEpoch anchorState ≤ epoch →
      ∀ s, computeStartSlotAtEpoch preset epoch = .ok s → anchorBlock.slot ≤ s)
    (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    -- The finalized checkpoint of each receiver must be read at the justified root of each sender.
    (crossFinal : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {m n k : ℕ}
    (order : m ≤ n) (nBound : (e.world n).time ≤ last)
    (late : (e.world m).time + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    -- A later call must hold that checkpoint as the caller's justified checkpoint.
    (realized : ((e.world n).state u).justifiedCheckpoint =
      ((e.world m).state u).unrealizedJustifiedCheckpoint)
    -- Each receiver must be in a later epoch than the earlier call.
    (laterEpoch : ∀ current currentW, ((e.world m).state u).getCurrentSlot config = .ok current →
      ((e.world k).state w).getCurrentSlot config = .ok currentW →
      computeEpochAtSlot preset current < computeEpochAtSlot preset currentW) :
    ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachable (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored)
      i v honest
  have reachedM := (forward u sender m).reachable
  have reachedN := (forward u sender n).reachable
  have reachedW := (forward w receiver k).reachable
  have mBound : (e.world m).time ≤ last := by omega
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  -- The receiver may have finalized the epoch already.
  by_cases covered : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).finalizedCheckpoint.epoch
  · exact UInt64.le_trans covered (reachedW.finalized_le_justified sound)
  have below := UInt64.not_le.mp covered
  have anchorLe := reachedW.anchor_le_finalized
  have later : getCurrentEpoch anchorState <
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch :=
    UInt64.lt_of_le_of_lt anchorLe below
  have notZero := anchorState_hash_nonzero anchored start nonzero sender mBound
  -- At the later call, the caller reads the receiver's finalized checkpoint at the observed root.
  have crossRead := crossFinal w receiver u sender k n bounded nBound
    (by rw [realized]; exact UInt64.le_of_lt below)
  rw [realized] at crossRead
  -- The block that gives the observed checkpoint at the earlier call reaches the receiver.
  have carry {root : Root} {state : BeaconState preset fork} {block : BeaconBlock preset fork}
      (stored : ((e.world m).state u).blockStates[root]? = some state)
      (known : ((e.world m).state u).blocks[root]? = some block)
      (member : ((e.world m).state u).unrealizedJustifiedCheckpoint ∈
          [state.currentJustifiedCheckpoint, state.previousJustifiedCheckpoint,
            state.finalizedCheckpoint] ∨
        ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
          ((e.world m).state u).unrealizedJustifiedCheckpoint ∈
            [pulled.currentJustifiedCheckpoint, pulled.previousJustifiedCheckpoint,
              pulled.finalizedCheckpoint]) :
      ((e.world k).state w).blocks[root]? = some block ∧
        ((e.world k).state w).blockStates[root]? = some state := by
    -- The later call still holds the block, with the same state.
    obtain ⟨post, storedN, -, -⟩ := reachedN.blockStatesFromParents (e.blocks_of_le order known)
    have same := e.blockStates_eq anchored (start u sender) (start u sender)
      (agree u sender u sender m n mBound nBound) stored storedN
    subst post
    have readN := (reachedN.getCheckpointBlock_of_blockState sound aligned positive window
      storedN member later).resolve_right notZero
    -- That read at the later call moves to the block that gives the observed checkpoint.
    have finalN : ((e.world n).state u).getCheckpointBlock root
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root := by
      rw [Store.getCheckpointBlock_trans readN.1 (UInt64.le_of_lt below)]
      exact crossRead
    -- The read moves back to the earlier call, which delivers the block.
    have boundaryOf := finalN
    unfold Store.getCheckpointBlock at boundaryOf
    simp only [bind_ok_iff] at boundaryOf
    obtain ⟨boundary, boundaryOk, -⟩ := boundaryOf
    have boundaryOk := mapError_ok_iff.mp boundaryOk
    -- The read then moves back to the earlier call, which holds the block and delivers it.
    exact carrier_delivered sync positive window admitted anchored sound anchorSlot start
      nonzero agree sender receiver mBound late bounded upToDate known stored
      (Store.getCheckpointBlock_of_same_blocks reachedM
        (agree u sender u sender n m nBound mBound) boundaryOk
        (aboveAnchor _ anchorLe _ boundaryOk) ⟨block, known⟩ finalN)
  rcases reachedM.justified_origins _ (.inr rfl) with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
  · rw [same] at later
    exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨block, known⟩ := reachedM.known_of_blockState stored
    obtain ⟨_, held⟩ := carry stored known (.inl (by simp [same]))
    rw [same]
    exact reachedW.justified_le_of_blockState sound held
  · obtain ⟨block, known⟩ := reachedM.known_of_blockState stored
    obtain ⟨blockHeld, stateHeld⟩ := carry stored known (.inr ⟨pulled, run, by simp [same]⟩)
    obtain ⟨currentM, currentMOk, blocksM, -⟩ := (forward u sender m).slots_le_current slots
      aligned
    obtain ⟨currentW, currentWOk⟩ := (forward w receiver k).exists_getCurrentSlot slots
    have blockLe : computeEpochAtSlot preset block.slot ≤ computeEpochAtSlot preset currentM :=
      UInt64.le_iff_toNat_le.mpr
        (epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp (blocksM root block known)))
    rw [same]
    exact (forward w receiver k).justified_le_of_pulledUp sound positive slots currentWOk
      blockHeld stateHeld run
      (UInt64.lt_of_le_of_lt blockLe (laterEpoch currentM currentW currentMOk currentWOk))

/-- The anchor block is at or before the first slot of each epoch from the anchor state's on.

The anchor block must be at its state's slot, and that slot must start an epoch. -/
private theorem anchor_le_epochStart (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true) :
    ∀ epoch : Epoch, getCurrentEpoch anchorState ≤ epoch →
      ∀ s, computeStartSlotAtEpoch preset epoch = .ok s → anchorBlock.slot ≤ s := by
  intro epoch le s sOk
  rw [isStartSlotAtEpoch_eq, Except.ok.injEq, decide_eq_true_eq] at anchorBoundary
  have sNat := (computeStartSlotAtEpoch_ok_iff.mp sOk).2
  have leNat := UInt64.le_iff_toNat_le.mp le
  rw [getCurrentEpoch_toNat, ← anchorSlot] at leNat
  have modNat := Nat.mod_add_div anchorBlock.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have mul := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat leNat
  apply UInt64.le_iff_toNat_le.mpr
  rw [sNat]
  rw [Nat.mul_comm] at modNat
  omega

/-- At an epoch's first slot, a call after the first one starts from the earlier call's view. -/
private theorem observedStart {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon : Epoch} {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
    (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    (sync : e.Synchronous Δ) (admitted : BlocksAdmitted e 0 Δ limit)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (agreement : SelectedCheckpointsAgree (e := e) horizon limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit)
    (finality : (∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root) ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit)
    {j n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) (j + 1) n fcr after)
    (callBound : (e.world n).time ≤ limit)
    {head base : Root} {slot : Slot}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    -- The call replaces its base by the observed checkpoint, so its slot starts an epoch.
    (replaces : ((e.world n).state u).ReplacesBase config after head base slot) :
    ∃ m, m ∈ events ∧ (e.world m).time + Δ < (e.world n).time ∧
      -- The observed checkpoint is the caller's unrealized justified checkpoint at the call before.
      after.currentEpochObservedJustifiedCheckpoint =
        ((e.world m).state u).unrealizedJustifiedCheckpoint ∧
      -- That checkpoint is of the epoch before the call's, and within the horizon.
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat + 1 =
        (computeEpochAtSlot preset slot).toNat ∧
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤ horizon ∧
      -- Unless two honest stores collide or cross-store evidence holds, the call has justified it.
      ((((e.world n).state u).justifiedCheckpoint =
          ((e.world m).state u).unrealizedJustifiedCheckpoint ∧
        -- Each up-to-date honest store from the call to the limit has then justified its epoch.
        ∀ w ∈ J, ∀ k, (e.world n).time ≤ (e.world k).time → (e.world k).time ≤ limit →
          UpToDate config checks sources (e.world k).time ((e.world k).view w)
            ((e.world k).state w) →
          ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
            ((e.world k).state w).justifiedCheckpoint.epoch) ∨
        HonestCollision (e := e) limit ∨ CrossStoreJustifiedEvidence (e := e) pre limit ∨
        CrossStoreDirectSafetyEvidence (e := e) pre limit) := by
  obtain ⟨anchored, sound, anchorSlot, anchorBoundary, start, slots, positive, long,
    window, nonzero, -, caller, anchorBefore, atSlots⟩ := id ctx
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachable (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored)
      i v honest
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  obtain ⟨m, fcrM, previous, before, -, slotN', slotNOk', -, observed⟩ := call_succ ctx calls
  have order : m ≤ n := Nat.le_of_lt before
  have mMem : m ∈ events := List.mem_of_getElem? previous.1
  obtain ⟨slotM, beginM, slotMOk, indexM, beginMOk, atM⟩ := atSlots j m previous.1
  obtain ⟨slotN, beginN, slotNOk, indexN, beginNOk, atN⟩ := atSlots (j + 1) n calls.1
  have slotEq : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  subst slotEq
  have slotEq' : slotN = slotN' := Except.ok.inj (slotNOk.symm.trans slotNOk')
  subst slotEq'
  -- Consecutive calls are a delay apart.
  have sumN : slotN.toNat = slotM.toNat + 1 := by omega
  have nextOk : addChecked slotM 1 = .ok slotN := addChecked_ok_iff.mpr
    ⟨by have := slotN.toNat_lt; simpa only [UInt64.toNat_one, ← sumN] using this,
      by simpa using sumN⟩
  obtain ⟨due, dueOk⟩ := fits.1
  have fitsStep := fits.2 slotM slotN beginM due beginN nextOk beginMOk dueOk beginNOk
  have late : (e.world m).time + Δ < (e.world n).time := by omega
  have mBound : (e.world m).time ≤ limit := by omega
  -- The call's slot starts its epoch, so the previous call is in the epoch before.
  have modN : slotN.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
    have boundary := replaces.1
    rw [isStartSlotAtEpoch_eq, Except.ok.injEq, decide_eq_true_eq] at boundary
    exact boundary
  have epochStep : (computeEpochAtSlot preset slotM).toNat + 1 =
      (computeEpochAtSlot preset slotN).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    rw [sumN]
    exact (Nat.succ_div_of_dvd (by rw [← sumN]; exact Nat.dvd_of_mod_eq_zero modN)).symm
  have epochMOk : ((e.world m).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slotM) := by
    simp [Store.getCurrentStoreEpoch, slotMOk, bind, Except.bind, pure, Except.pure]
  have epochNOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slotN) := by
    simp [Store.getCurrentStoreEpoch, slotNOk, bind, Except.bind, pure, Except.pure]
  -- This call observes the previous call's unrealized justified checkpoint.
  have observedEq : after.currentEpochObservedJustifiedCheckpoint =
      ((e.world m).state u).unrealizedJustifiedCheckpoint := by
    rcases observed with ⟨-, eq⟩ | ⟨notStart, -⟩
    · exact eq
    · rw [replaces.1] at notStart
      cases notStart
  have reachedM := (forward u caller m).reachable
  have reachedN := (forward u caller n).reachable
  have notZero := anchorState_hash_nonzero anchored start nonzero caller mBound
  -- The observed checkpoint is of the epoch before the call's.
  obtain ⟨observedBlock, epochN, foundN, epochNOk', ageOk⟩ := replaces.2.1
  cases Except.ok.inj (epochNOk'.symm.trans epochNOk)
  rw [observedEq] at foundN
  have age := (addChecked_ok_iff.mp ageOk).2
  simp only [UInt64.toNat_one] at age
  have observedLe : (computeEpochAtSlot preset observedBlock.slot).toNat ≤
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat := by
    rcases reachedM.checkpoints_known sound aligned positive window
        (checkpoint := ((e.world m).state u).unrealizedJustifiedCheckpoint) (by simp) with
      ⟨epochEq, hashed, -⟩ | ⟨later, -⟩ | zero
    · obtain ⟨anchorRoot, anchorHashed, held⟩ := reachedN.anchor_known
      have rootEq := Except.ok.inj (hashed.symm.trans anchorHashed)
      have blockEq : observedBlock = anchorBlock := by
        have found := Store.block_ok_iff.mp foundN
        rw [rootEq, held, Option.some.injEq] at found
        exact found.symm
      rw [blockEq, epochEq, anchorSlot]
      exact Nat.le_refl _
    · have fromRead {root : Root}
          (read : ((e.world m).state u).getCheckpointBlock root
            ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch =
              .ok ((e.world m).state u).unrealizedJustifiedCheckpoint.root) :
          (computeEpochAtSlot preset observedBlock.slot).toNat ≤
            ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat := by
        obtain ⟨block, held, le, -⟩ := Store.getCheckpointBlock_self positive read
        obtain rfl : block = observedBlock := Option.some.inj
          ((e.blocks_of_le order held).symm.trans (Store.block_ok_iff.mp foundN))
        exact le
      rcases reachedM.justified_origins _ (.inr rfl) with
        ⟨_, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
      · rw [same] at later
        exact (UInt64.lt_irrefl _ later).elim
      · exact fromRead ((reachedM.getCheckpointBlock_of_blockState sound aligned positive window
          stored (.inl (by simp [same])) later).resolve_right notZero).1
      · exact fromRead ((reachedM.getCheckpointBlock_of_blockState sound aligned positive window
          stored (.inr ⟨pulled, run, by simp [same]⟩) later).resolve_right notZero).1
    · exact (notZero zero).elim
  have upper := UInt64.le_iff_toNat_le.mp
    ((forward u caller m).justified_epoch_le_current sound slots aligned epochMOk).2
  have epochEq : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat + 1 =
      (computeEpochAtSlot preset slotN).toNat := by omega
  have uHorizon : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤ horizon :=
    UInt64.le_trans (UInt64.le_iff_toNat_le.mpr upper)
      (bounded u caller m _ mBound epochMOk)
  refine ⟨m, mMem, late, observedEq, epochEq, uHorizon, ?_⟩
  -- The caller's justified checkpoint and the receivers, unless some evidence holds.
  rcases agreement with selected | evidence
  swap
  · exact .inr (.inr (.inl evidence))
  rcases finality with crossFinal | evidence
  swap
  · exact .inr (.inr (.inr evidence))
  rcases e.blocksAgree_or_collision limit with agree | collision
  swap
  · exact .inr (.inl collision)
  left
  -- The call's justified checkpoint is of the observed epoch, so it is the observed checkpoint.
  have firstLe : (computeEpochAtSlot preset firstSlot).toNat ≤
      (computeEpochAtSlot preset slotN).toNat :=
    epoch_le_of_slot_le _ _ (by omega)
  have anchorLt := UInt64.lt_iff_toNat_lt.mp anchorBefore
  have justifiedUpper : ((e.world n).state u).justifiedCheckpoint.epoch.toNat + 1 ≤
      (computeEpochAtSlot preset slotN).toNat := by
    rcases (forward u caller n).justified_before_current sound positive slots anchorSlot
        slotNOk (by omega) with eq | lt
    · rw [eq]
      omega
    · exact UInt64.lt_iff_toNat_lt.mp lt
  have heldAtN {root : Root} {state : BeaconState preset fork}
      (stored : ((e.world m).state u).blockStates[root]? = some state) :
      ∃ block, ((e.world m).state u).blocks[root]? = some block ∧
        ((e.world n).state u).blocks[root]? = some block ∧
        ((e.world n).state u).blockStates[root]? = some state := by
    obtain ⟨block, known⟩ := reachedM.known_of_blockState stored
    have knownN := e.blocks_of_le order known
    obtain ⟨post, storedN, -, -⟩ := reachedN.blockStatesFromParents knownN
    have same := e.blockStates_eq anchored (start u caller) (start u caller)
      (agree u caller u caller m n mBound callBound) stored storedN
    subst post
    exact ⟨block, known, knownN, storedN⟩
  have justifiedLower : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world n).state u).justifiedCheckpoint.epoch := by
    rcases reachedM.justified_origins _ (.inr rfl) with
      ⟨_, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
    · rw [same]
      exact UInt64.le_trans reachedN.anchor_le_finalized (reachedN.finalized_le_justified sound)
    · obtain ⟨-, -, -, storedN⟩ := heldAtN stored
      rw [same]
      exact reachedN.justified_le_of_blockState sound storedN
    · obtain ⟨block, known, knownN, storedN⟩ := heldAtN stored
      have blockLe := (forward u caller m).block_epoch_le_current slots aligned slotMOk known
      rw [same]
      exact (forward u caller n).justified_le_of_pulledUp sound positive slots slotNOk knownN
        storedN run (UInt64.lt_iff_toNat_lt.mpr (by omega))
  have epochsEq : ((e.world n).state u).justifiedCheckpoint.epoch =
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch := by
    apply UInt64.toNat_inj.mp
    have := UInt64.le_iff_toNat_le.mp justifiedLower
    omega
  have realized := selected u caller u caller n m callBound mBound _ _ (.inl rfl) (.inr rfl)
    epochsEq (epochsEq ▸ uHorizon)
  refine ⟨realized, ?_⟩
  -- Each receiver is in a later epoch than the previous call, so it has justified the epoch.
  intro w receiver k afterCall kBound current
  refine observedOrder sync slots positive window admitted anchored sound anchorSlot
    start (anchor_le_epochStart anchorSlot anchorBoundary) nonzero agree crossFinal caller
    receiver order callBound (by omega) kBound current realized ?_
  intro currentM currentW currentMOk currentWOk
  obtain rfl : slotM = currentM := Except.ok.inj (slotMOk.symm.trans currentMOk)
  have slotLe := e.currentSlot_le_of_time_le start caller receiver afterCall current slotNOk
    currentWOk
  have epochLe := epoch_le_of_slot_le (preset := preset) _ _ (UInt64.le_iff_toNat_le.mp slotLe)
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-! ## The anchor facts and the carried facts of a call -/

/-- A block with an epoch descends from itself. -/
private theorem isAncestor_self_of_blockEpoch {store : Store preset fork} {root : Root}
    {epoch : Epoch} (read : store.getBlockEpoch root = .ok epoch) :
    store.isAncestor ⟨root, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  obtain ⟨block, found, -⟩ := found_of_blockEpoch read
  exact Store.isAncestor_self (node := ⟨root, .pending⟩) found

/-- Every up-to-date honest head by the limit descends from the anchor's finalized root. -/
private theorem anchor_cover {anchor : Store preset fork} {limit : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (absent : AnchorParentAbsent (e := e) limit) :
    HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root 0 (limit + 1) := by
  intro time _ lt a ha i hd _ _ headOk
  have bound : (e.world i).time ≤ limit := by omega
  have reached := e.reachable
    (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) i a ha
  have toJustified := Store.isAncestor_getHead headOk
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.held_of_isAncestor toJustified
  obtain ⟨headBlock, headFound, -⟩ := Store.slot_le_of_isAncestor justifiedFound toJustified
  obtain ⟨anchorRoot, hashed, -, -, -, final, -⟩ := getForkchoiceStore_anchor anchored
  have read := reached.getCheckpointBlock_anchor anchorSlot anchorBoundary
    (absent a ha i bound) headFound hashed
  obtain ⟨-, -, -, -, -, descends⟩ := Store.isAncestor_of_getCheckpointBlock read
  rw [Store.isAncestor_getHead_root headOk, final]
  exact descends

/-- The anchor's finalized root satisfies the call invariant at every call by the limit.

It also covers every up-to-date honest head from the call to the limit. -/
private theorem anchor_facts {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot) :
    ∀ n ∈ events, (e.world n).time ≤ limit →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
        anchor.finalizedCheckpoint.root ∧
      HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root (e.world n).time (limit + 1) := by
  intro n member _
  have from_ (t : ℕ) : HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root t (limit + 1) :=
    honestHeadsCover_mono
      (anchor_cover ctx.anchored ctx.start ctx.anchorSlot ctx.anchorBoundary ctx.absent)
      (Nat.zero_le t) le_rfl
  refine ⟨⟨fun _ _ following _ _ _ => from_ following.toNat, ?_, ?_⟩, from_ _⟩
  · intro epoch rootEpoch epochOk rootOk recent
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨slot, begin, slotOk, -, beginOk, -⟩ := ctx.atSlots index n found
    have boundary := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot
    have le :=
      (computeStartSlotAtEpoch_le_lt (UInt64.lt_iff_toNat_lt.mpr ctx.positive) boundary).1
    obtain ⟨time, timeOk, -⟩ :=
      exists_timeAtSlotMs_of_le (UInt64.le_iff_toNat_le.mpr le) beginOk
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
    exact ⟨_, rootEpoch, _, time, isAncestor_self_of_blockEpoch rootOk, rootOk, recent,
      boundary, timeOk, from_ _⟩
  · intro epoch _ rootOk
    exact ⟨n, le_rfl, anchor.finalizedCheckpoint.root, rootOk, rootOk,
      isAncestor_self_of_blockEpoch rootOk, Or.inl rfl, from_ _⟩

/-- The root that a call reads satisfies the call invariant at the call.

It also covers every up-to-date honest head from the call to the limit.

The first call reads the anchor's finalized root.

A later call reads the root of the call before it, whose invariant carries over. -/
private theorem carried_facts {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    (earlier : ∀ i' < i, ∀ n' fcr' after',
      CallAt (e := e) u events (getFastConfirmationStore anchor) i' n' fcr' after' →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n' after'.confirmedRoot) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n fcr.confirmedRoot ∧
      HonestHeadsCover (e := e) fcr.confirmedRoot (e.world n).time (limit + 1) := by
  cases i with
  | zero =>
    obtain ⟨rfl, -⟩ := call_zero ctx.long calls
    exact anchor_facts ctx n (List.mem_of_getElem? calls.1) nBound
  | succ j =>
    obtain ⟨m, before, previous⟩ := callAt_previous calls
    obtain ⟨slot, begin, slotOk, index, beginOk, atSlot⟩ := ctx.atSlots (j + 1) n calls.1
    obtain ⟨oldSlot, -, oldSlotOk, oldIndex, -, -⟩ := ctx.atSlots j m previous.1
    obtain ⟨eventLt, -⟩ := call_order ctx.toCallsCtx previous.1 calls.1 (Nat.lt_succ_self j)
    have nextOk : addChecked oldSlot 1 = .ok slot := addChecked_ok_iff.mpr ⟨by
      have := slot.toNat_lt
      simp only [UInt64.toNat_one]
      omega, by simp only [UInt64.toNat_one]; omega⟩
    have inv := earlier j (Nat.lt_succ_self j) m before fcr previous
    have cover : HonestHeadsCover (e := e) fcr.confirmedRoot (e.world n).time (limit + 1) := by
      rw [atSlot]
      exact inv.1 oldSlot slot begin oldSlotOk nextOk beginOk
    have mBound : (e.world m).time ≤ limit := (e.monotone_time eventLt.le).trans nBound
    obtain ⟨rootEpoch, oldRootOk⟩ := root_known (ctx.toCallsCtx.forward m).reachable ctx.sound
      ctx.anchorSlot ctx.positive ctx.window
      (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller mBound)
      previous.2.2
    have first : ∀ readSlot next following,
        ((e.world n).state u).getCurrentSlot config = .ok readSlot →
        addChecked readSlot 1 = .ok next →
        computeTimeAtSlotMs config genesisTimeMs next = .ok following →
        HonestHeadsCover (e := e) fcr.confirmedRoot following.toNat (limit + 1) := by
      intro readSlot next following readSlotOk readNextOk followingOk
      obtain rfl : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
      obtain ⟨due, dueOk⟩ := ctx.fits.1
      have late := ctx.fits.2 readSlot next begin due following readNextOk beginOk dueOk
        followingOk
      exact honestHeadsCover_mono cover (by omega) le_rfl
    have nowRootOk := e.getBlockEpoch_of_le eventLt.le oldRootOk
    have readBefore {epoch : Epoch}
        (read : ((e.world n).state u).getBlockEpoch fcr.confirmedRoot = .ok epoch) :
        ((e.world m).state u).getBlockEpoch fcr.confirmedRoot = .ok epoch := by
      obtain rfl : rootEpoch = epoch := Except.ok.inj (nowRootOk.symm.trans read)
      exact oldRootOk
    refine ⟨⟨first, ?_⟩, cover⟩
    by_cases boundary : isStartSlotAtEpoch preset slot = .ok true
    · -- At an epoch start, the kept root is its own historical root, of an earlier epoch.
      have boundaryOk := computeStartSlotAtEpoch_of_isStartSlotAtEpoch ctx.positive boundary
      have old : rootEpoch ≠ computeEpochAtSlot preset slot := by
        intro same
        obtain ⟨block, found, blockEpoch⟩ := found_of_blockEpoch oldRootOk
        have le := (ctx.toCallsCtx.forward m).block_epoch_le_current ctx.slots
          (UInt64.le_of_eq ctx.anchorSlot) oldSlotOk found
        have zero : computeSlotsSinceEpochStart preset slot = .ok 0 := by
          unfold isStartSlotAtEpoch at boundary
          cases offset : computeSlotsSinceEpochStart preset slot with
          | error fault => simp [offset, Except.mapError, bind, Except.bind] at boundary
          | ok offset' =>
            simp [offset, Except.mapError, bind, Except.bind, pure, Except.pure] at boundary
            rw [boundary]
        have lt := UInt64.lt_iff_toNat_lt.mp
          (epoch_lt_of_offset_zero (old := oldSlot) (UInt64.lt_iff_toNat_lt.mpr (by omega)) zero)
        rw [blockEpoch, same] at le
        omega
      constructor
      · intro epoch rootEpoch' epochOk rootOk recent
        obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
        refine ⟨fcr.confirmedRoot, rootEpoch', slot, begin, isAncestor_self_of_blockEpoch rootOk,
          rootOk, recent, boundaryOk, beginOk, ?_⟩
        rw [← atSlot]
        exact cover
      · intro epoch epochOk rootOk
        obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
        exact absurd (Except.ok.inj (nowRootOk.symm.trans rootOk)) old
    · -- Inside an epoch, the previous call's historical root and target origin carry over.
      have notMod : ¬ slot % preset.SLOTS_PER_EPOCH = 0 := by
        intro modZero
        apply boundary
        rw [isStartSlotAtEpoch_eq, Except.ok.injEq, decide_eq_true_eq]
        simpa [UInt64.toNat_mod] using congrArg UInt64.toNat modZero
      have sameEpoch : computeEpochAtSlot preset slot = computeEpochAtSlot preset oldSlot := by
        apply UInt64.toNat_inj.mp
        simp only [computeEpochAtSlot, UInt64.toNat_div]
        exact nextSlot_epoch_of_inside (by omega) notMod
      have epochBefore {epoch : Epoch}
          (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
          ((e.world m).state u).getCurrentStoreEpoch config = .ok epoch := by
        have epochEq := Store.getCurrentStoreEpoch_eq slotOk epochOk
        simp [Store.getCurrentStoreEpoch, oldSlotOk, epochEq, sameEpoch, bind, Except.bind,
          pure, Except.pure]
      constructor
      · intro epoch rootEpoch' epochOk rootOk recent
        obtain ⟨historical, historicalEpoch, epochStart, time, below, historicalOk,
          age, startOk, timeOk, historicalCover⟩ :=
          inv.2.1 epoch rootEpoch' (epochBefore epochOk) (readBefore rootOk) recent
        exact ⟨historical, historicalEpoch, epochStart, time,
          e.isAncestor_of_le eventLt.le below, e.getBlockEpoch_of_le eventLt.le historicalOk,
          age, startOk, timeOk, historicalCover⟩
      · intro epoch epochOk rootOk
        obtain ⟨k, kLe, origin, -, originOk, below, checked, originCover⟩ :=
          inv.2.2 epoch (epochBefore epochOk) (readBefore rootOk)
        exact ⟨k, kLe.trans eventLt.le, origin, rootOk,
          e.getBlockEpoch_of_le eventLt.le originOk, e.isAncestor_of_le eventLt.le below,
          checked, originCover⟩

/-! ## The finalized reset of the confirmed root -/

/-- A caller's finalized checkpoint other than the anchor's is old.

Its root's block epoch is at most its epoch.

That epoch is at least two epochs before the current epoch. -/
private theorem finalized_old {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {n : ℕ} (nBound : (e.world n).time ≤ limit)
    (other : ((e.world n).state u).finalizedCheckpoint ≠ anchor.finalizedCheckpoint) :
    ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ∃ rootEpoch, ((e.world n).state u).getBlockEpoch
          ((e.world n).state u).finalizedCheckpoint.root = .ok rootEpoch ∧
        rootEpoch.toNat ≤ ((e.world n).state u).finalizedCheckpoint.epoch.toNat ∧
        ((e.world n).state u).finalizedCheckpoint.epoch.toNat + 2 ≤ epoch.toNat := by
  intro epoch epochOk
  exact (ctx.forward n).finalized_epoch_add_two_le ctx.anchored ctx.sound
    (UInt64.le_of_eq ctx.anchorSlot) ctx.slots ctx.positive ctx.window
    (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller nBound) other epochOk

/-- The caller's finalized root satisfies the call invariant.

The anchor's finalized root satisfies it by the anchor's facts.

Any other finalized root is old, so only its coverage of the next slot remains.

A delay later, each up-to-date honest store has justified its epoch and reads it below its head. -/
private theorem finalized_invariant {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    (good : Good (e := e) horizon limit)
    (anchorFacts : ∀ n ∈ events, (e.world n).time ≤ limit →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
        anchor.finalizedCheckpoint.root ∧
      HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root (e.world n).time (limit + 1))
    {n : ℕ} (member : n ∈ events) (nBound : (e.world n).time ≤ limit) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
      ((e.world n).state u).finalizedCheckpoint.root := by
  by_cases same : ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint
  · rw [same]
    exact (anchorFacts n member nBound).1
  have old := finalized_old ctx nBound same
  refine ⟨?_, ?_, ?_⟩
  · intro slot next following slotOk nextOk followingOk earlier afterNext beforeEnd a honest i
      hd timeEq upToDate headOk
    -- The call is at its slot start, a delay before the following slot.
    obtain ⟨index, indexOk⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨slot', begin, slotOk', -, beginOk, atSlot⟩ := ctx.atSlots index n indexOk
    have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst sameSlot
    obtain ⟨due, dueOk⟩ := ctx.fits.1
    have bound := ctx.fits.2 slot' next begin due following nextOk beginOk dueOk followingOk
    have late : (e.world n).time + Δ ≤ (e.world i).time := by omega
    have iBound : (e.world i).time ≤ limit := by omega
    -- The receiver has justified the caller's finalized epoch.
    have le := finalizedOrder ctx.sync ctx.slots ctx.positive ctx.window
      ctx.admitted ctx.anchored ctx.sound ctx.anchorSlot ctx.start ctx.roots good.blocks
      good.finality ctx.caller honest late iBound upToDate
    -- The receiver reads that finality below its justified root.
    have read := good.finality u ctx.caller a honest n i nBound iBound le
    obtain ⟨-, finalBlock, -, finalFound, -, below⟩ :=
      Store.isAncestor_of_getCheckpointBlock read
    have headDescends := Store.isAncestor_getHead headOk
    obtain ⟨justifiedBlock, justifiedFound⟩ := Store.held_of_isAncestor headDescends
    exact Store.isAncestor_trans justifiedFound finalFound headDescends below
  · intro epoch rootEpoch epochOk rootOk recent
    obtain ⟨other, otherOk, low, lagged⟩ := old epoch epochOk
    rw [rootOk, Except.ok.injEq] at otherOk
    subst otherOk
    omega
  · intro epoch epochOk rootOk
    obtain ⟨other, otherOk, low, lagged⟩ := old epoch epochOk
    rw [rootOk, Except.ok.injEq] at otherOk
    subst otherOk
    omega

/-- A checked walk from the caller's finalized root makes it the anchor's finalized checkpoint.

The walk's start is in the current epoch or the one before.

Any other finalized root is at least two epochs old. -/
private theorem finalized_start_anchor {Δ : ℕ}
    {anchor : Store preset fork} {limit : ℕ} {horizon anchorEpoch : Epoch}
    {g : ForkedBeaconState preset} {pre : Run config checks g ⟨fork, anchorState⟩}
    {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {n : ℕ} (nBound : (e.world n).time ≤ limit)
    {fcr' : FastConfirmationStore} {head root : Root}
    (checked : ((e.world n).state u).FastConfirmationChecked config fcr' head
      ((e.world n).state u).finalizedCheckpoint.root root) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint := by
  by_contra other
  obtain ⟨epoch, -, -, startEpoch, epochOk, -, -, startOk, recent, -⟩ := checked
  obtain ⟨blockEpoch, blockOk, low, lagged⟩ := finalized_old ctx nBound other epoch epochOk
  rw [startOk, Except.ok.injEq] at blockOk
  subst blockOk
  omega

/-- A call that replaces its base holds the observed block, of the epoch before its slot.

The call's slot starts its epoch. -/
private theorem replaces_facts {store : Store preset fork} {after : FastConfirmationStore}
    {head base : Root} {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot)
    (replaces : store.ReplacesBase config after head base slot) :
    ∃ observedBlock : BeaconBlock preset fork,
      store.blocks[after.currentEpochObservedJustifiedCheckpoint.root]? = some observedBlock ∧
      (computeEpochAtSlot preset observedBlock.slot).toNat + 1 =
        (computeEpochAtSlot preset slot).toNat ∧
      observedBlock.slot ≤ slot ∧
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok slot := by
  have slotMod : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
    have isStart := replaces.1
    rw [isStartSlotAtEpoch_eq, Except.ok.injEq, decide_eq_true_eq] at isStart
    exact isStart
  obtain ⟨-, ⟨observedBlock, epoch, foundBlock, epochOk, epochAdd⟩, -, -⟩ := replaces
  obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
  have observedNat := (addChecked_ok_iff.mp epochAdd).2
  simp only [UInt64.toNat_one] at observedNat
  have slotEpochNat : (computeEpochAtSlot preset slot).toNat =
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  have blockEpochNat : (computeEpochAtSlot preset observedBlock.slot).toNat =
      observedBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  refine ⟨observedBlock, Store.block_ok_iff.mp foundBlock, observedNat.symm, ?_, ?_⟩
  · -- The observed block is of the epoch before the call's, so before the call slot.
    apply UInt64.le_iff_toNat_le.mpr
    have lt : observedBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat <
        slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by omega
    exact Nat.le_of_lt (Nat.lt_of_div_lt_div lt)
  · -- The call slot starts its epoch.
    apply computeStartSlotAtEpoch_ok_iff.mpr
    have eq : slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat =
        slot.toNat := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero slotMod)
    rw [slotEpochNat, eq]
    exact ⟨slot.toNat_lt, rfl⟩

/-- At a call that replaces its base, the observed justified block covers up-to-date honest heads.

It holds to the limit, or stores collide, or cross-store direct-safety or justified evidence holds.

It assumes synchrony, delayed admission, fitting delays, signed justifications and nonzero roots.

It also needs direct-safety premises, the anchor at an epoch start, slot reads and the call run. -/
theorem Execution.observedRestart_covers_or_evidence
    {Δ limit : ℕ} {anchor : Store preset fork} {horizon : Epoch} {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩) (genesis : Genesis config checks g)
    (parameters : DirectSafety.Parameters preset) (sync : e.Synchronous Δ)
    (admitted : BlocksAdmitted e 0 Δ limit) (fits : DelayFits fork config genesisTimeMs Δ)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (roots : HeldBlockStateRootsNonzero (e := e) limit) (absent : AnchorParentAbsent (e := e) limit)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) limit)
    (enough : HeldRunStakeFloor (e := e) pre horizon limit)
    (terminal : HeldTerminalStakeFloor (e := e) horizon limit)
    (signedAll : JustifiedHonestlySigned (e := e) anchor.justifiedCheckpoint.epoch 0 limit)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (anchorBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧ slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧ (e.world n).time = begin.toNat)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit) {head base : Root} {slot : Slot}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (replaces : ((e.world n).state u).ReplacesBase config after head base slot) :
    HonestHeadsCover (e := e) after.currentEpochObservedJustifiedCheckpoint.root (e.world n).time
      (limit + 1) ∨
    HonestCollision (e := e) limit ∨ CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
    CrossStoreJustifiedEvidence (e := e) pre limit := by
  classical
  have sound := (DirectSafety.run_justified_separated pre genesis).1
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have ctx : CallsCtx (e := e) anchor u events firstSlot limit :=
    ⟨anchored, sound, anchorSlot, anchorBoundary, start, slots, positive, long, window, roots,
      absent, caller, anchorBefore, atSlots⟩
  cases i with
  | zero =>
    -- The first call observes the anchor's finalized checkpoint.
    left
    rw [(call_zero long calls).2]
    exact honestHeadsCover_mono (anchor_cover anchored start anchorSlot anchorBoundary absent)
      (Nat.zero_le _) le_rfl
  | succ j =>
    -- Justified checkpoints agree, and finality reads across stores, unless evidence holds.
    rcases e.selectedCheckpointsAgree_or_evidence anchored start anchorSlot roots absent
        parameters genesis pre heldEarly enough terminal with agree | justified
    swap
    · exact .inr (.inr (.inr justified))
    rcases e.crossStoreFinality_or_evidence anchored start anchorSlot anchorBoundary slots bounded
        roots absent parameters genesis pre heldEarly enough terminal with crossFinal | direct
    swap
    · exact .inr (.inr (.inl direct))
    -- A later call observes an earlier call's unrealized justified checkpoint, of the epoch before.
    obtain ⟨m, -, mBefore, observed, epochSucc, horizonLe, rest⟩ := observedStart pre
      ctx sync admitted fits bounded (.inl agree) (.inl crossFinal) calls nBound slotOk replaces
    rcases rest with ⟨-, later⟩ | collision | justified | direct
    rotate_left
    · exact .inr (.inl collision)
    · exact .inr (.inr (.inr justified))
    · exact .inr (.inr (.inl direct))
    by_cases collision : HonestCollision (e := e) limit
    · exact .inr (.inl collision)
    left
    rw [← observed] at epochSucc horizonLe later
    have mTime : (e.world m).time ≤ limit := by omega
    obtain ⟨slot', begin, slotOk', slotEq, beginOk, timeEq⟩ := atSlots (j + 1) n calls.1
    rw [slotOk, Except.ok.injEq] at slotOk'
    subst slot'
    obtain ⟨observedBlock, callerHeld, observedNat, blockLe, callSlotOk⟩ :=
      replaces_facts slotOk replaces
    -- The anchor's justified epoch is before the call's.
    obtain ⟨anchorRoot, -, -, -, anchorJustified, -⟩ := getForkchoiceStore_anchor anchored
    have anchorNat : anchor.justifiedCheckpoint.epoch.toNat <
        (computeEpochAtSlot preset slot).toNat := by
      have before := UInt64.lt_iff_toNat_lt.mp anchorBefore
      rw [anchorJustified]
      simp only [computeEpochAtSlot, UInt64.toNat_div] at before ⊢
      have : firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
          slot.toNat / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
      omega
    have forward := e.forwardReachable
      (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored)
    -- Coverage, by induction on the time.
    have cover : ∀ T, T ≤ limit + 1 → HonestHeadsCover (e := e)
        after.currentEpochObservedJustifiedCheckpoint.root (e.world n).time T := by
      intro T
      induction T with
      | zero => intro _ earlier _ high; omega
      | succ T ih =>
        intro bound earlier low high w receiver k hd atTime upToDate headOk
        by_cases before : earlier < T
        · exact ih (by omega) earlier low before w receiver k hd atTime upToDate headOk
        have same : earlier = T := by omega
        subst same
        have covers := ih (by omega)
        have kLow : (e.world n).time ≤ (e.world k).time := by omega
        have kHigh : (e.world k).time ≤ limit := by omega
        have headAbove := Store.isAncestor_getHead headOk
        have lower := later w receiver k kLow kHigh upToDate
        by_cases sameEpoch : after.currentEpochObservedJustifiedCheckpoint.epoch =
            ((e.world k).state w).justifiedCheckpoint.epoch
        · -- The same epoch: a receiver's justified checkpoint of that epoch is the observed one.
          have eq := agree u caller w receiver m k mTime kHigh _ _ (.inr observed)
            (.inl rfl) sameEpoch horizonLe
          rw [eq]
          exact headAbove
        -- A later epoch: the justified block descends from the observed one, by its signer.
        --
        -- A later justified checkpoint has an honest signer, putting it above the observed block.
        have laterEpoch : (computeEpochAtSlot preset slot).toNat ≤
            ((e.world k).state w).justifiedCheckpoint.epoch.toNat := by
          have le := UInt64.le_iff_toNat_le.mp lower
          have ne : after.currentEpochObservedJustifiedCheckpoint.epoch.toNat ≠
              ((e.world k).state w).justifiedCheckpoint.epoch.toNat :=
            fun h => sameEpoch (UInt64.toNat_inj.mp h)
          omega
        have early : slot.toNat ≤
            ((e.world k).state w).justifiedCheckpoint.epoch.toNat *
              preset.SLOTS_PER_EPOCH.toNat := by
          have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat laterEpoch
          have := (computeStartSlotAtEpoch_ok_iff.mp callSlotOk).2
          omega
        obtain ⟨current, currentOk, _, _⟩ :=
          (forward k w receiver).slots_le_current slots (UInt64.le_of_eq anchorSlot)
        obtain ⟨v, honest, _, -, msg, sent, data, member, target, before⟩ := signedAll w
          receiver k current (Nat.zero_le _) kHigh upToDate currentOk
          (UInt64.lt_iff_toNat_lt.mpr (by omega))
        obtain ⟨k', -, duty⟩ := e.exists_maySign_of_signed sent member honest
        -- The signer's duty is in the justified epoch, so at or after the call's slot.
        have dutyCopy := duty
        obtain ⟨_, -, -, -, -, made, -⟩ := dutyCopy
        obtain ⟨_, _, _, _, -, -, -, -, dataOk⟩ := made
        have slotLe : slot ≤ data.slot := by
          rw [← target, target_epoch_eq_of_getAttestationData dataOk] at early
          simp only [computeEpochAtSlot, UInt64.toNat_div] at early
          have := Nat.div_mul_le_self data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
          exact UInt64.le_iff_toNat_le.mpr (by omega)
        obtain ⟨low', high'⟩ := duty_window_of_slot_le start fits beginOk receiver
          upToDate currentOk honest duty slotLe before
        obtain ⟨justifiedBlock, justifiedKnown⟩ := Store.held_of_isAncestor headAbove
        have descends := (justified_descends_of_duty anchored start anchorSlot
          anchorBoundary roots caller callerHeld nBound covers
          (by omega) receiver atTime ⟨justifiedBlock, justifiedKnown⟩
          ((UInt64.le_iff_toNat_le.mp blockLe).trans early) honest duty target (by omega)
          high').resolve_right collision
        obtain ⟨rootBlock, rootKnown⟩ := Store.held_of_isAncestor descends
        exact Store.isAncestor_trans justifiedKnown rootKnown headAbove
          descends
    exact cover (limit + 1) le_rfl

/-- At a call that replaces its base, the observed justified checkpoint covers honest heads.

It keeps the call invariant, or one of the evidence alternatives holds. -/
private theorem observed_facts [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    -- The first call observes the anchor's finalized checkpoint, whose invariant is given.
    (anchorInvariant : ∀ n ∈ events, (e.world n).time ≤ limit →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
        anchor.finalizedCheckpoint.root)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head base : Root} {slot : Slot}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (replaces : ((e.world n).state u).ReplacesBase config after head base slot) :
    (CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
        after.currentEpochObservedJustifiedCheckpoint.root ∧
      -- Its block is on every up-to-date honest head from the call to the limit.
      HonestHeadsCover (e := e) after.currentEpochObservedJustifiedCheckpoint.root
        (e.world n).time (limit + 1)) ∨
    Bad (e := e) pre limit := by
  rcases e.observedRestart_covers_or_evidence pre ctx.genesis ctx.parameters ctx.sync
      ctx.admitted ctx.fits ctx.anchored ctx.start ctx.anchorSlot ctx.anchorBoundary ctx.slots
      ctx.long ctx.roots ctx.absent ctx.bounded ctx.heldEarly ctx.enough ctx.terminal
      (ctx.anchorEpochOk ▸ ctx.signedAll) ctx.caller ctx.anchorEpochBefore ctx.atSlots calls
      nBound slotOk replaces with coverAll | collision | direct | justified
  rotate_left
  · exact .inr (.inl collision)
  · exact .inr (.inr (.inr (.inl direct)))
  · exact .inr (.inr (.inr (.inr (.inl justified))))
  refine .inl ⟨?_, coverAll⟩
  cases i with
  | zero =>
    -- The first call observes the anchor's finalized checkpoint.
    rw [(call_zero ctx.long calls).2]
    exact anchorInvariant n (List.mem_of_getElem? calls.1) nBound
  | succ j =>
    obtain ⟨slot', begin, slotOk', -, beginOk, timeEq⟩ := ctx.atSlots (j + 1) n calls.1
    rw [slotOk, Except.ok.injEq] at slotOk'
    subst slot'
    obtain ⟨observedBlock, callerHeld, observedNat, -, callSlotOk⟩ :=
      replaces_facts slotOk replaces
    refine ⟨?_, ?_, ?_⟩
    · -- From the next slot.
      intro slot2 next following slotOk2 nextOk followingOk
      rw [slotOk, Except.ok.injEq] at slotOk2
      subst slot2
      have nextNat := (addChecked_ok_iff.mp nextOk).2
      simp only [UInt64.toNat_one] at nextNat
      obtain ⟨start', startOk', -, startLe⟩ := exists_timeAtSlotMs_of_le
        (UInt64.le_iff_toNat_le.mpr (by omega) : slot ≤ next) followingOk
      rw [beginOk, Except.ok.injEq] at startOk'
      subst start'
      have := UInt64.le_iff_toNat_le.mp startLe
      intro earlier low high
      exact coverAll earlier (by omega) high
    · -- The observed block is its own recent historical root, covered from the epoch start.
      intro epoch rootEpoch epochOk2 rootEpochOk near
      obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk2
      refine ⟨_, rootEpoch, slot, begin,
        Store.isAncestor_self (node := ⟨after.currentEpochObservedJustifiedCheckpoint.root,
          .pending⟩) callerHeld, rootEpochOk, near, callSlotOk, beginOk, ?_⟩
      rw [← timeEq]
      exact coverAll
    · -- The observed block is not of the current epoch.
      intro epoch epochOk2 rootEpochOk
      exfalso
      obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk2
      obtain ⟨found, foundHeld, rootEq⟩ := found_of_blockEpoch rootEpochOk
      rw [callerHeld, Option.some.injEq] at foundHeld
      subst foundHeld
      have := congrArg UInt64.toNat rootEq
      omega

/-! ## The call step

A call keeps the call invariant, given the invariant at every earlier call.
-/

/-- One call of one honest validator keeps the call invariant, given it at every earlier call.

The alternatives are an honest-store collision and four kinds of accountable-safety evidence. -/
private theorem Execution.callInvariant_step [DecidablePred (· ∈ J)] {Δ : ℕ}
    {anchor : Store preset fork} {limit : ℕ} {horizon anchorEpoch : Epoch}
    {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    -- The execution verifies signatures with BLS, as the pulled-up head state of the rule does.
    (bls : checks = .bls)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (exitWindow : preset.SeedLookaheadAtLeastThree)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon)
    (weights : .glamsterdam ≤ fork → config.HeadWeightsFit preset (2 * 10 ^ 17))
    (supply : .glamsterdam ≤ fork → CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) limit)
    (admitted : BlocksAdmitted e 0 Δ limit)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (long : 1 < preset.SLOTS_PER_EPOCH)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (votes : ValidatedDutyVotes (e := e) limit) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e limit) (windows : AssignmentWindowAgreement (e := e) limit)
    (fit : config.CommitteeWindowsFit preset)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (roots : HeldBlockStateRootsNonzero (e := e) limit)
    (unslashed : HonestCountedStatesUnslashed (e := e) limit)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) (genesis : Genesis config checks g)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) limit)
    (enough : HeldRunStakeFloor (e := e) pre horizon limit)
    (terminal : HeldTerminalStakeFloor (e := e) horizon limit)
    (absent : AnchorParentAbsent (e := e) limit)
    (pinned : JustifiedPinned (e := e) anchorEpoch 0 0 limit)
    (signedAll : JustifiedHonestlySigned (e := e) anchorEpoch 0 limit)
    (fusaka : .fusaka ≤ fork) (band : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (included : TargetIncluded (e := e) limit) (stale : StaleHeadVotersInWindow (e := e) limit)
    (reference : ∃ x ∈ J, ∃ m, ∃ referenceSlot finish : Slot, limit ≤ (e.world m).time ∧
      UpToDate config checks sources (e.world m).time ((e.world m).view x)
        ((e.world m).state x) ∧
      ((e.world m).state x).getCurrentSlot config = .ok referenceSlot ∧
      subChecked referenceSlot 1 = .ok finish)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot)
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
      ((e.world n).view u) ((e.world n).state u))
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    (obligations : CallObligations (e := e) 0 limit u n fcr after)
    (earlier : ∀ i' < i, ∀ n' fcr' after',
      CallAt (e := e) u events (getFastConfirmationStore anchor) i' n' fcr' after' →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n'
        after'.confirmedRoot) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n after.confirmedRoot ∨
      HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit ∨
        HeldStateFinalityEvidence (e := e) pre limit := by
  have positive := fit.positive
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have incrementPositive := band.1
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot :=
    { bls, anchorGenesis, sync, slots, positive, minLookahead, exitWindow, ring, room, weights,
      supply,
      admitted, half, long, window, maxAligned, incrementPositive, votes, fits, prompt,
      windows, fit, anchored, sound, anchorSlot, anchorBoundary, start,
      anchorEpochOk, increment, bounded, roots, unslashed, ceiling, scoreFits, parameters,
      genesis, heldEarly, enough, terminal, absent, pinned, signedAll, fusaka,
      included, stale, reference, caller,
      confirmationEpoch, anchorEpochBefore, upToDate, atSlots }
  suffices goal : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
      after.confirmedRoot ∨ Bad (e := e) pre limit from goal
  -- Honest justified checkpoints agree, or the cross-store justified evidence holds.
  rcases e.selectedCheckpointsAgree_or_evidence anchored start anchorSlot roots absent parameters
      genesis pre heldEarly enough terminal with agree | evidence
  swap
  · exact .inr (.inr (.inr (.inr (.inl evidence))))
  -- Each store's finalized checkpoint is on the chain of each justified one, or evidence holds.
  rcases e.crossStoreFinality_or_evidence anchored start anchorSlot anchorBoundary slots bounded
      roots absent parameters genesis pre heldEarly enough terminal with finality | evidence
  swap
  · exact .inr (.inr (.inr (.inl evidence)))
  -- Honest stores agree on blocks, or two collide.
  rcases e.blocksAgree_or_collision limit with blocks | collision
  swap
  · exact .inr (.inl collision)
  -- The stake of each call's voters drifts by at most the call's reserve.
  have quorum : QuorumDriftWithin (e := e) horizon limit := by
    subst bls
    have maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := by
      have : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := exitWindow
      omega
    exact e.quorumDriftWithin anchored start anchorSlot slots positive genesis pre room fusaka
      forkWindow bounded maxLookahead band withdrawDelay caps activation
  have good : Good (e := e) horizon limit := ⟨agree, finality, blocks, quorum⟩
  have anchorFacts := anchor_facts ctx
  have member : n ∈ events := List.mem_of_getElem? calls.1
  obtain ⟨head, slot, start0, headOk, slotOk, selects, result⟩ :=
    Store.onFastConfirmation_checked calls.2.2
  -- The start is the previous call's stored root, the finalized root or the observed justified one.
  --
  -- Each start keeps the invariant, and the walk from the head to the start then keeps it too.
  --
  -- The selected start keeps the invariant and, for a walk, covers from the call on.
  have startFacts : (CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start0 ∧
      HonestHeadsCover (e := e) start0 (e.world n).time (limit + 1)) ∨
      Bad (e := e) pre limit ∨
      (start0 = ((e.world n).state u).finalizedCheckpoint.root ∧
        CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start0 ∧
        (((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint →
          HonestHeadsCover (e := e) start0 (e.world n).time (limit + 1))) := by
    obtain ⟨base, baseCase, startCase⟩ := selects
    rcases startCase with ⟨rfl, _⟩ | ⟨rfl, replaces⟩
    · rcases baseCase with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact .inl (carried_facts ctx calls nBound earlier)
      · refine .inr (.inr ⟨rfl, finalized_invariant ctx good anchorFacts member nBound,
          fun same => ?_⟩)
        rw [same]
        exact (anchorFacts n member nBound).2
    · rcases observed_facts ctx (fun n member bound => (anchorFacts n member bound).1) calls nBound
          slotOk replaces with facts | bad
      · exact .inl facts
      · exact .inr (.inl bad)
  -- The call's stored root is its start, or a root on the walk from its head to that start.
  rcases result with same | ⟨-, checked, source, chain, later, sourceOk, walked,
    confirmedAll⟩
  · -- No walk: the stored root is the selected start.
    rw [same]
    rcases startFacts with facts | bad | ⟨_, inv, _⟩
    · exact .inl facts.1
    · exact .inr bad
    · exact .inl inv
  -- A walk: the start's facts, then the walk's inputs, holding, coverage and invariant.
  have startBoth : (CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start0 ∧
      HonestHeadsCover (e := e) start0 (e.world n).time (limit + 1)) ∨
      Bad (e := e) pre limit := by
    rcases startFacts with facts | bad | ⟨rfl, inv, covers⟩
    · exact .inl facts
    · exact .inr bad
    · exact .inl ⟨inv, covers (finalized_start_anchor ctx nBound checked)⟩
  rcases startBoth with ⟨startInv, startCovers⟩ | bad
  swap
  · exact .inr bad
  have inputs := walk_inputs ctx calls nBound headOk slotOk selects checked sourceOk walked
    confirmedAll obligations startInv
  rcases walk_holds ctx calls nBound headOk slotOk selects checked sourceOk walked
      confirmedAll obligations with holds | bad
  swap
  · exact .inr bad
  have onChainAll := sourceOnParentChain_of_walk anchored sound anchorSlot anchorBoundary start
    slots positive long window roots absent caller anchorEpochBefore atSlots calls nBound
    headOk slotOk selects checked walked
  -- Each walked member is covered from the call to the horizon, from the coverage of its parent.
  rcases walkMembers_cover ctx good calls nBound headOk slotOk selects checked sourceOk walked
      confirmedAll obligations startInv startCovers inputs holds onChainAll with covers | bad
  swap
  · exact .inr bad
  exact .inl (walk_invariant ctx calls headOk slotOk checked walked confirmedAll startInv inputs
    (covers after.confirmedRoot (by simp)))

/-- Every event of a run of calls starts no later than the slot after the last event. -/
private theorem time_le_following {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {n : ℕ} {slot next : Slot} {following : UInt64}
    (lastEvent : events.getLast? = some n)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    {i m : ℕ} (event : events[i]? = some m) :
    (e.world m).time ≤ following.toNat := by
  have lastAt : events[events.length - 1]? = some n := by
    rw [← List.getLast?_eq_getElem?]; exact lastEvent
  obtain ⟨slotL, -, slotOkL, slotEqL, -, -⟩ := atSlots _ _ lastAt
  rw [slotOk] at slotOkL
  cases slotOkL
  obtain ⟨slotI, beginI, -, slotEqI, beginOkI, timeEqI⟩ := atSlots _ _ event
  have iLt : i < events.length := (List.getElem?_eq_some_iff.mp event).1
  have nextEq := (addChecked_ok_iff.mp nextOk).2
  have le : slotI ≤ next := UInt64.le_iff_toNat_le.mpr (by simp at nextEq; omega)
  obtain ⟨start, startOk, -, startLe⟩ := exists_timeAtSlotMs_of_le le followingOk
  rw [beginOkI] at startOk
  cases startOk
  rw [timeEqI]
  exact UInt64.le_iff_toNat_le.mp startLe

/-- The confirmed root of the last of consecutive calls of one honest validator covers honest heads.

Every up-to-date honest head descends from it, from the slot after the last call to the horizon.

The alternatives are a collision of two honest stores and four kinds of accountable-safety evidence.

The evidence is historical, cross-store direct-safety, cross-store justified or held-state finality.
-/
theorem Execution.confirmedRoot_covers [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    -- The execution verifies signatures with BLS, as the pulled-up head state of the rule does.
    (pre : Run config checks g ⟨fork, anchorState⟩) (bls : checks = .bls)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (exitWindow : preset.SeedLookaheadAtLeastThree)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    -- From Gloas, the anchor's registry leaves room up to the horizon, an assumption on the anchor.
    --
    -- Like the weak-head bound below, it says nothing before Gloas.
    (room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon)
    -- From Gloas the head weights of the configuration fit, a configuration fact.
    (weights : .glamsterdam ≤ fork → config.HeadWeightsFit preset (2 * 10 ^ 17))
    -- From Gloas, honest justified states through the limit bound each weak-head weight.
    --
    -- The bound is 2·10^17 Gwei, and this assumption says nothing before Gloas.
    (supply : .glamsterdam ≤ fork → CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) limit)
    (admitted : BlocksAdmitted e 0 Δ limit)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (long : 1 < preset.SLOTS_PER_EPOCH)
    -- The maximum effective balances of the preset are aligned, as they are on mainnet and minimal.
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (votes : ValidatedDutyVotes (e := e) limit) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e limit) (windows : AssignmentWindowAgreement (e := e) limit)
    (fit : config.CommitteeWindowsFit preset)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (roots : HeldBlockStateRootsNonzero (e := e) limit)
    (unslashed : HonestCountedStatesUnslashed (e := e) limit)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) (genesis : Genesis config checks g)
    (enough : HeldRunStakeFloor (e := e) pre horizon limit)
    (terminal : HeldTerminalStakeFloor (e := e) horizon limit)
    (absent : AnchorParentAbsent (e := e) limit)
    -- An assumption on the run: the justification of each call's epoch is pinned.
    (pinned : JustifiedPinned (e := e) anchorEpoch 0 0 limit)
    -- An assumption on the run: the anchor's latest header is the anchor block's.
    --
    -- Its state root is zero.
    --
    -- The anchor store checks neither condition.
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    -- The inclusion delay is positive on mainnet and minimal.
    (delay : preset.InclusionDelayPositive)
    -- An assumption on the run: Byzantine stake is under two thirds in each vote-counting state.
    --
    -- It holds after the anchor's justified epoch.
    --
    -- It buys the honest signer of each later justification.
    (byzantine : ByzantineCountedStake (e := e) anchorEpoch 0 limit)
    -- The fork is Fulu or later.
    (fusaka : .fusaka ≤ fork) (band : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (included : TargetIncluded (e := e) limit) (stale : StaleHeadVotersInWindow (e := e) limit)
    (reference : ∃ x ∈ J, ∃ m, ∃ referenceSlot finish : Slot, limit ≤ (e.world m).time ∧
      UpToDate config checks sources (e.world m).time ((e.world m).view x)
        ((e.world m).state x) ∧
      ((e.world m).state x).getCurrentSlot config = .ok referenceSlot ∧
      subChecked referenceSlot 1 = .ok finish)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    -- An assumption on the run: the first slot's epoch is at least two.
    --
    -- It is also after the epoch of the anchor state.
    (confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot)
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
      ((e.world n).view u) ((e.world n).state u))
    -- The calls are at consecutive slots from the first slot.
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {last : FastConfirmationStore}
    (folded : (events.map fun n => (e.world n).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) (getFastConfirmationStore anchor) =
        .ok last)
    -- Each call assumes its obligations.
    (obligations : ∀ i n fcr after,
      CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after →
      CallObligations (e := e) 0 limit u n fcr after)
    {n : ℕ} {slot next : Slot} {following : UInt64}
    (lastEvent : events.getLast? = some n)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (followingLe : following.toNat ≤ limit) :
    HonestHeadsCover (e := e) last.confirmedRoot following.toNat (limit + 1) ∨
      HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit ∨
        HeldStateFinalityEvidence (e := e) pre limit := by
  -- Honest stores hold only states before the next fork, from the horizon.
  have heldEarly := e.heldStatesBeforeUpgrade_of_bounded anchored start anchorSlot slots
    fit.positive forkWindow bounded
  -- Honest validators sign each justified checkpoint after the anchor's epoch.
  have afterAnchor : getCurrentEpoch anchorState ≤ anchorEpoch := by
    obtain ⟨_, -, -, -, anchorJustified, -⟩ := getForkchoiceStore_anchor anchored
    rw [← anchorEpochOk, anchorJustified]
    exact UInt64.le_refl _
  have signedAll := Execution.justifiedHonestlySigned anchored start anchorSlot anchorHeader
    anchorZero slots parameters delay genesis pre roots absent heldEarly bounded enough terminal
    afterAnchor byzantine
  by_cases bad : Bad (e := e) pre limit
  · exact .inr bad
  have timeLe : ∀ i m, events[i]? = some m → (e.world m).time ≤ limit := fun i m event =>
    Nat.le_trans (time_le_following atSlots lastEvent slotOk nextOk followingOk event)
      followingLe
  -- The cover of the last root reads the call-invariant step at every call of the run.
  --
  -- The call invariant holds at every call, by strong induction on the call's index.
  have invariant : ∀ i n fcr after,
      CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n after.confirmedRoot := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i earlier =>
      intro n fcr after calls
      rcases e.callInvariant_step pre bls anchorGenesis sync slots minLookahead exitWindow ring
        room weights supply admitted half long maxAligned votes fits prompt windows fit anchored
        anchorSlot anchorBoundary start anchorEpochOk increment bounded roots unslashed ceiling
        scoreFits parameters genesis heldEarly enough terminal absent pinned signedAll fusaka band
        withdrawDelay caps activation forkWindow included stale reference caller confirmationEpoch
        anchorEpochBefore upToDate atSlots calls
        (timeLe i n calls.1) (obligations i n fcr after calls) (fun i' lt => earlier i' lt) with
        holds | evidence
      · exact holds
      · exact absurd evidence bad
  -- The last call is the last step of the run of calls.
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp lastEvent
  rw [List.map_append, List.foldlM_append] at folded
  cases prefixOk : (ys.map fun n => (e.world n).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) (getFastConfirmationStore anchor) with
  | error fault => simp [prefixOk, bind, Except.bind] at folded
  | ok fcr =>
    simp only [prefixOk, bind, Except.bind, List.map_cons, List.map_nil, List.foldlM_cons,
      List.foldlM_nil] at folded
    have callOk : ((e.world n).state u).onFastConfirmation config fcr = .ok last := by
      cases called : ((e.world n).state u).onFastConfirmation config fcr with
      | error fault => simp [called] at folded
      | ok after => simpa [called, pure, Except.pure] using folded
    have calls : CallAt (e := e) u (ys ++ [n]) (getFastConfirmationStore anchor) ys.length n
        fcr last := ⟨by simp, by simpa using prefixOk, callOk⟩
    exact .inl ((invariant _ _ _ _ calls).1 slot next following slotOk nextOk followingOk)

end EthLib.Consensus.Models.Network
