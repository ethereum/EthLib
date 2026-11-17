module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ReceiverExits
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.RootViability
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification

/-!
# The confirmed roots of the calls of one validator

A delay after an event of an honest store, each up-to-date honest store has justified its epoch.

That epoch is the one of the finalized checkpoint of the first store at the event.

The same holds for the unrealized justified checkpoint of a caller at an earlier call.

That needs a later call at which the caller's justified checkpoint is that unrealized one.

Both proofs read the finalized checkpoint of each receiver at the justified root of the sender.

`CallAt` names one call in a run of calls by one validator.

Along the accepted walk of a call, the call's balance source is on the chain of each parent.

That source is the observed checkpoint, and the stored root's recency carries from call to call.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models Serialization.Ssz SszType

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-! ## The finalized order of honest stores -/

/-- The finalized epoch of a reachable store is at least the epoch of the anchor state. -/
private theorem anchor_le_finalized {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store) :
    getCurrentEpoch anchorState ≤ store.finalizedCheckpoint.epoch := by
  by_cases low : store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · rw [(reached.finalized_eq_anchor_of_epoch_le low).1]
    exact UInt64.le_refl _
  · exact UInt64.le_of_lt (UInt64.not_le.mp low)

/-- The anchor state does not hash to the zero root, as no honest store holds a zero state root. -/
private theorem anchorState_hash_nonzero {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {last : ℕ}
    (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    {u : ValidatorIndex} (honest : u ∈ J) {n : ℕ} (inTime : (e.world n).time ≤ last) :
    hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0) := by
  intro zero
  have reached := e.reachable (fun x hx => (start x hx).symm ▸ Store.Reachable.anchor anchored)
    n u honest
  rw [reached.anchorState_root, Except.ok.injEq] at zero
  exact e.anchor_stateRoot_nonzero anchored start nonzero honest inTime zero

/-- A block of an honest store reaches each up-to-date honest receiver a delay later.

The sender's read at the block must give the finalized checkpoint of the receiver.

The receiver then holds the block with the sender's state for it.

Honest stores must agree on their blocks, and hold no state of a block with a zero state root. -/
private theorem carrier_delivered {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ last)
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
  have finalizedKnown : ∃ finalizedBlock,
      ((e.world k).state w).blocks[((e.world k).state w).finalizedCheckpoint.root]? =
        some finalizedBlock := by
    have contains : ((e.world k).state w).blocks.contains
        ((e.world k).state w).finalizedCheckpoint.root := by
      rcases reachedW.checkpoints_known sound (UInt64.le_of_eq anchorSlot) positive window
          (checkpoint := ((e.world k).state w).finalizedCheckpoint) (by simp) with
        ⟨-, -, held⟩ | ⟨-, held⟩ | zero
      · exact held
      · exact held
      · exact absurd zero (anchorState_hash_nonzero anchored start nonzero receiver bounded)
    rw [Std.TreeMap.contains_eq_isSome_getElem?] at contains
    exact Option.isSome_iff_exists.mp contains
  rcases e.blocks_of_partiallySynchronous sync preGloas admitted anchored start sender receiver
      (by simpa using late) bounded upToDate finalizedKnown known final with
    ⟨held, -⟩ | ⟨a, ha, b, hb, i, j, hi, hj, _, ⟨r, left, right⟩, found⟩
  · -- The receiver's state for the block is the sender's.
    obtain ⟨post, postFound, -, -⟩ := reachedW.blockStatesFromParents held
    have same := e.blockStates_eq anchored sender receiver (start u sender) (start w receiver)
      (agree u sender w receiver m k mBound bounded) stored postFound
    subst post
    exact ⟨held, postFound⟩
  · obtain ⟨leftFound, rightFound, different⟩ := Store.findBlockCollision_held found
    exact absurd (agree a ha b hb i j hi hj r left right leftFound rightFound) different

/-- A delay after an event of an honest store, each up-to-date honest store has justified its epoch.

That epoch is the one of the finalized checkpoint of the sender at the event.

The finalized checkpoint of each receiver must be read at the justified root of each sender.

The sender's justified checkpoint comes from the anchor, from a held state, or from its pull-up.

The block of that state reaches the receiver, whose justified epoch is then at least as late. -/
private theorem finalizedOrder {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
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
    UInt64.lt_of_le_of_lt (anchor_le_finalized reachedW) (UInt64.lt_of_lt_of_le below finalLe)
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
    refine carrier_delivered sync positive window preGloas admitted anchored sound anchorSlot start
      nonzero agree sender receiver nBound late bounded upToDate known stored ?_
    rw [Store.getCheckpointBlock_trans preGloas read
      (UInt64.le_of_lt (UInt64.lt_of_lt_of_le below finalLe))]
    exact crossRead
  obtain ⟨currentU, currentUOk⟩ := (forward u sender n).exists_getCurrentSlot slots
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
    have genesisU := (e.clock_bounds u n).1
    have genesisW := (e.clock_bounds w k).1
    rw [start u sender] at genesisU
    rw [start w receiver] at genesisW
    have timeU := (e.clock_bounds u n).2.2
    have startW := (e.clock_bounds w k).2.1
    rw [start u sender] at timeU
    rw [start w receiver] at startW
    have timeW := upToDate.1
    have timeLe : ((e.world n).state u).timeMs ≤ ((e.world k).state w).timeMs := by
      apply UInt64.le_iff_toNat_le.mpr
      have := UInt64.le_iff_toNat_le.mp startW
      omega
    have slotLe : currentU ≤ currentW := by
      unfold Store.getCurrentSlot at currentUOk currentWOk
      rw [genesisU] at currentUOk
      rw [genesisW] at currentWOk
      exact computeSlotAtTimeMs_mono timeLe (mapError_ok_iff.mp currentUOk)
        (mapError_ok_iff.mp currentWOk)
    have epochLe : computeEpochAtSlot preset currentU ≤ computeEpochAtSlot preset currentW :=
      UInt64.le_iff_toNat_le.mpr (epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp slotLe))
    rw [same] at finalLe
    exact UInt64.le_trans finalLe ((forward w receiver k).justified_le_of_pulledUp sound positive
      slots currentWOk blockHeld stateHeld run (UInt64.lt_of_lt_of_le earlier epochLe))

/-! ## The observed start of a call -/

/-- A delay after an earlier call, each up-to-date honest store has justified the observed epoch.

That epoch is the one of the caller's unrealized justified checkpoint at the earlier call.

A later call must hold that checkpoint as the caller's justified checkpoint.

Each receiver must be in a later epoch than the earlier call.

The finalized checkpoint of each receiver must be read at the justified root of each sender.

That read at the later call moves to the block that gives the observed checkpoint.

It then moves back to the earlier call, which holds the block, and which delivers it. -/
private theorem observedOrder {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ last)
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
    (realized : ((e.world n).state u).justifiedCheckpoint =
      ((e.world m).state u).unrealizedJustifiedCheckpoint)
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
  have anchorLe := anchor_le_finalized reachedW
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
    have same := e.blockStates_eq anchored sender sender (start u sender) (start u sender)
      (agree u sender u sender m n mBound nBound) stored storedN
    subst post
    have readN := (reachedN.getCheckpointBlock_of_blockState sound aligned positive window
      storedN member later).resolve_right notZero
    have finalN : ((e.world n).state u).getCheckpointBlock root
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root := by
      rw [Store.getCheckpointBlock_trans preGloas readN.1 (UInt64.le_of_lt below)]
      exact crossRead
    -- The read moves back to the earlier call, which delivers the block.
    have boundaryOf := finalN
    unfold Store.getCheckpointBlock at boundaryOf
    simp only [bind_ok_iff] at boundaryOf
    obtain ⟨boundary, boundaryOk, -⟩ := boundaryOf
    have boundaryOk := mapError_ok_iff.mp boundaryOk
    exact carrier_delivered sync positive window preGloas admitted anchored sound anchorSlot start
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

/-! ## The balance source of a walked member -/

/-- One call of the rule in a run of calls by one validator. -/
def CallAt (u : ValidatorIndex) (events : List ℕ) (first : FastConfirmationStore)
    (i n : ℕ) (fcr after : FastConfirmationStore) : Prop :=
  events[i]? = some n ∧
    ((events.take i).map fun k => (e.world k).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) first = .ok fcr ∧
    ((e.world n).state u).onFastConfirmation config fcr = .ok after

/-- The unrealized justification read of a block is its stored entry. -/
private theorem unrealizedJustification_found {store : Store preset fork} {root : Root}
    {checkpoint : Checkpoint} (read : store.unrealizedJustification root = .ok checkpoint) :
    store.unrealizedJustifications[root]? = some checkpoint := by
  unfold Store.unrealizedJustification at read
  split at read
  · rename_i stored found
    simp only [pure, Except.pure, Except.ok.injEq] at read
    rw [found, read]
  · simp [throw, throwThe, MonadExceptOf.throw] at read

/-- A stored unrealized justification is at most the store's unrealized justified checkpoint.

An entry of the anchor epoch is at most the finalized epoch, which is at most the justified one.

Any other entry is the pull-up of a held state, which the store has adopted.

The anchor state must keep the invariant of the state transition. -/
private theorem unrealizedJustification_epoch_le {store : Store preset fork}
    (sound : Invariant anchorState)
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (slots : 0 < config.SLOT_DURATION_MS)
    {root : Root} {checkpoint : Checkpoint}
    (found : store.unrealizedJustifications[root]? = some checkpoint) :
    checkpoint.epoch ≤ store.unrealizedJustifiedCheckpoint.epoch := by
  have reachable := forward.reachable
  rcases reachable.unrealizedJustification_origin found with
    ⟨epochEq, -⟩ | ⟨state, pulled, held, run, rfl⟩
  · rw [epochEq]
    exact UInt64.le_trans (anchor_le_finalized reachable) (UInt64.le_trans
      (reachable.finalized_le_justified sound)
      (Store.Reachable.justified_epoch_le_unrealized sound reachable))
  · obtain ⟨_, known⟩ := reachable.known_of_blockState held
    exact forward.pulledUp_le_unrealized sound positive slots known held run

/-- A voting source of a store is at most its unrealized justified checkpoint.

The source is a stored unrealized justification, or the justified checkpoint of a held state.

The anchor state must keep the invariant of the state transition. -/
private theorem votingSource_epoch_le {store : Store preset fork}
    (sound : Invariant anchorState)
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (slots : 0 < config.SLOT_DURATION_MS)
    {root : Root} {source : Checkpoint} (voted : store.getVotingSource config root = .ok source) :
    source.epoch ≤ store.unrealizedJustifiedCheckpoint.epoch := by
  unfold Store.getVotingSource at voted
  simp only [bind_ok_iff] at voted
  obtain ⟨_, -, _, -, voted⟩ := voted
  split at voted
  · split at voted
    · rename_i checkpoint found
      cases voted
      exact unrealizedJustification_epoch_le sound forward positive slots found
    · cases voted
  · split at voted
    · rename_i state held
      cases voted
      exact UInt64.le_trans (forward.reachable.justified_le_of_blockState sound held)
        (Store.Reachable.justified_epoch_le_unrealized sound forward.reachable)
    · cases voted

/-- An honest store's unrealized justified epoch is at least the anchor store's. -/
private theorem anchor_unrealized_le {anchor : Store preset fork}
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (honest : u ∈ J) (k : ℕ) :
    anchor.unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state u).unrealizedJustifiedCheckpoint.epoch := by
  have later := e.unrealizedJustified_epoch_le_of_le u (Nat.zero_le k)
  simpa [Execution.world_zero, World.initial, start u honest] using later

/-- The start of an epoch no later than a slot's epoch is no later than the slot. -/
private theorem start_le_slot {epoch : Epoch} {boundary slot : Slot}
    (startOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (le : epoch.toNat ≤ (computeEpochAtSlot preset slot).toNat) : boundary ≤ slot := by
  have value := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
  rw [computeEpochAtSlot, UInt64.toNat_div] at le
  have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat le
  have := Nat.div_mul_le_self slot.toNat preset.SLOTS_PER_EPOCH.toNat
  exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- A checkpoint read at an ancestor in the checkpoint's epoch or later holds at a descendant. -/
private theorem checkpointBlock_of_ancestor {store : Store preset fork}
    (preGloas : fork < .glamsterdam) {root above checkpoint : Root}
    {aboveBlock : BeaconBlock preset fork} (aboveFound : store.blocks[above]? = some aboveBlock)
    (descends : store.isAncestor ⟨root, .pending⟩ ⟨above, .pending⟩ = .ok true) {epoch : Epoch}
    (le : epoch.toNat ≤ (computeEpochAtSlot preset aboveBlock.slot).toNat)
    (read : store.getCheckpointBlock above epoch = .ok checkpoint) :
    store.getCheckpointBlock root epoch = .ok checkpoint := by
  obtain ⟨boundary, -, boundaryOk, -, -, -⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read
  exact Store.getCheckpointBlock_of_isAncestor preGloas aboveFound descends boundaryOk
    (start_le_slot boundaryOk le) read

/-- A checkpoint read names a held block in the checkpoint's epoch or before.

That block reads itself as the checkpoint block of the epoch. -/
private theorem read_facts {store : Store preset fork} (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {root checkpoint : Root} {epoch : Epoch}
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    ∃ block : BeaconBlock preset fork, store.blocks[checkpoint]? = some block ∧
      (computeEpochAtSlot preset block.slot).toNat ≤ epoch.toNat ∧
      store.getCheckpointBlock checkpoint epoch = .ok checkpoint := by
  obtain ⟨boundary, block, boundaryOk, found, le, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas read
  have epochEq := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) boundaryOk
  refine ⟨block, found, ?_, ?_⟩
  · rw [← epochEq]
    exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp le)
  · rw [← Store.getCheckpointBlock_trans preGloas read (UInt64.le_refl _)]
    exact read

/-- A passed chain-safety test reads the observed checkpoint on the confirmed root. -/
private theorem chainSafe_read {store : Store preset fork} {fcr : FastConfirmationStore}
    {head root : Root} (safe : store.isConfirmedChainSafe config fcr head root = .ok true) :
    store.getCheckpointBlock root fcr.currentEpochObservedJustifiedCheckpoint.epoch =
      .ok fcr.currentEpochObservedJustifiedCheckpoint.root := by
  unfold Store.isConfirmedChainSafe at safe
  rw [bind_ok_iff] at safe
  obtain ⟨checkpoint, checkpointOk, rest⟩ := safe
  split at rest
  · simp [pure, Except.pure] at rest
  · rename_i same
    simp only [ne_eq, Decidable.not_not] at same
    obtain ⟨block, blockOk, rfl⟩ := Store.getCheckpointForBlock_eq_ok_iff.mp checkpointOk
    rw [same]
    exact blockOk

/-- The store's epoch is the epoch of its slot. -/
private theorem epoch_eq {store : Store preset fork} {slot : Slot} {epoch : Epoch}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch) :
    epoch = computeEpochAtSlot preset slot := by
  simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
    using epochOk.symm

/-- The start test of a slot is its remainder by the epoch length. -/
private theorem isStart_eq (slot : Slot) :
    isStartSlotAtEpoch preset slot =
      .ok (decide (slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0)) := by
  have rounded := (computeStartSlotAtEpoch_ok_iff.mp
    (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot)).2
  rw [computeEpochAtSlot, UInt64.toNat_div] at rounded
  have below := Nat.div_mul_le_self slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have le : slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH ≤ slot :=
    UInt64.le_iff_toNat_le.mpr (by omega)
  have sub := UInt64.toNat_sub_of_le _ _ le
  have modNat := Nat.mod_add_div slot.toNat preset.SLOTS_PER_EPOCH.toNat
  simp only [isStartSlotAtEpoch, computeSlotsSinceEpochStart,
    computeStartSlotAtEpoch_computeEpochAtSlot, Except.mapError, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Nat.mul_comm] at rounded
  constructor
  · intro zero
    have := congrArg UInt64.toNat zero
    rw [sub, UInt64.toNat_zero] at this
    omega
  · intro zero
    apply UInt64.toNat_inj.mp
    rw [sub, UInt64.toNat_zero]
    omega

/-- A block epoch read names a held block. -/
private theorem found_of_blockEpoch {store : Store preset fork} {root : Root} {epoch : Epoch}
    (read : store.getBlockEpoch root = .ok epoch) :
    ∃ block : BeaconBlock preset fork, store.blocks[root]? = some block ∧
      computeEpochAtSlot preset block.slot = epoch := by
  unfold Store.getBlockEpoch at read
  obtain ⟨block, found, eq⟩ := bind_ok_iff.mp read
  simp only [pure, Except.pure, Except.ok.injEq] at eq
  exact ⟨block, Store.block_ok_iff.mp found, eq⟩

/-- A held block has an epoch. -/
private theorem blockEpoch_of_found {store : Store preset fork} {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    ∃ epoch, store.getBlockEpoch root = .ok epoch :=
  ⟨computeEpochAtSlot preset block.slot, by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr found, bind, Except.bind, pure,
      Except.pure]⟩

/-- When a root of the current epoch is one-confirmed, the current slot does not start the epoch.

At that slot the root would be a block at the current slot, which is never one-confirmed. -/
private theorem not_start_of_confirmed {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot)
    {root head : Root} {source : BeaconState preset fork}
    (rootEpochOk : store.getBlockEpoch root = .ok (computeEpochAtSlot preset slot))
    (confirmed : store.isOneConfirmed config head source (store.tallyVotes source) root =
      .ok true) :
    isStartSlotAtEpoch preset slot = .ok false := by
  obtain ⟨block, held, epochEq⟩ := found_of_blockEpoch rootEpochOk
  obtain ⟨current, currentOk, blocksLe, -⟩ := forward.slots_le_current slots anchorSlot
  obtain rfl : current = slot := Except.ok.inj (currentOk.symm.trans slotOk)
  rw [isStart_eq, Except.ok.injEq, decide_eq_false_iff_not]
  intro zero
  apply Store.not_isOneConfirmed_of_slot_eq_current forward currentOk held ?_ confirmed
  apply UInt64.toNat_inj.mp
  have le := UInt64.le_iff_toNat_le.mp (blocksLe root block held)
  have epochNat := congrArg UInt64.toNat epochEq
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
  have slotDiv := Nat.mod_add_div current.toNat preset.SLOTS_PER_EPOCH.toNat
  have blockDiv := Nat.mod_add_div block.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [← epochNat] at slotDiv
  omega

/-- A held block of a forward-reachable store is in the store's epoch or before. -/
private theorem epoch_le_current {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot) {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    (computeEpochAtSlot preset block.slot).toNat ≤ (computeEpochAtSlot preset slot).toNat := by
  obtain ⟨current, currentOk, blocksLe, -⟩ := forward.slots_le_current slots anchorSlot
  obtain rfl : current = slot := Except.ok.inj (currentOk.symm.trans slotOk)
  exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp (blocksLe root block found))

/-- The recency facts of a root for a call of epoch `E` with observed checkpoint `c`.

They apply when the root's epoch is at least `E - 1`.

The root's epoch is then at most one past the store's unrealized justified epoch.

The checkpoint is at most two epochs before `E`, and the root reads it on its chain. -/
private def Recent (store : Store preset fork) (E : ℕ) (c : Checkpoint) (r : Root) : Prop :=
  ∀ be : Epoch, store.getBlockEpoch r = .ok be → E ≤ be.toNat + 1 →
    be.toNat ≤ store.unrealizedJustifiedCheckpoint.epoch.toNat + 1 ∧
    E ≤ c.epoch.toNat + 2 ∧ store.getCheckpointBlock r c.epoch = .ok c.root

/-- A checked walk's start is in epoch `E - 1` or later, so its recency facts apply. -/
private theorem checked_start {store : Store preset fork} {E : ℕ} {c : Checkpoint} {slot : Slot}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (hE : (computeEpochAtSlot preset slot).toNat = E)
    {fcr : FastConfirmationStore} {head start root : Root}
    (startRec : Recent store E c start)
    (checked : store.FastConfirmationChecked config fcr head start root) :
    ∃ startBlock : BeaconBlock preset fork, store.blocks[start]? = some startBlock ∧
      E ≤ (computeEpochAtSlot preset startBlock.slot).toNat + 1 ∧
      E ≤ c.epoch.toNat + 2 ∧ store.getCheckpointBlock start c.epoch = .ok c.root := by
  obtain ⟨epoch, slot', rootEpoch, startEpoch, epochOk, slotOk', -, startOk, recent, -⟩ :=
    checked
  obtain rfl : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
  obtain rfl := epoch_eq slotOk epochOk
  obtain ⟨startBlock, startFound, rfl⟩ := found_of_blockEpoch startOk
  obtain ⟨-, R, T⟩ := startRec _ startOk (by omega)
  exact ⟨startBlock, startFound, by omega, R, T⟩

/-- Each walked member's parent is the start or a root of the walk, so it is above the start. -/
private theorem parent_above {store : Store preset fork} {head start root member : Root}
    {chain later : List Root} {startBlock block : BeaconBlock preset fork}
    (startFound : store.blocks[start]? = some startBlock)
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    (mem : member ∈ chain ++ [root]) (blockOk : store.block member = .ok block) :
    store.isAncestor ⟨block.parentRoot, .pending⟩ ⟨start, .pending⟩ = .ok true := by
  have mem' : member ∈ chain ++ root :: later := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
    tauto
  obtain ⟨older, newer, split⟩ := List.append_of_mem mem'
  rw [split] at walked
  rw [(Store.parentRoot_of_getAncestorRoots walked blockOk).1]
  cases last : older.getLast? with
  | none => exact Store.isAncestor_self (node := ⟨start, .pending⟩) startFound
  | some x =>
    exact Store.isAncestor_terminal_of_getAncestorRoots walked
      (List.mem_append_left _ (List.mem_of_getLast? last))

/-- The source of a call is on the chain of each walked member's parent.

It holds at one walk, from the recency facts of the walk's start. -/
private theorem parent_source {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {E : ℕ} {c : Checkpoint} {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot)
    (hE : (computeEpochAtSlot preset slot).toNat = E) (below : c.epoch.toNat + 1 ≤ E)
    {fcr : FastConfirmationStore} {head start root : Root} {chain later : List Root}
    (startRec : Recent store E c start)
    (checked : store.FastConfirmationChecked config fcr head start root)
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    {member : Root} (mem : member ∈ chain ++ [root]) {block parent : BeaconBlock preset fork}
    (blockOk : store.block member = .ok block)
    (parentOk : store.block block.parentRoot = .ok parent) :
    SourceOnParentChain store c block.parentRoot parent := by
  obtain ⟨startBlock, startFound, recent, R, T⟩ := checked_start slotOk hE startRec checked
  have descends := parent_above startFound walked mem blockOk
  have parentFound := Store.block_ok_iff.mp parentOk
  obtain ⟨found, foundAt, le⟩ := Store.slot_le_of_isAncestor startFound descends
  obtain rfl : found = parent := Option.some.inj (foundAt.symm.trans parentFound)
  have above := epoch_le_of_slot_le (preset := preset) _ _ (UInt64.le_iff_toNat_le.mp le)
  have current := epoch_le_current forward slots anchorSlot slotOk parentFound
  refine ⟨by omega, by omega, ?_⟩
  exact checkpointBlock_of_ancestor preGloas startFound descends (by omega) T

/-- A checked walk's confirmed root keeps the recency facts of its start.

A root of the current epoch is not at the epoch's first slot, so the call kept a realized check.

That check reads the root's unrealized justification, which the store's bounds.

An older root reads a voting source two epochs back at most, which the store's also bounds. -/
private theorem root_recent {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {E : ℕ} {c : Checkpoint} {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot)
    (hE : (computeEpochAtSlot preset slot).toNat = E) (below : c.epoch.toNat + 1 ≤ E)
    {fcr : FastConfirmationStore} {head start root : Root} {chain later : List Root}
    {source : BeaconState preset fork}
    (startRec : Recent store E c start)
    (checked : store.FastConfirmationChecked config fcr head start root)
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    (confirmed : store.isOneConfirmed config head source (store.tallyVotes source) root =
      .ok true) :
    Recent store E c root := by
  obtain ⟨startBlock, startFound, recent, R, T⟩ := checked_start slotOk hE startRec checked
  intro be beOk _
  obtain ⟨epoch, slot', rootEpoch, startEpoch, epochOk, slotOk', rootOk, -, -, branches⟩ :=
    checked
  obtain rfl : slot = slot' := Except.ok.inj (slotOk.symm.trans slotOk')
  obtain rfl := epoch_eq slotOk epochOk
  obtain rfl : be = rootEpoch := Except.ok.inj (beOk.symm.trans rootOk)
  have descends := Store.isAncestor_terminal_of_getAncestorRoots (member := root) walked (by simp)
  refine ⟨?_, R, checkpointBlock_of_ancestor preGloas startFound descends (by omega) T⟩
  by_cases same : be = computeEpochAtSlot preset slot
  · have inside := not_start_of_confirmed forward slots anchorSlot slotOk (same ▸ rootOk)
      confirmed
    rcases branches with ⟨-, different, -⟩ | ⟨nonStart, -, -⟩
    · exact absurd same different
    · obtain ⟨j, jOk, jLe⟩ := nonStart inside
      have := UInt64.le_iff_toNat_le.mp (unrealizedJustification_epoch_le sound forward positive
        slots (unrealizedJustification_found jOk))
      rw [same]
      omega
  · obtain ⟨rootBlock, rootFound, rfl⟩ := found_of_blockEpoch rootOk
    have current := epoch_le_current forward slots anchorSlot slotOk rootFound
    have voting : ∃ voteSource : Checkpoint, ∃ r,
        store.getVotingSource config r = .ok voteSource ∧
        (computeEpochAtSlot preset slot).toNat ≤ voteSource.epoch.toNat + 2 := by
      rcases branches with ⟨-, -, ⟨voteSource, voteOk, voteLe, -⟩, -⟩ | ⟨-, -, older⟩
      · exact ⟨voteSource, _, voteOk, voteLe⟩
      · obtain ⟨voteSource, voteOk, voteLe⟩ := (older same).1
        exact ⟨voteSource, _, voteOk, voteLe⟩
    obtain ⟨voteSource, r, voteOk, voteLe⟩ := voting
    have := UInt64.le_iff_toNat_le.mp (votingSource_epoch_le sound forward positive slots voteOk)
    have := UInt64.toNat_inj.not.mpr same
    omega

/-- A successful call returns a held block. -/
private theorem root_known {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0))
    {fcr after : FastConfirmationStore}
    (called : store.onFastConfirmation config fcr = .ok after) :
    ∃ epoch, store.getBlockEpoch after.confirmedRoot = .ok epoch := by
  have held (r : Root) (contains : store.blocks.contains r) :
      ∃ epoch, store.getBlockEpoch r = .ok epoch := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?] at contains
    obtain ⟨b, found⟩ := Option.isSome_iff_exists.mp contains
    exact blockEpoch_of_found found
  obtain ⟨head, slot, start, -, -, selected, result⟩ := Store.onFastConfirmation_checked called
  rcases result with same | ⟨-, checked, -⟩
  · rw [same]
    obtain ⟨base, baseCase, startCase⟩ := selected
    rcases startCase with ⟨rfl, _⟩ | ⟨rfl, _, ⟨block, _, found, _⟩, _⟩
    · rcases baseCase with ⟨rfl, ⟨_, blockEpoch, _, known, _⟩, _⟩ | ⟨rfl, _⟩
      · exact ⟨blockEpoch, known⟩
      · rcases reached.checkpoints_known sound (UInt64.le_of_eq anchorSlot) positive window
            (checkpoint := store.finalizedCheckpoint) (by simp) with
          ⟨-, -, contains⟩ | ⟨-, contains⟩ | zero
        · exact held _ contains
        · exact held _ contains
        · exact absurd zero nonzero
    · exact blockEpoch_of_found (Store.block_ok_iff.mp found)
  · obtain ⟨_, _, rootEpoch, _, _, _, known, _⟩ := checked
    exact ⟨rootEpoch, known⟩

/-- A held block's epoch is the same at a later event. -/
private theorem getBlockEpoch_of_le {u : ValidatorIndex} {n k : ℕ} (later : n ≤ k)
    {root : Root} {epoch : Epoch}
    (read : ((e.world n).state u).getBlockEpoch root = .ok epoch) :
    ((e.world k).state u).getBlockEpoch root = .ok epoch := by
  unfold Store.getBlockEpoch at read ⊢
  simp only [bind_ok_iff] at read
  obtain ⟨block, found, rest⟩ := read
  rw [Store.block_ok_iff.mpr (e.blocks_of_le later (Store.block_ok_iff.mp found))]
  exact rest

/-- A call after the first one has the call before it, whose result the call reads. -/
private theorem callAt_previous {u : ValidatorIndex} {events : List ℕ}
    {first : FastConfirmationStore} {j n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events first (j + 1) n fcr after) :
    ∃ m fcr', CallAt (e := e) u events first j m fcr' fcr := by
  obtain ⟨found, run, called⟩ := calls
  have lt : j < events.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
    omega
  refine ⟨events[j], ?_⟩
  rw [List.take_add_one, List.getElem?_eq_getElem lt, Option.toList_some, List.map_append,
    List.foldlM_append] at run
  obtain ⟨fcr', before, step⟩ := bind_ok_iff.mp run
  simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_ok_iff] at step
  obtain ⟨last, lastOk, eq⟩ := step
  simp only [pure, Except.pure, Except.ok.injEq] at eq
  subst eq
  exact ⟨fcr', List.getElem?_eq_getElem lt, before, lastOk⟩

/-- A successful call has a next slot. -/
private theorem next_exists {store : Store preset fork} {fcr after : FastConfirmationStore}
    (called : store.onFastConfirmation config fcr = .ok after) {slot : Slot}
    (slotOk : store.getCurrentSlot config = .ok slot) :
    ∃ next, addChecked slot 1 = .ok next := by
  unfold Store.onFastConfirmation at called
  simp only [bind_ok_iff] at called
  obtain ⟨head, -, updated, update, -⟩ := called
  unfold Store.updateFastConfirmationVariables at update
  simp only [bind_ok_iff] at update
  obtain ⟨slot', slotOk', next, nextOk, -⟩ := update
  obtain rfl : slot = slot' := Except.ok.inj (slotOk.symm.trans slotOk')
  exact ⟨next, mapError_ok_iff.mp nextOk⟩

/-- The slot after an epoch's first slot does not start an epoch. -/
private theorem next_not_start (long : 1 < preset.SLOTS_PER_EPOCH) {slot next : Slot}
    (nextOk : addChecked slot 1 = .ok next)
    (atStart : isStartSlotAtEpoch preset slot = .ok true) :
    isStartSlotAtEpoch preset next = .ok false := by
  rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq] at atStart
  have value := (addChecked_ok_iff.mp nextOk).2
  have P := UInt64.lt_iff_toNat_lt.mp long
  simp only [UInt64.toNat_one] at value P
  have one : (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 1 := by
    rw [Nat.add_mod, atStart, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt P]
  rw [isStart_eq, Except.ok.injEq, decide_eq_false_iff_not, value, one]
  omega

/-- The premises of the run of calls, bundled once. -/
private structure CallsCtx (anchor : Store preset fork) (u : ValidatorIndex) (events : List ℕ)
    (firstSlot : Slot) (limit : ℕ) : Prop where
  anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor
  sound : Invariant anchorState
  anchorSlot : anchorBlock.slot = anchorState.slot
  anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true
  start : ∀ w ∈ J, e.start w = anchor
  slots : 0 < config.SLOT_DURATION_MS
  positive : 0 < preset.SLOTS_PER_EPOCH.toNat
  long : 1 < preset.SLOTS_PER_EPOCH
  preGloas : fork < .glamsterdam
  window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  roots : HeldBlockStateRootsNonzero (e := e) limit
  absent : AnchorParentAbsent (e := e) limit
  caller : u ∈ J
  anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot
  atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
    ((e.world n).state u).getCurrentSlot config = .ok slot ∧
    slot.toNat = firstSlot.toNat + i ∧
    computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
    (e.world n).time = begin.toNat

section Calls

variable {anchor : Store preset fork} {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
  {limit : ℕ}

/-- The caller's stores are forward reachable. -/
private theorem CallsCtx.forward (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    (n : ℕ) : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u) :=
  e.forwardReachable
    (fun x hx => (ctx.start x hx).symm ▸ Store.ForwardReachable.anchor ctx.anchored) n u
    ctx.caller

/-- A call's slot and time. -/
private theorem call_slot (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {i n : ℕ}
    (found : events[i]? = some n) :
    ∃ slot, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      (e.world n).time =
        genesisTimeMs.toNat + (firstSlot.toNat + i) * config.SLOT_DURATION_MS.toNat := by
  obtain ⟨slot, begin, slotOk, slotNat, beginOk, timeEq⟩ := ctx.atSlots i n found
  obtain ⟨start, startOk, value, -⟩ := exists_timeAtSlotMs_of_le (UInt64.le_refl slot) beginOk
  rw [beginOk, Except.ok.injEq] at startOk
  subst startOk
  exact ⟨slot, slotOk, slotNat, by rw [timeEq, value, slotNat]⟩

/-- Earlier calls are at earlier events and times. -/
private theorem call_order (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    {j i m n : ℕ} (fm : events[j]? = some m) (fn : events[i]? = some n) (lt : j < i) :
    m < n ∧ (e.world m).time < (e.world n).time := by
  obtain ⟨-, -, -, tm⟩ := call_slot ctx fm
  obtain ⟨-, -, -, tn⟩ := call_slot ctx fn
  have D := UInt64.lt_iff_toNat_lt.mp ctx.slots
  simp only [UInt64.toNat_zero] at D
  have : (firstSlot.toNat + j) * config.SLOT_DURATION_MS.toNat <
      (firstSlot.toNat + i) * config.SLOT_DURATION_MS.toNat :=
    Nat.mul_lt_mul_of_pos_right (by omega) D
  have timeLt : (e.world m).time < (e.world n).time := by omega
  refine ⟨?_, timeLt⟩
  by_contra h
  have back := e.monotone_time (Nat.le_of_not_gt h)
  dsimp only at back
  omega

/-- The first call reads the anchor's fast confirmation store.

Its observed checkpoint is the anchor's finalized one. -/
private theorem call_zero (long : 1 < preset.SLOTS_PER_EPOCH) {n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) 0 n fcr after) :
    fcr = getFastConfirmationStore anchor ∧
      after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint := by
  obtain ⟨-, run, called⟩ := calls
  simp only [List.take_zero, List.map_nil, List.foldlM_nil, pure, Except.pure,
    Except.ok.injEq] at run
  subst run
  refine ⟨rfl, ?_⟩
  obtain ⟨slot, slotOk, -, keepPrev, atStart, notStart⟩ :=
    Store.onFastConfirmation_checkpoints called
  by_cases zero : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0
  · have st : isStartSlotAtEpoch preset slot = .ok true := by
      rw [isStart_eq]
      simp [zero]
    obtain ⟨next, nextOk⟩ := next_exists called slotOk
    rw [(atStart st).1, keepPrev next nextOk (next_not_start long nextOk st)]
    rfl
  · have st : isStartSlotAtEpoch preset slot = .ok false := by
      rw [isStart_eq]
      simp [zero]
    rw [(notStart st).1]
    rfl

/-- A later call reads the call before it.

At an epoch's first slot, its observed checkpoint is the earlier call's unrealized justified one.

At any other slot, it keeps the observed checkpoint of the earlier call. -/
private theorem call_succ (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {j n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) (j + 1) n fcr after) :
    ∃ m fcr', CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr ∧
      m < n ∧ (e.world m).time < (e.world n).time ∧
      ∃ slot, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
        slot.toNat = firstSlot.toNat + (j + 1) ∧
        ((isStartSlotAtEpoch preset slot = .ok true ∧
            after.currentEpochObservedJustifiedCheckpoint =
              ((e.world m).state u).unrealizedJustifiedCheckpoint) ∨
          (isStartSlotAtEpoch preset slot = .ok false ∧
            after.currentEpochObservedJustifiedCheckpoint =
              fcr.currentEpochObservedJustifiedCheckpoint)) := by
  obtain ⟨m, fcr', prev⟩ := callAt_previous calls
  obtain ⟨mn, tlt⟩ := call_order ctx prev.1 calls.1 (by omega)
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  obtain ⟨slotM, slotMOk, slotMNat, -⟩ := call_slot ctx prev.1
  obtain ⟨sN, sNOk, -, keepPrev, atStart, notStart⟩ :=
    Store.onFastConfirmation_checkpoints calls.2.2
  obtain rfl : slotN = sN := Except.ok.inj (slotNOk.symm.trans sNOk)
  obtain ⟨sM, sMOk, toPrev, -, -, -⟩ := Store.onFastConfirmation_checkpoints prev.2.2
  obtain rfl : slotM = sM := Except.ok.inj (slotMOk.symm.trans sMOk)
  refine ⟨m, fcr', prev, mn, tlt, slotN, slotNOk, slotNNat, ?_⟩
  by_cases zero : slotN.toNat % preset.SLOTS_PER_EPOCH.toNat = 0
  · have st : isStartSlotAtEpoch preset slotN = .ok true := by
      rw [isStart_eq]
      simp [zero]
    obtain ⟨next, nextOk⟩ := next_exists calls.2.2 slotNOk
    have step : addChecked slotM 1 = .ok slotN := addChecked_ok_iff.mpr ⟨by
      have := slotN.toNat_lt
      simp only [UInt64.toNat_one]
      omega, by simp only [UInt64.toNat_one]; omega⟩
    refine .inl ⟨st, ?_⟩
    rw [(atStart st).1, keepPrev next nextOk (next_not_start ctx.long nextOk st),
      toPrev slotN step st]
  · have st : isStartSlotAtEpoch preset slotN = .ok false := by
      rw [isStart_eq]
      simp [zero]
    exact .inr ⟨st, (notStart st).1⟩

/-- The anchor block's epoch is the anchor state's. -/
private theorem anchor_epoch {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot) {anchorRoot : Root}
    (hashed : hashTreeRoot anchorBlock = .ok anchorRoot) {be : Epoch}
    (read : store.getBlockEpoch anchorRoot = .ok be) : be = getCurrentEpoch anchorState := by
  obtain ⟨b, bFound, rfl⟩ := found_of_blockEpoch read
  obtain ⟨key, keyHash, aFound⟩ := reached.anchor_known
  obtain rfl : key = anchorRoot := Except.ok.inj (keyHash.symm.trans hashed)
  obtain rfl : b = anchorBlock := Option.some.inj (bFound.symm.trans aFound)
  rw [anchorSlot]
  rfl

/-- The anchor root has the recency facts against the anchor's finalized checkpoint.

They hold in any caller store by the limit. -/
private theorem anchor_recent (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {n : ℕ}
    (bound : (e.world n).time ≤ limit) (E : ℕ) :
    Recent ((e.world n).state u) E anchor.finalizedCheckpoint
      anchor.finalizedCheckpoint.root := by
  obtain ⟨anchorRoot, hashed, -, -, -, finEq, ujEq, -⟩ := getForkchoiceStore_anchor ctx.anchored
  have reached := (ctx.forward n).reachable
  have mono := anchor_unrealized_le ctx.start ctx.caller n
  rw [ujEq] at mono
  have mono := UInt64.le_iff_toNat_le.mp mono
  dsimp only at mono
  rw [finEq]
  intro be beOk rec
  obtain rfl := anchor_epoch reached ctx.anchorSlot hashed beOk
  obtain ⟨key, keyHash, aFound⟩ := reached.anchor_known
  obtain rfl : key = anchorRoot := Except.ok.inj (keyHash.symm.trans hashed)
  dsimp only
  exact ⟨by omega, by omega, reached.getCheckpointBlock_anchor ctx.anchorSlot
    ctx.anchorBoundary (ctx.absent u ctx.caller n bound) aFound hashed⟩

/-- A finalized start within one epoch of the call is the anchor root.

That is in the run's first epoch, where the observed checkpoint is the anchor's. -/
private theorem finalized_recent (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    {n : ℕ} (bound : (e.world n).time ≤ limit) {slot : Slot}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {E E0 : ℕ}
    (hE : (computeEpochAtSlot preset slot).toNat = E)
    (before : (getCurrentEpoch anchorState).toNat < E0) (first : E0 ≤ E)
    {c : Checkpoint} (cAnchor : E = E0 → c = anchor.finalizedCheckpoint) :
    Recent ((e.world n).state u) E c ((e.world n).state u).finalizedCheckpoint.root := by
  have forward := ctx.forward n
  have reached := forward.reachable
  have nonzero := anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller bound
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  obtain ⟨anchorRoot, hashed, -, -, -, finEq, -, -⟩ := getForkchoiceStore_anchor ctx.anchored
  intro be beOk rec
  by_cases lt : getCurrentEpoch anchorState <
      ((e.world n).state u).finalizedCheckpoint.epoch
  · exfalso
    have known := fun {root : Root} {st : BeaconState preset fork}
        (stFound : ((e.world n).state u).blockStates[root]? = some st) member =>
      reached.getCheckpointBlock_of_blockState ctx.sound (UInt64.le_of_eq ctx.anchorSlot)
        ctx.positive ctx.window stFound
        (checkpoint := ((e.world n).state u).finalizedCheckpoint) member lt
    have read : ∃ root, ((e.world n).state u).getCheckpointBlock root
        ((e.world n).state u).finalizedCheckpoint.epoch =
          .ok ((e.world n).state u).finalizedCheckpoint.root := by
      rcases reached.finalized_origins _ (Or.inl rfl) with ⟨root, -, same⟩ |
          ⟨root, st, stFound, same⟩ | ⟨root, st, pulled, stFound, pulledOk, same⟩
      · rw [same] at lt
        exact absurd lt (UInt64.lt_irrefl _)
      · rcases known stFound (.inl (by simp [same])) with ⟨r, -⟩ | zero
        · exact ⟨root, r⟩
        · exact absurd zero nonzero
      · rcases known stFound (.inr ⟨pulled, pulledOk, by simp [same]⟩) with ⟨r, -⟩ | zero
        · exact ⟨root, r⟩
        · exact absurd zero nonzero
    obtain ⟨root, r⟩ := read
    obtain ⟨b, bFound, bLe, -⟩ := read_facts ctx.preGloas ctx.positive r
    obtain ⟨b', bFound', rfl⟩ := found_of_blockEpoch beOk
    obtain rfl : b' = b := Option.some.inj (bFound'.symm.trans bFound)
    rcases forward.finalized_add_two_le_or_anchor ctx.sound ctx.slots epochOk with lag | lag
    · omega
    · exact UInt64.not_lt.mpr lag lt
  · have le := UInt64.not_lt.mp lt
    obtain ⟨-, hash⟩ := reached.finalized_eq_anchor_of_epoch_le le
    have rootEq : ((e.world n).state u).finalizedCheckpoint.root =
        anchor.finalizedCheckpoint.root := by
      rw [finEq]
      exact Except.ok.inj (hash.symm.trans hashed)
    rw [rootEq] at beOk ⊢
    have beEq := anchor_epoch reached ctx.anchorSlot hashed (by rw [finEq] at beOk; exact beOk)
    subst beEq
    rw [cAnchor (by omega)]
    exact anchor_recent ctx bound E _ beOk rec

/-- The facts carried from call `j` at event `m` to the next call.

The observed checkpoint is before the call's epoch, and is the anchor's in the run's first epoch.

The confirmed root has the recency facts. -/
private def Facts (anchor : Store preset fork) (u : ValidatorIndex) (f j m : ℕ)
    (after : FastConfirmationStore) : Prop :=
  after.currentEpochObservedJustifiedCheckpoint.epoch.toNat + 1 ≤
      (f + j) / preset.SLOTS_PER_EPOCH.toNat ∧
    ((f + j) / preset.SLOTS_PER_EPOCH.toNat = f / preset.SLOTS_PER_EPOCH.toNat →
      after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint) ∧
    Recent ((e.world m).state u) ((f + j) / preset.SLOTS_PER_EPOCH.toNat)
      after.currentEpochObservedJustifiedCheckpoint after.confirmedRoot

/-- One call: from the facts of the call before it, the facts of the call's observed checkpoint.

Every start that the call may select, kept, finalized or observed, has the recency facts. -/
private theorem start_recent (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {i n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (bound : (e.world n).time ≤ limit)
    (prev : ∀ j, i = j + 1 → ∀ m fcr',
      CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr →
      (e.world m).time ≤ limit → Facts (e := e) anchor u firstSlot.toNat j m fcr) :
    after.currentEpochObservedJustifiedCheckpoint.epoch.toNat + 1 ≤
        (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat ∧
      ((firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
          firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat →
        after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint) ∧
      ∀ (head : ForkChoiceNode) (slot : Slot) (start : Root),
        ((e.world n).state u).getHead config = .ok head →
        ((e.world n).state u).getCurrentSlot config = .ok slot →
        ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot start →
        Recent ((e.world n).state u) ((firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat)
          after.currentEpochObservedJustifiedCheckpoint start := by
  have forward := ctx.forward n
  have reached := forward.reachable
  obtain ⟨anchorRoot, hashed, -, -, -, finEq, -, -⟩ := getForkchoiceStore_anchor ctx.anchored
  have before := UInt64.lt_iff_toNat_lt.mp ctx.anchorEpochBefore
  simp only [computeEpochAtSlot, UInt64.toNat_div] at before
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  have hE : (computeEpochAtSlot preset slotN).toNat =
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div, slotNNat]
  have first : firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
  have rel : (after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint ∧
        fcr.confirmedRoot = anchor.finalizedCheckpoint.root) ∨
      ∃ j m fcr', i = j + 1 ∧
        CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr ∧ m < n ∧
        (e.world m).time ≤ limit ∧ Facts (e := e) anchor u firstSlot.toNat j m fcr ∧
        ((isStartSlotAtEpoch preset slotN = .ok true ∧
            after.currentEpochObservedJustifiedCheckpoint =
              ((e.world m).state u).unrealizedJustifiedCheckpoint ∧
            (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
              (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat + 1) ∨
          (isStartSlotAtEpoch preset slotN = .ok false ∧
            after.currentEpochObservedJustifiedCheckpoint =
              fcr.currentEpochObservedJustifiedCheckpoint ∧
            (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
              (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat)) := by
    cases i with
    | zero =>
      obtain ⟨rfl, cEq⟩ := call_zero ctx.long calls
      exact .inl ⟨cEq, rfl⟩
    | succ j =>
      obtain ⟨m, fcr', prevCall, mn, tlt, slot', slot'Ok, -, cases'⟩ := call_succ ctx calls
      obtain rfl : slotN = slot' := Except.ok.inj (slotNOk.symm.trans slot'Ok)
      have facts := prev j rfl m fcr' prevCall (by omega)
      refine .inr ⟨j, m, fcr', rfl, prevCall, mn, by omega, facts, ?_⟩
      have succ : (firstSlot.toNat + j + 1) / preset.SLOTS_PER_EPOCH.toNat =
          (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat +
            if (firstSlot.toNat + j + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 then 1 else 0 := by
        rw [Nat.succ_div]
        simp [Nat.dvd_iff_mod_eq_zero]
      rw [← Nat.add_assoc]
      rcases cases' with ⟨st, cEq⟩ | ⟨st, cEq⟩
      · have st' := st
        rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq, slotNNat, ← Nat.add_assoc] at st'
        simp only [st', ↓reduceIte] at succ
        exact .inl ⟨st, cEq, succ⟩
      · have st' := st
        rw [isStart_eq, Except.ok.injEq, decide_eq_false_iff_not, slotNNat,
          ← Nat.add_assoc] at st'
        simp only [st', ↓reduceIte, Nat.add_zero] at succ
        exact .inr ⟨st, cEq, succ⟩
  have cFacts : after.currentEpochObservedJustifiedCheckpoint.epoch.toNat + 1 ≤
        (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat ∧
      ((firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
          firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat →
        after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint) := by
    rcases rel with ⟨cEq, -⟩ |
        ⟨j, m, fcr', rfl, prevCall, mn, mb, ⟨cb, ca, -⟩, ⟨-, cEq, eEq⟩ | ⟨-, cEq, eEq⟩⟩
    · rw [cEq, finEq]
      exact ⟨by dsimp only; omega, fun _ => rfl⟩
    · obtain ⟨slotM, slotMOk, slotMNat, -⟩ := call_slot ctx prevCall.1
      have epochM : ((e.world m).state u).getCurrentStoreEpoch config =
          .ok (computeEpochAtSlot preset slotM) := by
        simp [Store.getCurrentStoreEpoch, slotMOk, bind, Except.bind, pure, Except.pure]
      have le := UInt64.le_iff_toNat_le.mp ((ctx.forward m).justified_epoch_le_current ctx.sound
        ctx.slots (UInt64.le_of_eq ctx.anchorSlot) epochM).2
      simp only [computeEpochAtSlot, UInt64.toNat_div, slotMNat] at le
      have firstJ : firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
          (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
      rw [cEq]
      exact ⟨by omega, fun h => absurd h (by omega)⟩
    · rw [cEq]
      exact ⟨by omega, fun h => ca (by omega)⟩
  refine ⟨cFacts.1, cFacts.2, ?_⟩
  intro head slot start headOk slotOk selects
  obtain rfl : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  rcases selects.eq_or with ⟨rfl, -, safe⟩ | rfl | ⟨rfl, atStart, -, ujHead⟩
  · -- The kept root: the previous call's facts, carried by the unrealized order and the blocks.
    rcases rel with ⟨cEq, rootEq⟩ | ⟨j, m, fcr', rfl, prevCall, mn, mb, ⟨-, -, recJ⟩, rest⟩
    · rw [rootEq, cEq]
      exact anchor_recent ctx bound _
    · intro be beOk rec
      have reachedM := (ctx.forward m).reachable
      obtain ⟨be', beOk'⟩ := root_known reachedM ctx.sound ctx.anchorSlot ctx.positive
        ctx.window (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller mb)
        prevCall.2.2
      obtain rfl : be = be' :=
        Except.ok.inj (beOk.symm.trans (getBlockEpoch_of_le (e := e) mn.le beOk'))
      have mono := UInt64.le_iff_toNat_le.mp (e.unrealizedJustified_epoch_le_of_le u mn.le)
      rcases rest with ⟨st, cEq, eEq⟩ | ⟨st, cEq, eEq⟩
      · obtain ⟨Q, -, -⟩ := recJ be beOk' (by omega)
        have T := chainSafe_read (safe st)
        rw [cEq] at T ⊢
        exact ⟨by omega, by omega, T⟩
      · obtain ⟨Q, R, T⟩ := recJ be beOk' (by omega)
        rw [cEq]
        exact ⟨by omega, by omega,
          Store.getCheckpointBlock_of_blocks (fun found => e.blocks_of_le mn.le found) T⟩
  · -- The finalized root.
    exact finalized_recent ctx bound slotNOk hE before first cFacts.2
  · -- The observed root: its checkpoint is the head's unrealized justification.
    rcases rel with ⟨cEq, -⟩ |
        ⟨j, m, fcr', rfl, prevCall, mn, mb, -, ⟨-, cEq, eEq⟩ | ⟨st, -, -⟩⟩
    · rw [cEq]
      exact anchor_recent ctx bound _
    · have reachedM := (ctx.forward m).reachable
      rcases reachedM.checkpoints_known ctx.sound (UInt64.le_of_eq ctx.anchorSlot) ctx.positive
          ctx.window (checkpoint := ((e.world m).state u).unrealizedJustifiedCheckpoint)
          (by simp) with ⟨epochEq, hash, -⟩ | ⟨lt, -⟩ | zero
      · have rootEq := Except.ok.inj (hash.symm.trans hashed)
        have same : after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint :=
          calc after.currentEpochObservedJustifiedCheckpoint
              = ⟨((e.world m).state u).unrealizedJustifiedCheckpoint.epoch,
                  ((e.world m).state u).unrealizedJustifiedCheckpoint.root⟩ := by rw [cEq]
            _ = anchor.finalizedCheckpoint := by rw [epochEq, rootEq, finEq]
        rw [same]
        exact anchor_recent ctx bound _
      · rw [← cEq] at lt
        intro be beOk rec
        rcases reached.getCheckpointBlock_of_unrealizedJustification ctx.sound
            (UInt64.le_of_eq ctx.anchorSlot) ctx.positive ctx.window
            (unrealizedJustification_found ujHead) lt with
          ⟨read, -⟩ | zero
        · obtain ⟨b, bFound, bLe, self⟩ := read_facts ctx.preGloas ctx.positive read
          obtain ⟨b', bFound', rfl⟩ := found_of_blockEpoch beOk
          obtain rfl : b' = b := Option.some.inj (bFound'.symm.trans bFound)
          have := UInt64.le_iff_toNat_le.mp (unrealizedJustification_epoch_le ctx.sound forward
            ctx.positive ctx.slots (unrealizedJustification_found ujHead))
          exact ⟨by omega, by omega, self⟩
        · exact absurd zero
            (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller bound)
      · exact absurd zero
          (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller mb)
    · exact absurd (atStart.symm.trans st) (by simp)

/-- One call keeps the facts. -/
private theorem facts_step (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {i n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (bound : (e.world n).time ≤ limit)
    (prev : ∀ j, i = j + 1 → ∀ m fcr',
      CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr →
      (e.world m).time ≤ limit → Facts (e := e) anchor u firstSlot.toNat j m fcr) :
    Facts (e := e) anchor u firstSlot.toNat i n after := by
  obtain ⟨cb, ca, startRec⟩ := start_recent ctx calls bound prev
  refine ⟨cb, ca, ?_⟩
  obtain ⟨head, slot, start, headOk, slotOk, selects, result⟩ :=
    Store.onFastConfirmation_checked calls.2.2
  have startFacts := startRec head slot start headOk slotOk selects
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  obtain rfl : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  have hE : (computeEpochAtSlot preset slotN).toNat =
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div, slotNNat]
  rcases result with same | ⟨-, checked, source, chain, later, -, walked, confirmed⟩
  · rw [same]
    exact startFacts
  · exact root_recent (ctx.forward n) ctx.sound ctx.positive ctx.slots
      (UInt64.le_of_eq ctx.anchorSlot) ctx.preGloas slotOk hE cb startFacts checked walked
      (confirmed _ (by simp))

/-- Every call by the limit has the facts, by induction over the calls. -/
private theorem facts (ctx : CallsCtx (e := e) anchor u events firstSlot limit) :
    ∀ i n fcr after,
      CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after →
      (e.world n).time ≤ limit → Facts (e := e) anchor u firstSlot.toNat i n after := by
  intro i
  induction i with
  | zero =>
    intro n fcr after calls bound
    exact facts_step ctx calls bound (fun j h => absurd h (by omega))
  | succ j ih =>
    intro n fcr after calls bound
    refine facts_step ctx calls bound (fun j' h m fcr' c b => ?_)
    obtain rfl : j' = j := by omega
    exact ih m fcr' fcr c b

end Calls

/-- The balance source of a call is on the chain of each walked member's parent.

The source is the call's observed checkpoint, and the walk is the accepted one.

The proof carries recency facts of the stored root from call to call. -/
private theorem sourceOnParentChain_of_walk {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (long : 1 < preset.SLOTS_PER_EPOCH) (preGloas : fork < .glamsterdam)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {limit : ℕ} (roots : HeldBlockStateRootsNonzero (e := e) limit)
    (absent : AnchorParentAbsent (e := e) limit)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {startRoot : Root} {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      startRoot)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root startRoot
      after.confirmedRoot)
    (walked : ((e.world n).state u).getAncestorRoots head.root startRoot =
      .ok (chain ++ after.confirmedRoot :: later)) :
    ∀ member ∈ chain ++ [after.confirmedRoot], ∀ (block parent : BeaconBlock preset fork),
      ((e.world n).state u).block member = .ok block →
      ((e.world n).state u).block block.parentRoot = .ok parent →
      SourceOnParentChain ((e.world n).state u) after.currentEpochObservedJustifiedCheckpoint
        block.parentRoot parent := by
  have ctx : CallsCtx (e := e) anchor u events firstSlot limit :=
    ⟨anchored, sound, anchorSlot, anchorBoundary, start, slots, positive, long, preGloas, window,
      roots, absent, caller, anchorEpochBefore, atSlots⟩
  obtain ⟨below, -, startRec⟩ := start_recent ctx calls nBound
    (fun j _ m fcr' c b => facts ctx j m fcr' fcr c b)
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  obtain rfl : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  have hE : (computeEpochAtSlot preset slotN).toNat =
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div, slotNNat]
  intro member mem block parent blockOk parentOk
  exact parent_source (ctx.forward n) slots (UInt64.le_of_eq anchorSlot) preGloas slotNOk hE below
    (startRec head slotN startRoot headOk slotNOk selects) checked walked mem blockOk parentOk

end EthLib.Consensus.Models.Network
