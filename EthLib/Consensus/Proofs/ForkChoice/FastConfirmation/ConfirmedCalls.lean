module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.RootViability

/-!
# The confirmed roots of the calls of one validator

A delay after an event of an honest store, each up-to-date honest store has justified its epoch.

That epoch is the one of the finalized checkpoint of the first store at the event.

The proof reads the finalized checkpoint of each receiver at the justified root of the sender.
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

end EthLib.Consensus.Models.Network
