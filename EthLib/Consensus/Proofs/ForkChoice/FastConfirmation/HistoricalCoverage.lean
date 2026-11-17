module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalAnchor
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport

/-!
# Honest heads over time from a historical anchor

The historical-anchor step keeps one honest head on the confirmed block at one time.

It assumes that every honest head descends from the block at each earlier time since the call.

An induction on time removes that assumption, so the block stays on every honest head chain.

Within two epochs after the parent, each step is the historical-anchor step.

Later, each step is the step of an honest duty epoch, which needs only the same-store finality.

Each step may instead name two honest stores that collide, or historical direct-safety evidence.
-/

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Coverage up to a time follows from one step at each time, or the step's alternative holds.

A step at a time may use the coverage at all earlier times. -/
private theorem cover_of_steps {root : Root} {first last : ℕ} {P : Prop}
    (step : ∀ T, first ≤ T → T ≤ last → HonestHeadsCover (e := e) root first T →
      ∀ a ∈ J, ∀ i hd, (e.world i).time = T →
        UpToDate config checks sources (e.world i).time ((e.world i).view a)
          ((e.world i).state a) →
        ((e.world i).state a).getHead config = .ok hd →
        ((e.world i).state a).isAncestor hd ⟨root, .pending⟩ = .ok true ∨ P) :
    HonestHeadsCover (e := e) root first (last + 1) ∨ P := by
  by_cases alternative : P
  · exact .inr alternative
  left
  -- Coverage up to each bound `T ≤ last + 1`, by induction on `T`.
  have all : ∀ T, T ≤ last + 1 → HonestHeadsCover (e := e) root first T := by
    intro T
    induction T with
    | zero => intro _ earlier low high; omega
    | succ T ih =>
      intro bound earlier low high a ha i hd atTime upToDate headOk
      by_cases before : earlier < T
      · exact ih (by omega) earlier low before a ha i hd atTime upToDate headOk
      have same : earlier = T := by omega
      subst same
      exact (step earlier low (by omega) (ih (by omega)) a ha i hd atTime upToDate
        headOk).resolve_right alternative
  exact all (last + 1) le_rfl

/-- A successful head read has a successful read of the filtered tree. -/
private theorem getFilteredNodeTree_of_getHead {store : Store preset fork}
    {head : ForkChoiceNode} (headOk : store.getHead config = .ok head) :
    ∃ nodes, store.getFilteredNodeTree config = .ok nodes := by
  unfold Store.getHead at headOk
  cases tree : store.getFilteredNodeTree config with
  | error error => simp [tree, bind, Except.bind] at headOk
  | ok nodes => exact ⟨nodes, rfl⟩

/-- A root that a receiver keeps viable is held with the caller's block, or the stores collide.

A viable root is in the filtered tree, or below the justified block of the tree. -/
private theorem known_or_collision_of_viable {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u w : ValidatorIndex} (caller : u ∈ J)
    (receiver : w ∈ J) {n k : ℕ} {root : Root} {block : BeaconBlock preset fork}
    {nodes : List ForkChoiceNode}
    (callerHeld : ((e.world n).state u).blocks[root]? = some block)
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (route : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    ((e.world k).state w).blocks[root]? = some block ∨
      ∃ r evidence, Store.findBlockCollision ((e.world n).state u) ((e.world k).state w) [r] =
        some evidence := by
  have reached := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored)
  -- In both cases some receiver node descends from the root.
  have descends : ∃ node, ((e.world k).state w).isAncestor node ⟨root, .pending⟩ = .ok true := by
    rcases route with below | inTree
    · exact ⟨_, below⟩
    obtain ⟨-, ⟨held, found⟩, -⟩ := Store.filterNodeTree_mem tree _ inTree
    exact ⟨_, Store.isAncestor_self (node := ⟨root, .pending⟩) found⟩
  obtain ⟨node, descends⟩ := descends
  rcases parent_read_or_collision (reached n u caller) (reached k w receiver) callerHeld
      descends with held | ⟨left, right, searched, -⟩
  · exact .inl held
  · exact .inr ⟨root, _, searched⟩

/-- A receiver that keeps the root viable relates it to each earlier finalized checkpoint.

The same-store family places each earlier finalized checkpoint below the justified block.

When the root is below the justified block, the checkpoint is below the root or above it.

Below the root, the root's walk reaches it; above the root, it descends from the root.

When the root is in the filtered tree, the viable-leaf argument of the duty step applies. -/
private theorem receiverFinality_of_viable {last : ℕ} {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) (absent : AnchorParentAbsent (e := e) last)
    (family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ last →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ last)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    {nodes : List ForkChoiceNode}
    (tree : ((e.world k).state w).getFilteredNodeTree config = .ok nodes)
    (route : ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    ReceiverFinalityCovers (e := e) w k root block := by
  have reached := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k w
    receiver
  have lower := reached.parentsBelow (UInt64.le_of_eq anchorSlot) (absent w receiver k bounded)
  rcases rootFinal_or_justified_covers anchored start anchorSlot preGloas family receiver bounded
      lower known tree route with below | final
  swap
  · intro k' earlier _
    exact .inl (final k' earlier)
  intro k' earlier _
  -- The walk from the justified block to the root's slot reaches the root.
  have walk := Store.getAncestor_of_isAncestor_of_lt preGloas known below
  -- The walk from the justified block to the boundary reaches the finalized block.
  have read := family w receiver k' k earlier bounded
  have split := read
  unfold Store.getCheckpointBlock at split
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at split
  obtain ⟨boundary, boundaryOk, reachedNode, boundaryWalk, reachedRoot⟩ := split
  have boundaryOk := mapError_ok_iff.mp boundaryOk
  by_cases early : boundary ≤ block.slot
  · -- The boundary is at or below the root: the root's walk to it meets the justified walk.
    left
    refine ⟨boundary, boundaryOk, early, ?_⟩
    have through := Store.getAncestor_trans early walk
    simp [Store.getCheckpointBlock, boundaryOk, ← through, boundaryWalk, reachedRoot,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  · -- The boundary is above the root: the finalized block descends from the root.
    right
    have late : block.slot ≤ boundary := UInt64.le_of_lt (UInt64.not_le.mp early)
    have pending := Store.getAncestor_pending_of_lt preGloas rfl boundaryWalk
    have same : reachedNode = ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩ := by
      obtain ⟨r, s⟩ := reachedNode
      simp only at reachedRoot pending
      rw [reachedRoot, pending]
    rw [same] at boundaryWalk
    have through := Store.getAncestor_trans late boundaryWalk
    rw [walk] at through
    exact Store.isAncestor_of_getAncestor through.symm

/-- An honest store's clock reads above a held block whose slot is positive.

The store's current slot is at or above the block's slot, so its previous slot is checked. -/
private theorem receiver_clock_reads {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) {w : ValidatorIndex} (receiver : w ∈ J) (k : ℕ)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block) (positive : 0 < block.slot.toNat) :
    ∃ current epoch last, ((e.world k).state w).getCurrentSlot config = .ok current ∧
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch ∧
      subChecked current 1 = .ok last ∧ block.slot ≤ current := by
  have forward := e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored) k w receiver
  obtain ⟨current, currentOk, blocks, _⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have above := blocks root block known
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have lastOk : subChecked current 1 = .ok (current - 1) := by
    apply subChecked_ok_iff.mpr
    have := UInt64.le_iff_toNat_le.mp above
    refine ⟨UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.toNat_one]; omega), ?_⟩
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr
      (by simp only [UInt64.toNat_one]; omega))]
  exact ⟨current, _, _, currentOk, epochOk, lastOk, above⟩

end EthLib.Consensus.Models.Network
