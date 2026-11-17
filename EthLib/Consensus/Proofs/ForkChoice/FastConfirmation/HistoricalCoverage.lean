module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalAnchor
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport
import EthLib.Consensus.Proofs.HonestAggregation

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

/-- An honest signer's duty for a target after the call's epoch lies between the call and a store.

The duty slot is in the target's epoch, so after the call's slot.

The signer signs at its deadline, before the next slot starts, so before the store's clock. -/
private theorem signer_duty_window {anchor : Store preset fork} {Δ : ℕ}
    {callSlot current : Slot} {callStart : UInt64} {callEpoch : Epoch} {w v : ValidatorIndex}
    {k i : ℕ} {m : Message preset fork} {data : AttestationData}
    (start : ∀ w ∈ J, e.start w = anchor) (fits : DelayFits fork config genesisTimeMs Δ)
    (callStartOk : computeTimeAtSlotMs config genesisTimeMs callSlot = .ok callStart)
    (callEpochEq : computeEpochAtSlot preset callSlot = callEpoch) (receiver : w ∈ J)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current) (honest : v ∈ J)
    (sent : m ∈ (e.world i).sent)
    (member : (v, data) ∈ statements config checks anchorState anchorBlock m)
    (later : callEpoch < data.target.epoch) (before : data.slot < current) :
    ∃ k', callStart.toNat ≤ (e.world k').time ∧ (e.world k').time < (e.world k).time ∧
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k').time ((e.world k').view v) ((e.world k').state v) data := by
  obtain ⟨k', -, duty⟩ := e.exists_maySign_of_signed sent member honest
  have dutyCopy := duty
  obtain ⟨_, -, deadline, genesis, -, made, -⟩ := dutyCopy
  obtain ⟨_, _, _, _, -, -, -, -, dataOk⟩ := made
  -- The duty slot is after the call's slot, as its epoch is later.
  have slotLt : callSlot < data.slot := by
    have epochLt := UInt64.lt_iff_toNat_lt.mp later
    rw [← callEpochEq, target_epoch_eq_of_getAttestationData dataOk] at epochLt
    simp only [computeEpochAtSlot, UInt64.toNat_div] at epochLt
    exact UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_div_lt_div epochLt)
  have deadlineCopy := deadline
  obtain ⟨dutyStart, due, dutyStartOk, -, timeEq⟩ := deadlineCopy
  obtain ⟨callStart', callStartOk', -, callLe⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt slotLt) dutyStartOk
  rw [callStartOk, Except.ok.injEq] at callStartOk'
  subst callStart'
  -- The store follows the signer's time of genesis, so its current slot starts by its clock.
  have senderGenesis := (e.clock_bounds v k').1
  have receiverGenesis := (e.clock_bounds w k).1
  rw [start v honest] at senderGenesis
  rw [start w receiver] at receiverGenesis
  obtain ⟨endTime, endOk, endLe⟩ := slotStart_le_clock
    (receiverGenesis.trans (senderGenesis.symm.trans genesis)) currentOk (UInt64.le_refl _)
  -- The deadline and the delay fall before the slot after the duty starts.
  have nextFits : data.slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := UInt64.lt_iff_toNat_lt.mp before
    have := current.toNat_lt
    simp only [UInt64.toNat_one]
    omega
  have nextOk := addChecked_of_lt nextFits
  have nextLe : data.slot + 1 ≤ current := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp before
    rw [(addChecked_ok_iff.mp nextOk).2]
    simp only [UInt64.toNat_one]
    omega)
  obtain ⟨following, followingOk, -, followingLe⟩ := exists_timeAtSlotMs_of_le nextLe endOk
  have bound := fits.before_boundary nextOk dutyStartOk followingOk deadline
  have followingNat := UInt64.le_iff_toNat_le.mp followingLe
  refine ⟨k', ?_, ?_, duty⟩
  · have := UInt64.le_iff_toNat_le.mp callLe
    omega
  · rw [← upToDate.1]
    omega

/-- A justified checkpoint after the call's epoch descends from the root, given an honest signer.

The signer voted for the checkpoint at its duty, after the call and before the store's time.

The coverage at that time puts the signer's head above the root.

The checkpoint is that head's block at the start of a later epoch, so it sits above the root.

The store agrees with the signer on that walk, as honest stores agree on blocks. -/
private theorem justified_descends_of_signer {anchor : Store preset fork} {Δ time T : ℕ}
    {root : Root} {callEpoch : Epoch} {callSlot : Slot} {callStart : UInt64}
    {u : ValidatorIndex} {n : ℕ} {block : BeaconBlock preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (caller : u ∈ J) (callerHeld : ((e.world n).state u).blocks[root]? = some block)
    (callerTime : (e.world n).time ≤ time)
    (callStartOk : computeTimeAtSlotMs config genesisTimeMs callSlot = .ok callStart)
    (timeEq : (e.world n).time = callStart.toNat) (blockLe : block.slot ≤ callSlot)
    (callEpochEq : computeEpochAtSlot preset callSlot = callEpoch)
    (covers : HonestHeadsCover (e := e) root (e.world n).time T) (high : T ≤ time)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {head : ForkChoiceNode} {current : Slot}
    (atTime : (e.world k).time = T)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (later : callEpoch < ((e.world k).state w).justifiedCheckpoint.epoch)
    (signer : ∃ v ∈ J, ∃ i, (e.world i).time ≤ (e.world k).time ∧ ∃ m ∈ (e.world i).sent,
      ∃ data, (v, data) ∈ statements config checks anchorState anchorBlock m ∧
        data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < current) :
    ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  obtain ⟨v, honest, i, -, m, sent, data, member, target, before⟩ := signer
  have laterData : callEpoch < data.target.epoch := target ▸ later
  obtain ⟨k', low', high', duty⟩ := signer_duty_window start fits callStartOk callEpochEq
    receiver upToDate currentOk honest sent member laterData before
  obtain ⟨_, -, -, -, current', honestData, -⟩ := duty
  have k'Bound : (e.world k').time ≤ time := by omega
  have reachedV := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k' v
    honest
  have reachedW := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k w
    receiver
  -- The store holds its justified block, which is the signer's target.
  obtain ⟨justifiedBlock, justifiedKnown⟩ : ∃ b, ((e.world k).state w).blocks[
      ((e.world k).state w).justifiedCheckpoint.root]? = some b := by
    have read := Store.isAncestor_getHead headOk
    unfold Store.isAncestor at read
    obtain ⟨b, ok, -⟩ := bind_ok_iff.mp read
    exact ⟨b, Store.block_ok_iff.mp ok⟩
  rw [← target] at justifiedKnown ⊢
  obtain ⟨signerHead, signerHeadOk, targetRead⟩ := honestData.target_read reachedV anchorSlot
    anchorBoundary (roots v honest k' k'Bound) reachedW justifiedKnown
  have supports := covers (e.world k').time (by omega) (by omega) v honest k' signerHead rfl
    current' signerHeadOk
  have pending : signerHead = ⟨signerHead.root, .pending⟩ := by
    have p := Store.getHead_pending preGloas signerHeadOk
    cases signerHead
    simp_all
  -- The signer holds the root, as the same block as the caller.
  have rootRead := supports
  unfold Store.isAncestor at rootRead
  obtain ⟨b', b'Ok, -⟩ := bind_ok_iff.mp rootRead
  have b'Found := Store.block_ok_iff.mp b'Ok
  have eqb : b' = block := agree v honest u caller k' n k'Bound callerTime root b' block b'Found
    callerHeld
  rw [eqb] at b'Found
  have rootWalk := Store.getAncestor_of_isAncestor_of_lt preGloas b'Found supports
  -- The target is the head's ancestor at the boundary of its epoch.
  have split := targetRead
  unfold Store.getCheckpointBlock at split
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at split
  obtain ⟨boundary, boundaryOk, reached, boundaryWalk, reachedRoot⟩ := split
  have boundaryOk := mapError_ok_iff.mp boundaryOk
  -- The boundary of a later epoch is above the call slot, hence above the block.
  have blockBelow : block.slot ≤ boundary := by
    have startNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have epochLt := UInt64.lt_iff_toNat_lt.mp laterData
    rw [← callEpochEq] at epochLt
    simp only [computeEpochAtSlot, UInt64.toNat_div] at epochLt
    have blockNat := UInt64.le_iff_toNat_le.mp blockLe
    have below : callSlot.toNat < callSlot.toNat / preset.SLOTS_PER_EPOCH.toNat *
        preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat :=
      Nat.lt_div_mul_add positive
    have above : callSlot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_EPOCH.toNat ≤
        data.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (Nat.succ_le_of_lt epochLt)
      rwa [Nat.succ_mul] at this
    apply UInt64.le_iff_toNat_le.mpr
    rw [startNat]
    omega
  have reachedPending := Store.getAncestor_pending_of_lt preGloas rfl boundaryWalk
  have reachedEq : reached = ⟨data.target.root, .pending⟩ := by
    obtain ⟨r, s⟩ := reached
    simp only at reachedRoot reachedPending
    rw [reachedRoot, reachedPending]
  rw [reachedEq] at boundaryWalk
  have through := Store.getAncestor_trans blockBelow boundaryWalk
  rw [pending] at rootWalk
  rw [rootWalk] at through
  -- The store agrees with the signer on the walk.
  have copied := Store.getAncestor_of_same_blocks reachedW
    (fun r b c hb hc => agree v honest w receiver k' k k'Bound (by omega) r b c hb hc)
    (reachedV.anchorSlot_le (UInt64.le_of_eq anchorSlot) b'Found) ⟨_, justifiedKnown⟩
    through.symm
  exact Store.isAncestor_of_getAncestor copied

/-- A comparable justified block and a kept leaf give the root's viability at one store. -/
private theorem route_of_split {store : Store preset fork} {root : Root}
    {nodes : List ForkChoiceNode}
    (consistent : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true ∨
      store.isAncestor ⟨root, .pending⟩ ⟨store.justifiedCheckpoint.root, .pending⟩ = .ok true)
    (leaf : store.isAncestor ⟨root, .pending⟩ ⟨store.justifiedCheckpoint.root, .pending⟩ =
        .ok true →
      root ≠ store.justifiedCheckpoint.root → (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes := by
  rcases consistent with below | above
  · exact .inl below
  by_cases same : root = store.justifiedCheckpoint.root
  · -- The root is the justified block itself, which is its own ancestor.
    left
    have read := above
    unfold Store.isAncestor at read
    obtain ⟨b, found, _⟩ := bind_ok_iff.mp read
    rw [same]
    exact Store.isAncestor_self (node := ⟨store.justifiedCheckpoint.root, .pending⟩)
      (Store.block_ok_iff.mp found)
  · exact .inr (leaf above same)

/-- The induction of the historical-anchor headline, with the root's viability given per time.

The viability at a time may read the coverage at every earlier time. -/
private theorem honestHeadsCover_core [DecidablePred (· ∈ J)] {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    (history : VoteCommitteeCommonHistory (e := e) time) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {block parent : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {boost maximum : Gwei}
    (headNode : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    {checkpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    (boostOk : computeProposerScore config source = .ok boost)
    (firstOk : addChecked parent.slot 1 = .ok first) (lastOk : subChecked slot 1 = .ok last)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head first
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei} (registry : source.RegistryWithinLimit)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head source root =
      .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head source root =
      .ok adversary)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (callerTime : (e.world n).time ≤ time) (sourceReads : SourceWindowReads (e := e) n time source)
    (drift : WindowMarginDrift (e := e) n time source shift)
    {finish : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first finish)
    {x : ValidatorIndex} (reference : x ∈ J) {m : ℕ} (referenceTime : time ≤ (e.world m).time)
    (referenceUpToDate : UpToDate config checks sources (e.world m).time ((e.world m).view x)
      ((e.world m).state x))
    {referenceSlot : Slot}
    (referenceSlotOk : ((e.world m).state x).getCurrentSlot config = .ok referenceSlot)
    (finishOk : subChecked referenceSlot 1 = .ok finish)
    {horizon : Epoch}
    (residual : ResidualFinalizedCheckpointCompatibility (e := e) horizon time)
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (headDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (near : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    (absent : AnchorParentAbsent (e := e) time)
    (parentCovers : HonestHeadsCover (e := e) block.parentRoot (e.world n).time (time + 1))
    (reads : HonestHeadReads (e := e) first (e.world n).time time)
    (viableAt : ∀ T, (e.world n).time ≤ T → T ≤ time →
      HonestHeadsCover (e := e) root (e.world n).time T →
      ∀ w ∈ J, ∀ k (nodes : List ForkChoiceNode) (hd : ForkChoiceNode), (e.world k).time = T →
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
      ((e.world k).state w).getHead config = .ok hd →
      ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
      ((e.world k).state w).isAncestor
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
        (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes)
    (exits : ReceiverWindowExits (e := e) source first (e.world n).time time)
    (late : LateDutyMajority (e := e) (computeEpochAtSlot preset parent.slot)
      (e.world n).time time) :
    HonestHeadsCover (e := e) root (e.world n).time (time + 1) ∨
      (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨
      HistoricalDirectSafetyEvidence (e := e) pre time := by
  classical
  -- The same-store finalized family, or the evidence alternative, once for the horizon.
  rcases e.finalizedFamily_or_historical_evidence anchored start sound anchorSlot anchorBoundary
      slots bounded roots absent parameters genesis pre heldEarly enough terminal caller callerTime
    with family | evidence
  swap
  · exact .inr (.inr evidence)
  have callerHeld : ((e.world n).state u).blocks[root]? = some block :=
    Store.block_ok_iff.mp blockOk
  -- The parent sits below the block, so the block's slot is positive.
  have callerLower := (e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored)
    n u caller).parentsBelow (UInt64.le_of_eq anchorSlot) (absent u caller n callerTime)
  have parentBelow := callerLower root block parent callerHeld (Store.block_ok_iff.mp parentOk)
  have blockPositive : 0 < block.slot.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp parentBelow
    omega
  have started : e.startTime ≤ (e.world n).time := by
    have le := e.monotone_time (Nat.zero_le n)
    simpa [Execution.world_zero, World.initial] using le
  -- The time induction; each step is the historical-anchor step or the duty-epoch step.
  have result := cover_of_steps (e := e) (root := root) (first := (e.world n).time) (last := time)
    (P := (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨
      HistoricalDirectSafetyEvidence (e := e) pre time)
    (fun T low high covers w receiver k receiverHead atTime upToDate receiverHeadOk => by
      obtain ⟨nodes, _, tree, _⟩ := Store.getHead_leaf receiverHeadOk
      have lowK : (e.world n).time ≤ (e.world k).time := atTime ▸ low
      have highK : (e.world k).time ≤ time := atTime ▸ high
      have route := viableAt T low high covers w receiver k nodes receiverHead atTime upToDate
        receiverHeadOk tree
      rcases known_or_collision_of_viable anchored start caller receiver callerHeld tree route with
        known | ⟨r, evidence, searched⟩
      swap
      · exact .inr (.inl ⟨u, caller, w, receiver, n, k, callerTime, highK, r, evidence, searched⟩)
      obtain ⟨⟨state, stateOk⟩, windowsOk⟩ :=
        reads w receiver k receiverHead lowK highK upToDate receiverHeadOk
      -- The ceiling and the parameter bound give the receiver's proposer score.
      obtain ⟨score, scoreOk⟩ := computeProposerScore_exists scoreFits positive
        (BeaconState.registryWithinLimit_of_lt preGloas state)
        (ceiling w receiver k _ state highK stateOk)
      have receiverParent : ((e.world k).state w).isAncestor receiverHead
          ⟨block.parentRoot, .pending⟩ = .ok true :=
        parentCovers T low (by omega) w receiver k receiverHead atTime upToDate receiverHeadOk
      obtain ⟨current, receiverEpoch, receiverLast, currentOk, receiverEpochOk, receiverLastOk,
        blockLe⟩ := receiver_clock_reads anchored start anchorSlot slots receiver k known
          blockPositive
      -- Both steps conclude at time `T`; their alternatives also hold at the horizon.
      suffices atStep : (((e.world k).state w).isAncestor receiverHead ⟨root, .pending⟩ = .ok true ∨
          ∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ T ∧ (e.world j).time ≤ T ∧
            ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b)
              [r] = some evidence) ∨
          HistoricalDirectSafetyEvidence (e := e) pre T by
        rcases atStep with (ancestor | ⟨a, ha, b, hb, i, j, hi, hj, rest⟩) |
            ⟨w', hw', i, j, ij, hj, rest⟩
        · exact .inl ancestor
        · exact .inr (.inl ⟨a, ha, b, hb, i, j, by omega, by omega, rest⟩)
        · exact .inr (.inr ⟨w', hw', i, j, ij, by omega, rest⟩)
      by_cases nearParent : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2
      · -- Historical-anchor step at time `T`.
        have lastLt : receiverLast < current := by
          have h1 := (subChecked_ok_iff.mp receiverLastOk).2
          have := UInt64.le_iff_toNat_le.mp blockLe
          simp only [UInt64.toNat_one] at h1
          exact UInt64.lt_iff_toNat_lt.mpr (by omega)
        have beforeLt : beforeBlock < current := by
          have h1 := (subChecked_ok_iff.mp beforeOk).2
          have := UInt64.le_iff_toNat_le.mp blockLe
          simp only [UInt64.toNat_one] at h1
          exact UInt64.lt_iff_toNat_lt.mpr (by omega)
        obtain ⟨window, windowOk⟩ := windowsOk current receiverLast currentOk lastLt
        obtain ⟨participants, participantsOk⟩ :=
          windowsOk current beforeBlock currentOk beforeLt
        have lastLe : receiverLast ≤ finish :=
          e.previousSlot_le_of_time_le start receiver reference (highK.trans referenceTime)
            referenceUpToDate currentOk referenceSlotOk receiverLastOk finishOk
        have finality := receiverFinality_of_viable anchored start anchorSlot preGloas absent
          family receiver highK known tree route
        have step := e.isAncestor_getHead_of_historical_anchor sync slots positive minLookahead
          maxLookahead ring preGloas (time := T)
          (fun v hv w hw i j hj => admitted v hv w hw i j (by omega))
          half (fun v hv s c d a dt b dl => votes v hv s c d a dt b (by omega)) fits
          (prompt.of_le high)
          (fun w hw j hj => windows w hw j (by omega))
          (fun w hw j hj => history w hw j (by omega))
          anchored sound anchorSlot anchorBoundary start caller callerUpToDate headNode slotOk
          beginOk timeEq blockOk parentOk sourceOk boostOk firstOk lastOk beforeOk maximumOk
          parentParticipantsOk registry aligned increment supportOk discountOk adversaryOk margin
          low
          (fun w hw j hd st cur fs fn mx a b => sourceReads w hw j hd st cur fs fn mx a (by omega))
          (fun w hw j hd st sc ssc fs fn mx smx a b => drift w hw j hd st sc ssc fs fn mx smx a
            (by omega))
          (receiverLast := receiverLast)
          (fun lo hi ps a b c => reserve lo hi ps a b (UInt64.le_trans c lastLe))
          (fun a ha b hb i j hi hj => residual a ha b hb i j (by omega) (by omega))
          (fun w hw j ep hj => bounded w hw j ep (by omega))
          (fun w hw j hj => roots w hw j (by omega))
          (fun w hw j st hj => unslashed w hw j st (by omega))
          (fun w hw j c st hj => ceiling w hw j c st (by omega))
          parameters genesis pre
          (fun w hw j hj => heldEarly w hw j (by omega))
          (fun w hw j hj => enough w hw j (by omega))
          (fun w hw j hj => terminal w hw j (by omega))
          covers headDescends historicalBelow callerEpochOk historicalEpochOk near epochStartOk
          epochStartTimeOk historyCovers receiver atTime upToDate known finality receiverHeadOk
          receiverParent stateOk currentOk receiverEpochOk nearParent receiverLastOk windowOk
          scoreOk participantsOk
          (exits w receiver k receiverHead current receiverLast lowK highK upToDate receiverHeadOk
            currentOk receiverLastOk)
          (fun a ha i hi => absent a ha i (by omega)) tree route
        exact step
      · -- Duty-epoch step at time `T`, with the late majority's complete epoch after the call.
        obtain ⟨epoch, epochBegin, epochNext, beginTime, endTime, beginOk', nextOk, beginTimeOk,
          endTimeOk, fresh, complete, majority⟩ :=
          late w receiver k receiverEpoch state lowK highK upToDate receiverEpochOk (by omega)
            stateOk
        have step := e.isAncestor_getHead_of_duty_epoch_or_accountable sync slots preGloas
          (first := (e.world n).time) (time := T)
          (fun v hv w hw i j hj => admitted v hv w hw i j (by omega))
          fits (prompt.of_le high) anchored sound anchorSlot anchorBoundary start started
          parameters genesis pre
          (fun w hw j hj => heldEarly w hw j (by omega))
          (fun w hw j hj => enough w hw j (by omega))
          (fun w hw j hj => terminal w hw j (by omega))
          (fun w hw j ep hj => bounded w hw j ep (by omega))
          (fun w hw j hj => roots w hw j (by omega))
          (fun a ha i hi => absent a ha i (by omega))
          covers
          (fun v hv j hd hj => parentCovers T low (by omega) v hv j hd hj)
          receiver atTime upToDate known stateOk tree route
          ⟨epoch, epochBegin, epochNext, beginTime, endTime, beginOk', nextOk, beginTimeOk,
            endTimeOk, fresh, atTime ▸ complete,
            votes.votesInSlots fits endTimeOk (by omega), majority⟩
          receiverHeadOk
        exact step)
  rcases result with cover | alternative
  · exact .inl cover
  · exact .inr alternative

/-- A guarded historical margin keeps the block on every honest head chain until the horizon.

Every up-to-date honest head from the call to the horizon descends from the block.

Otherwise two honest stores hold different blocks at one root, or direct-safety evidence exists.

That evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key.

The induction on time replaces the earlier coverage of the root that each step assumes.

The parent's coverage over the same interval is still assumed.

Until two epochs after the parent's epoch, each step is the historical-anchor step.

After that, each step is the duty-epoch step, which needs a late duty majority at the receiver.

The cross-store finality of the historical-anchor step, `residual`, stays an assumption.

The receivers' reads, their exits and the late duty majority are assumed.

The root's viability is assumed too.

It says that no honest justified checkpoint over the interval conflicts with the root.

That is the checkpoint-consistency half of the safety of the confirmation, not derived here.

A companion theorem derives its late half from an honest signer.

The stake ceiling is `2 * 10^8` ETH, above mainnet's active stake.

The proposer score at each receiver follows from the stake ceiling and `scoreFits`.

The reserve is read up to `finish`, the slot before the current slot of an honest reference store.

That store is at the horizon or later.

A safety threshold that subtracts the exit reserve would make `reserve` and `exits` fixed bounds. -/
public theorem Execution.honestHeadsCover_of_historical_anchor [DecidablePred (· ∈ J)] {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    (history : VoteCommitteeCommonHistory (e := e) time) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {block parent : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {boost maximum : Gwei}
    (headNode : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    {checkpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    (boostOk : computeProposerScore config source = .ok boost)
    (firstOk : addChecked parent.slot 1 = .ok first) (lastOk : subChecked slot 1 = .ok last)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head first
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei} (registry : source.RegistryWithinLimit)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head source root =
      .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head source root =
      .ok adversary)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (callerTime : (e.world n).time ≤ time) (sourceReads : SourceWindowReads (e := e) n time source)
    (drift : WindowMarginDrift (e := e) n time source shift)
    {finish : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first finish)
    {x : ValidatorIndex} (reference : x ∈ J) {m : ℕ} (referenceTime : time ≤ (e.world m).time)
    (referenceUpToDate : UpToDate config checks sources (e.world m).time ((e.world m).view x)
      ((e.world m).state x))
    {referenceSlot : Slot}
    (referenceSlotOk : ((e.world m).state x).getCurrentSlot config = .ok referenceSlot)
    (finishOk : subChecked referenceSlot 1 = .ok finish)
    {horizon : Epoch}
    (residual : ResidualFinalizedCheckpointCompatibility (e := e) horizon time)
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (headDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (near : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    (absent : AnchorParentAbsent (e := e) time)
    (parentCovers : HonestHeadsCover (e := e) block.parentRoot (e.world n).time (time + 1))
    (reads : HonestHeadReads (e := e) first (e.world n).time time)
    (viable : RootViable (e := e) root (e.world n).time time)
    (exits : ReceiverWindowExits (e := e) source first (e.world n).time time)
    (late : LateDutyMajority (e := e) (computeEpochAtSlot preset parent.slot)
      (e.world n).time time) :
    HonestHeadsCover (e := e) root (e.world n).time (time + 1) ∨
      (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨
      HistoricalDirectSafetyEvidence (e := e) pre time :=
  honestHeadsCover_core sync slots positive minLookahead maxLookahead ring preGloas
    admitted half votes fits prompt windows history anchored sound anchorSlot anchorBoundary
    start caller callerUpToDate headNode slotOk beginOk timeEq blockOk parentOk sourceOk boostOk
    firstOk lastOk beforeOk maximumOk parentParticipantsOk registry aligned increment supportOk
    discountOk adversaryOk margin callerTime sourceReads drift reserve reference referenceTime
    referenceUpToDate referenceSlotOk finishOk residual bounded roots unslashed ceiling scoreFits
    parameters genesis pre heldEarly enough terminal headDescends historicalBelow callerEpochOk
    historicalEpochOk near epochStartOk epochStartTimeOk historyCovers absent parentCovers reads
    (fun _ low high _ w receiver k nodes _ atTime upToDate _ tree =>
      viable w receiver k nodes (atTime ▸ low) (atTime ▸ high) upToDate tree)
    exits late

/-- A guarded historical margin keeps the block on every honest head chain until the horizon.

It is the historical-anchor headline with the root's viability replaced by narrower premises.

A justified checkpoint after the call's epoch is derived to descend from the root.

An honest validator signed a vote for it, after the call, from a head that the induction covers.

So three premises replace the root's viability:

- `consistent`: justified checkpoints of the call's epoch or before are comparable with the root;
- `leaf`: the root keeps a viable leaf when it strictly descends from the justified block;
- `signed`: each later justified checkpoint has an honest signer.

The other premises and the conclusion are those of the historical-anchor headline.

That evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key. -/
public theorem Execution.honestHeadsCover_of_signed_justification [DecidablePred (· ∈ J)] {Δ : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : ValidatedDutyVotes (e := e) time) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (windows : AssignmentWindowAgreement (e := e) time)
    (history : VoteCommitteeCommonHistory (e := e) time) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerUpToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {source : BeaconState preset fork}
    {slot first last beforeBlock : Slot} {block parent : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {boost maximum : Gwei}
    (headNode : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (timeEq : (e.world n).time = begin.toNat)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    {checkpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    (boostOk : computeProposerScore config source = .ok boost)
    (firstOk : addChecked parent.slot 1 = .ok first) (lastOk : subChecked slot 1 = .ok last)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head first
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei} (registry : source.RegistryWithinLimit)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head source root =
      .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head source root =
      .ok adversary)
    (margin : maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (callerTime : (e.world n).time ≤ time) (sourceReads : SourceWindowReads (e := e) n time source)
    (drift : WindowMarginDrift (e := e) n time source shift)
    {finish : Slot}
    (reserve : SourceWindowReserve (J := J) (config := config) ((e.world n).state u) head source
      first finish)
    {x : ValidatorIndex} (reference : x ∈ J) {m : ℕ} (referenceTime : time ≤ (e.world m).time)
    (referenceUpToDate : UpToDate config checks sources (e.world m).time ((e.world m).view x)
      ((e.world m).state x))
    {referenceSlot : Slot}
    (referenceSlotOk : ((e.world m).state x).getCurrentSlot config = .ok referenceSlot)
    (finishOk : subChecked referenceSlot 1 = .ok finish)
    {horizon : Epoch}
    (residual : ResidualFinalizedCheckpointCompatibility (e := e) horizon time)
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (unslashed : HonestCountedStatesUnslashed (e := e) time)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) time)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (headDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (historicalBelow : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (near : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historyCovers : HonestHeadsCover (e := e) historical epochStartTime.toNat (e.world n).time)
    (absent : AnchorParentAbsent (e := e) time)
    (parentCovers : HonestHeadsCover (e := e) block.parentRoot (e.world n).time (time + 1))
    (reads : HonestHeadReads (e := e) first (e.world n).time time)
    (consistent : EarlyJustifiedConsistent (e := e) root callerEpoch (e.world n).time time)
    (leaf : RootKeepsViableLeaf (e := e) root (e.world n).time time)
    (signed : JustifiedHonestlySigned (e := e) callerEpoch (e.world n).time time)
    (exits : ReceiverWindowExits (e := e) source first (e.world n).time time)
    (late : LateDutyMajority (e := e) (computeEpochAtSlot preset parent.slot)
      (e.world n).time time) :
    HonestHeadsCover (e := e) root (e.world n).time (time + 1) ∨
      (∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
        ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
          some evidence) ∨
      HistoricalDirectSafetyEvidence (e := e) pre time := by
  classical
  -- Honest stores up to the horizon agree on blocks, or two of them collide.
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agree | collision
  swap
  · obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, evidence, searched⟩ := collision
    exact .inr (.inl ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩)
  have callerHeld : ((e.world n).state u).blocks[root]? = some block :=
    Store.block_ok_iff.mp blockOk
  have forward := e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored)
  -- The block is at or before the call slot, and the call slot is in the caller's epoch.
  have blockLe : block.slot ≤ slot := by
    obtain ⟨current, currentOk, blocks, _⟩ :=
      (forward n u caller).slots_le_current slots (UInt64.le_of_eq anchorSlot)
    rw [slotOk, Except.ok.injEq] at currentOk
    subst current
    exact blocks root block callerHeld
  have callEpochEq : computeEpochAtSlot preset slot = callerEpoch := by
    have read := callerEpochOk
    simp only [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at read
    exact read
  exact honestHeadsCover_core sync slots positive minLookahead maxLookahead ring preGloas
    admitted half votes fits prompt windows history anchored sound anchorSlot anchorBoundary
    start caller callerUpToDate headNode slotOk beginOk timeEq blockOk parentOk sourceOk boostOk
    firstOk lastOk beforeOk maximumOk parentParticipantsOk registry aligned increment supportOk
    discountOk adversaryOk margin callerTime sourceReads drift reserve reference referenceTime
    referenceUpToDate referenceSlotOk finishOk residual bounded roots unslashed ceiling scoreFits
    parameters genesis pre heldEarly enough terminal headDescends historicalBelow callerEpochOk
    historicalEpochOk near epochStartOk epochStartTimeOk historyCovers absent parentCovers reads
    (fun T low high covers w receiver k nodes hd atTime upToDate headOk tree => by
      have lowK : (e.world n).time ≤ (e.world k).time := atTime ▸ low
      have highK : (e.world k).time ≤ time := atTime ▸ high
      by_cases later : callerEpoch < ((e.world k).state w).justifiedCheckpoint.epoch
      · -- A later justified checkpoint descends from the root, through its honest signer.
        obtain ⟨current, currentOk, _, _⟩ :=
          (forward k w receiver).slots_le_current slots (UInt64.le_of_eq anchorSlot)
        exact .inl (justified_descends_of_signer anchored start anchorSlot anchorBoundary
          positive preGloas fits roots
          (fun a ha b hb i j hi hj r l rt hl hr => agree (a, i) ⟨ha, hi⟩ (b, j) ⟨hb, hj⟩
            r l rt hl hr)
          caller callerHeld callerTime beginOk timeEq blockLe callEpochEq covers high receiver
          atTime upToDate headOk currentOk later
          (signed w receiver k current lowK highK upToDate currentOk later))
      · -- An early justified checkpoint: the assumed consistency and the kept leaf.
        exact route_of_split
          (consistent w receiver k lowK highK upToDate (UInt64.not_lt.mp later))
          (leaf w receiver k nodes lowK highK upToDate tree))
    exits late

end EthLib.Consensus.Models.Network
