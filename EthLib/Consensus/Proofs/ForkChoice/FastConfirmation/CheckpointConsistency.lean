module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetVotes
public import EthLib.Consensus.Proofs.DirectSafety.Execution
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# Checkpoint consistency of a fast-confirmation call

A call of the fast confirmation rule counts honest voters for its current target.

An honest set pins each justified checkpoint if 3 times its stake exceeds the total plus a reserve.

One of its members signed that checkpoint.

If that member was counted for the target, it signed both, so the two checkpoints are one.

So an honest store's justified checkpoint of the call's epoch or earlier meets the confirmed root.

One of the two descends from the other, while honest heads descend from the root.
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

/-- An honest set of a call's voters pins the justified checkpoints of the call's epoch.

The call reads its fork-choice head, and the set is active in its pulled-up head state.

There `total + (margin + pinReserve) < 3 * stake` holds for the set.

So its stake exceeds a third of the sum of the total, `margin` and the call's pin reserve.

The pin reserve reads that state and the state of the call's target block.

It also reads the state of that block's finalized checkpoint, or the anchor state before then.

Take an up-to-date honest store in the interval whose justified checkpoint is of the call's epoch.

If that epoch is after the anchor's, a member of the set signed the checkpoint.

It signed before the store's slot.

The reserve reads the call's blocks, so two honest stores may collide instead. -/
def JustifiedPinned (anchorEpoch : Epoch) (margin first last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n (head : Root) state total epoch (voters : Finset ValidatorIndex),
    (e.world n).time ≤ last →
    (∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head) →
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ∀ (target : Checkpoint) (anc fin : BeaconState preset fork),
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).blockStates[target.root]? = some anc →
    (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
    (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
    (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state) →
    total.toNat + (margin + pinReserve config state anc fin) <
      3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k (slot : Slot), first ≤ (e.world k).time → (e.world k).time ≤ last →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getCurrentSlot config = .ok slot →
      ((e.world k).state w).justifiedCheckpoint.epoch = epoch → anchorEpoch < epoch →
      (∃ v ∈ voters, ∃ i, (e.world i).time ≤ (e.world k).time ∧ ∃ m ∈ (e.world i).sent,
        ∃ data, (v, data) ∈ statements config checks anchorState anchorBlock m ∧
          data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < slot) ∨
        HonestCollision (e := e) last

/-- The honest count of a call, with the call's pin reserve on top of `margin`.

The reserve reads the call's pulled-up head state and the state of its current target's block.

It also reads the state of that block's finalized checkpoint, or the anchor state before then. -/
def ReservedTargetVotes (margin : ℕ) (u : ValidatorIndex) (n : ℕ) (head : Root) : Prop :=
  ∀ (pulled anc fin : BeaconState preset fork) (target : Checkpoint),
    ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).blockStates[target.root]? = some anc →
    (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
    (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
    HonestTargetVotes e (margin + pinReserve config pulled anc fin) u n head

/-- An earlier call checked the target of a block's epoch.

The block descends from an origin of its epoch.

The origin is the anchor root, or an earlier call's head descends from it.

That call was up to date at a slot start of the epoch, with the reserved count.

It accepted the current-target test.

Honest heads descend from the origin from that call up to `coveredUntil`.

No theorem derives that coverage: a caller supplies it. -/
def TargetChecked (margin : ℕ) (anchorRoot : Root) (u : ValidatorIndex) (n : ℕ)
    (epoch : Epoch) (root : Root) (coveredUntil : ℕ) : Prop :=
  ∃ k ≤ n, ∃ origin,
    ((e.world n).state u).getBlockEpoch root = .ok epoch ∧
    ((e.world n).state u).getBlockEpoch origin = .ok epoch ∧
    ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
    (origin = anchorRoot ∨ ∃ head,
      UpToDate config checks sources (e.world k).time ((e.world k).view u) ((e.world k).state u) ∧
      ((e.world k).state u).getCurrentStoreEpoch config = .ok epoch ∧
      ((e.world k).state u).getHead config = .ok head ∧
      ((e.world k).state u).willCurrentTargetBeJustified config head.root = .ok true ∧
      ((e.world k).state u).isAncestor ⟨head.root, .pending⟩ ⟨origin, .pending⟩ = .ok true ∧
      ReservedTargetVotes (e := e) margin u k head.root ∧
      ∃ slot begin, ((e.world k).state u).getCurrentSlot config = .ok slot ∧
        computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
        (e.world k).time = begin.toNat) ∧
    HonestHeadsCover (e := e) origin (e.world k).time coveredUntil

/-- The checkpoint inputs of one call of the rule that confirmed `root` from `start`.

The call accepted its checks, and the root is on the head's chain.

Off the epoch's first slot, the call's count is reserved.

The start's epoch, if it is the call's, was checked by an earlier call.

At the epoch's first slot, the root is of an earlier epoch.

The call's epoch is at least two and after the anchor's epoch.

The rule checks neither of the last two, and no theorem derives them. -/
def CallCheckpointInputs (margin : ℕ) (anchorRoot : Root) (u : ValidatorIndex) (n : ℕ)
    (fcr : FastConfirmationStore) (head : ForkChoiceNode) (start root : Root) : Prop :=
  ((e.world n).state u).FastConfirmationChecked config fcr head.root start root ∧
  ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∧
  (∀ slot, ((e.world n).state u).getCurrentSlot config = .ok slot →
    isStartSlotAtEpoch preset slot = .ok false →
      ReservedTargetVotes (e := e) margin u n head.root) ∧
  (∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch start = .ok epoch →
    TargetChecked (e := e) margin anchorRoot u n epoch start ((e.world n).time + 1)) ∧
  (∀ slot epoch rootEpoch, ((e.world n).state u).getCurrentSlot config = .ok slot →
    isStartSlotAtEpoch preset slot = .ok true →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch root = .ok rootEpoch → rootEpoch ≠ epoch) ∧
  (∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    GENESIS_EPOCH + 1 < epoch ∧ getCurrentEpoch anchorState < epoch)

/-- A pinned justified checkpoint of the target's epoch is the call's target, or a voter signed it.

That voter is outside the committees seen so far, and it signed before the receiver's slot.

Otherwise two honest stores collide.

The pin gives a voter that signed the justified checkpoint.

If that voter was counted for the target, it signed both.

Two honest votes of one target epoch carry one data. -/
private theorem Execution.target_eq_or_unseen_signer (slots : 0 < config.SLOT_DURATION_MS)
    {anchorEpoch : Epoch} {margin first last : ℕ}
    (pins : JustifiedPinned (e := e) anchorEpoch margin first last)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (nBound : (e.world n).time ≤ last)
    {head : Root} {state anc fin : BeaconState preset fork} {total : Gwei} {epoch : Epoch}
    {target : Checkpoint} {voters : Finset ValidatorIndex}
    {participants : Std.TreeSet ValidatorIndex}
    (headOk : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (stateOk : ((e.world n).state u).getPulledUpHeadState config head = .ok state)
    (totalOk : getTotalActiveBalance state = .ok total)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    (ancOk : ((e.world n).state u).blockStates[target.root]? = some anc)
    (finRead : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin)
    (finAnchor : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState)
    (afterAnchor : anchorEpoch < epoch) (targetEpoch : target.epoch = epoch)
    (members : ∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
      (SignsTarget e v target (e.world n).time ∨ v ∉ participants))
    (quorum : total.toNat + (margin + pinReserve config state anc fin) <
      3 * stake (fun v => balanceAt state v.toNat) voters)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {slot : Slot}
    (kFirst : first ≤ (e.world k).time) (kLast : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (justifiedEpoch : ((e.world k).state w).justifiedCheckpoint.epoch = epoch) :
    (((e.world k).state w).justifiedCheckpoint = target ∨
      ∃ v ∈ voters, v ∉ participants ∧ ∃ i, (e.world i).time ≤ (e.world k).time ∧
        ∃ m ∈ (e.world i).sent, ∃ data,
          (v, data) ∈ statements config checks anchorState anchorBlock m ∧
          data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < slot) ∨
      HonestCollision (e := e) last := by
  rcases pins u caller n head state total epoch voters nBound headOk stateOk totalOk epochOk target
      anc fin targetOk ancOk finRead finAnchor (fun v hv => ⟨(members v hv).1, (members v hv).2.1⟩)
      quorum w receiver k slot kFirst kLast upToDate slotOk justifiedEpoch afterAnchor with
    ⟨v, member, i, iLe, m, sent, data, signed, dataTarget, dataSlot⟩ | collision
  swap
  · exact .inr collision
  refine .inl ?_
  rcases (members v member).2.2 with ⟨_, _, other, otherSent, otherData, otherSigned, otherTarget⟩ |
    unseen
  · have same := Execution.data_eq_of_signed_of_target_epoch slots sent otherSent signed
      otherSigned (members v member).1
      (by rw [dataTarget, otherTarget, justifiedEpoch, targetEpoch])
    exact .inl (dataTarget.symm.trans ((congrArg AttestationData.target same).trans otherTarget))
  · exact .inr ⟨v, member, unseen, i, iLe, m, sent, data, signed, dataTarget, dataSlot⟩


/-- Same-block agreement carries pending descent to a receiver that holds the descendant. -/
private theorem copy_ancestor {sender receiver : Store preset fork}
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (senderReached : Store.Reachable config anchorState anchorBlock sender)
    (reached : Store.Reachable config anchorState anchorBlock receiver)
    (before : fork < .glamsterdam)
    (same : ∀ (r : Root) (b c : BeaconBlock preset fork),
      sender.blocks[r]? = some b → receiver.blocks[r]? = some c → b = c)
    {a b : Root} {aBlock : BeaconBlock preset fork}
    (aKnown : receiver.blocks[a]? = some aBlock)
    (above : sender.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true) :
    receiver.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true := by
  obtain ⟨block, held⟩ := Store.held_of_isAncestor above
  exact Store.isAncestor_of_same_blocks reached before same held
    (senderReached.anchorSlot_le (UInt64.le_of_eq anchorSlot) held) ⟨aBlock, aKnown⟩ above

/-- A target read on a head above the root makes the checkpoint comparable with the root.

The comparison holds at a receiver that holds both blocks. -/
private theorem comparable_of_target_read {sender receiver : Store preset fork}
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (senderReached : Store.Reachable config anchorState anchorBlock sender)
    (reached : Store.Reachable config anchorState anchorBlock receiver)
    (before : fork < .glamsterdam)
    (same : ∀ (r : Root) (b c : BeaconBlock preset fork),
      sender.blocks[r]? = some b → receiver.blocks[r]? = some c → b = c)
    {head root : Root} {checkpoint : Checkpoint}
    {rootBlock checkpointBlock : BeaconBlock preset fork}
    (known : receiver.blocks[root]? = some rootBlock)
    (checkpointKnown : receiver.blocks[checkpoint.root]? = some checkpointBlock)
    (supports : sender.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (read : sender.getCheckpointBlock head checkpoint.epoch = .ok checkpoint.root) :
    receiver.isAncestor ⟨checkpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      receiver.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true := by
  obtain ⟨_, block, _, held, _, targetAbove⟩ := Store.isAncestor_of_getCheckpointBlock before read
  obtain ⟨rb, rk⟩ := Store.held_of_isAncestor supports
  rcases Store.comparable_of_ancestors before held rk targetAbove supports with h | h
  · exact .inl (copy_ancestor anchorSlot senderReached reached before same checkpointKnown h)
  · exact .inr (copy_ancestor anchorSlot senderReached reached before same known h)

/-- The call's target block has a stored state (the anchor of the count's reserves). -/
private theorem exists_blockState_of_currentTarget {u : ValidatorIndex} {n : ℕ} {head : Root}
    {target : Checkpoint}
    (reachable : Store.Reachable config anchorState anchorBlock ((e.world n).state u))
    (preGloas : fork < .glamsterdam)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target) :
    ∃ anc : BeaconState preset fork,
      ((e.world n).state u).blockStates[target.root]? = some anc := by
  obtain ⟨epoch, checkpoint, _, read, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
  obtain ⟨_, block, _, held, _, _⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read
  obtain ⟨anc, stored, _⟩ := reachable.blockStatesFromParents held
  exact ⟨anc, stored⟩

/-- The state of a held block state's finalized checkpoint, once it is after the anchor epoch.

Before that the anchor state stands in for it.

A finalized checkpoint of a held block state after the anchor epoch names a held block.

Its state root is nonzero, so the checkpoint is not the anchor's zero-root read. -/
theorem Store.Reachable.finalizedState_of_blockState {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (params : DirectSafety.Parameters preset) (nonzero : HeldStateRootsNonzero store)
    {root : Root} {anc : BeaconState preset fork} (ancOk : store.blockStates[root]? = some anc) :
    ∃ fin : BeaconState preset fork,
      (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
        store.blockStates[anc.finalizedCheckpoint.root]? = some fin) ∧
      (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) := by
  by_cases later : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch
  · rcases reachable.getCheckpointBlock_of_blockState sound (UInt64.le_of_eq anchorSlot)
        params.slots (by have := params.roots; omega) ancOk (.inl (by simp)) later with
      ⟨-, known⟩ | zero
    · rw [Std.TreeMap.contains_eq_isSome_getElem?] at known
      obtain ⟨block, held⟩ := Option.isSome_iff_exists.mp known
      obtain ⟨fin, stored, -⟩ := reachable.blockStatesFromParents held
      exact ⟨fin, fun _ => stored, fun le => absurd later (UInt64.not_lt.mpr le)⟩
    · obtain ⟨anchorKey, -, anchorFound⟩ := reachable.anchor_known
      rw [reachable.anchorState_root, Except.ok.injEq] at zero
      exact absurd zero (nonzero anchorKey anchorBlock anchorFound)
  · exact ⟨anchorState, fun lt => absurd lt later, fun _ => rfl⟩

/-- The reserved count is a count at the margin plus the call's pin reserve.

The reserve reads the call's pulled-up state, its target block's state and that finalized state. -/
private theorem targetVotes_of_reserved {u : ValidatorIndex} {n margin : ℕ} {head : Root}
    (reserved : ReservedTargetVotes (e := e) margin u n head)
    {pulled anc fin : BeaconState preset fork} {target : Checkpoint}
    (pulledOk : ((e.world n).state u).getPulledUpHeadState config head = .ok pulled)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    (ancOk : ((e.world n).state u).blockStates[target.root]? = some anc)
    (finRead : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin)
    (finAnchor : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) :
    HonestTargetVotes e (margin + pinReserve config pulled anc fin) u n head := by
  intro state support target' slot epochStart lastSlot participants stateOk supportOk targetOk'
    slotOk startOk lastOk participantsOk
  cases Except.ok.inj (stateOk.symm.trans pulledOk)
  cases Except.ok.inj (targetOk'.symm.trans targetOk)
  obtain ⟨voters, members, bound⟩ := reserved pulled anc fin target pulledOk targetOk ancOk finRead
    finAnchor pulled support target slot epochStart lastSlot participants pulledOk supportOk
    targetOk slotOk startOk lastOk participantsOk
  exact ⟨voters, members, by omega⟩

/-- The call's count with its pin reserve, as one margin `M`.

When the call's pulled-up state and target read succeed, `M` adds the pin reserve to the margin.

Otherwise the count is vacuous. -/
private theorem pinned_count {u : ValidatorIndex} {n margin : ℕ} {head : Root}
    (reachable : Store.Reachable config anchorState anchorBlock ((e.world n).state u))
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (params : DirectSafety.Parameters preset)
    (nonzero : HeldStateRootsNonzero ((e.world n).state u))
    (preGloas : fork < .glamsterdam)
    (reserved : ReservedTargetVotes (e := e) margin u n head) :
    ∃ M, HonestTargetVotes e M u n head ∧
      ∀ {pulled anc fin : BeaconState preset fork} {target : Checkpoint},
        ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
        ((e.world n).state u).getCurrentTarget config head = .ok target →
        ((e.world n).state u).blockStates[target.root]? = some anc →
        (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
          ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
        (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
        M = margin + pinReserve config pulled anc fin := by
  cases pulledOk : ((e.world n).state u).getPulledUpHeadState config head with
  | error _ =>
    refine ⟨0, fun _ _ _ _ _ _ _ stateOk => ?_, fun stateOk => ?_⟩ <;>
      simp only [pulledOk, reduceCtorEq] at stateOk
  | ok pulled =>
    cases targetOk : ((e.world n).state u).getCurrentTarget config head with
    | error _ =>
      refine ⟨0, fun _ _ _ _ _ _ _ _ _ targetOk' => ?_, fun _ targetOk' => ?_⟩ <;>
        simp only [targetOk, reduceCtorEq] at targetOk'
    | ok target =>
      obtain ⟨anc, ancOk⟩ := exists_blockState_of_currentTarget reachable preGloas targetOk
      obtain ⟨fin, finRead, finAnchor⟩ :=
        Store.Reachable.finalizedState_of_blockState reachable sound anchorSlot params nonzero ancOk
      refine ⟨margin + pinReserve config pulled anc fin,
        targetVotes_of_reserved reserved pulledOk targetOk ancOk finRead finAnchor, ?_⟩
      intro pulled' anc' fin' target' pulledOk' targetOk' ancOk' finRead' finAnchor'
      simp only [Except.ok.injEq] at pulledOk' targetOk'
      subst pulled' target'
      cases Option.some.inj (ancOk.symm.trans ancOk')
      by_cases later : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch
      · cases Option.some.inj ((finRead later).symm.trans (finRead' later))
        rfl
      · have le := UInt64.not_lt.mp later
        rw [finAnchor le, finAnchor' le]

/-- An honest duty for a checkpoint makes the checkpoint comparable with a covered root.

The duty is between the call and a store's time, and the root is covered over that stretch.

The comparison holds at a store holding both blocks.

The signer's head descends from the root, and reads the checkpoint as its target. -/
private theorem comparable_of_duty {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (preGloas : fork < .glamsterdam) {time first T : ℕ}
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    {root : Root} (covers : HonestHeadsCover (e := e) root first T) (high : T ≤ time)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k k' : ℕ}
    {data : AttestationData}
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k').time ((e.world k').view v) ((e.world k').state v) data)
    (low : first ≤ (e.world k').time) (lt : (e.world k').time < T)
    (kBound : (e.world k).time ≤ time)
    {rootBlock checkpointBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some rootBlock)
    (checkpointKnown : ((e.world k).state w).blocks[data.target.root]? = some checkpointBlock) :
    ((e.world k).state w).isAncestor ⟨data.target.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ((e.world k).state w).isAncestor ⟨root, .pending⟩ ⟨data.target.root, .pending⟩ =
        .ok true := by
  have k'Bound : (e.world k').time ≤ time := by omega
  have reachedV := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k' v
    honest
  have reachedW := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k w
    receiver
  obtain ⟨head, supports, targetRead⟩ := signerHead_of_duty anchored start anchorSlot
    anchorBoundary preGloas roots covers honest receiver duty low lt k'Bound checkpointKnown
  exact comparable_of_target_read anchorSlot reachedV reachedW preGloas
    (agree v honest w receiver k' k k'Bound kBound) known checkpointKnown supports targetRead

/-- An honest duty for a checkpoint places its held block at or before the epoch's boundary.

The duty's target read walks to the boundary. -/
private theorem checkpoint_slot_le_of_duty {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (preGloas : fork < .glamsterdam) {time : ℕ}
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k k' : ℕ}
    {data : AttestationData}
    (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k').time ((e.world k').view v) ((e.world k').state v) data)
    (k'Bound : (e.world k').time ≤ time) (kBound : (e.world k).time ≤ time)
    {checkpointBlock : BeaconBlock preset fork}
    (checkpointKnown : ((e.world k).state w).blocks[data.target.root]? = some checkpointBlock) :
    ∃ boundary, computeStartSlotAtEpoch preset data.target.epoch = .ok boundary ∧
      checkpointBlock.slot ≤ boundary := by
  obtain ⟨_, -, -, -, -, honestData, -⟩ := duty
  have reachedV := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k' v
    honest
  have reachedW := e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) k w
    receiver
  obtain ⟨_, -, targetRead⟩ := honestData.target_read reachedV anchorSlot
    anchorBoundary (roots v honest k' k'Bound) reachedW checkpointKnown
  obtain ⟨boundary, block, boundaryOk, held, le, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas targetRead
  have same := agree v honest w receiver k' k k'Bound kBound _ _ _ held checkpointKnown
  subst same
  exact ⟨boundary, boundaryOk, le⟩

/-- The rule's test `total < 3 · support` and the reserved count give the pinned quorum. -/
private theorem pin_quorum_of_count {support total stake margin pin : ℕ}
    (check : total < 3 * support) (count : 3 * support + (margin + pin) ≤ 3 * stake) :
    total + (margin + pin) < 3 * stake := by
  omega

/-- The receiver's justified checkpoint is comparable with the root, given the pin at the count.

The pin `pin` is the target-or-unseen-signer step at the caller's count.

Its quorum is the third that the rule's test gives, plus the count's margin and pin reserve. -/
private theorem justified_comparable_of_pin {anchor : Store preset fork} {Δ time T : ℕ}
    {anchorEpoch horizon : Epoch} {margin : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    (slots : 0 < config.SLOT_DURATION_MS)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (windows : AssignmentWindowAgreement (e := e) time)
    (params : DirectSafety.Parameters preset)
    (incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (selected : SelectedCheckpointsAgree (e := e) horizon time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {base root : Root}
    {callerEpoch : Epoch}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      base root)
    (callLe : (e.world n).time ≤ T) (high : T ≤ time)
    (baseCovers : HonestHeadsCover (e := e) base (e.world n).time (time + 1))
    (covers : HonestHeadsCover (e := e) root (e.world n).time T)
    (holds : HonestHoldsFrom (e := e) root (e.world n).time time)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {hd : ForkChoiceNode}
    (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (hdOk : ((e.world k).state w).getHead config = .ok hd)
    (early : ((e.world k).state w).justifiedCheckpoint.epoch ≤ callerEpoch)
    (pin : ∀ {state anc fin : BeaconState preset fork} {total : Gwei} {target : Checkpoint}
      {voters : Finset ValidatorIndex} {participants : Std.TreeSet ValidatorIndex} {slot : Slot},
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      getTotalActiveBalance state = .ok total →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
        ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
      (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
      anchorEpoch < callerEpoch → target.epoch = callerEpoch →
      (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
        (SignsTarget e v target (e.world n).time ∨ v ∉ participants)) →
      total.toNat + (margin + pinReserve config state anc fin) <
        3 * stake (fun v => balanceAt state v.toNat) voters →
      ((e.world k).state w).getCurrentSlot config = .ok slot →
      ((e.world k).state w).justifiedCheckpoint.epoch = callerEpoch →
      ((e.world k).state w).justifiedCheckpoint = target ∨
        ∃ v ∈ voters, v ∉ participants ∧ ∃ i, (e.world i).time ≤ (e.world k).time ∧
          ∃ m ∈ (e.world i).sent, ∃ data,
            (v, data) ∈ statements config checks anchorState anchorBlock m ∧
            data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < slot) :
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true := by
  have nBound : (e.world n).time ≤ time := callLe.trans high
  have kBound : (e.world k).time ≤ time := atTime ▸ high
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := params.slots
  have forward := e.forwardReachable
    (fun a ha => (start a ha) ▸ Store.ForwardReachable.anchor anchored)
  have sr := (forward n u caller).reachable
  have rr := (forward k w receiver).reachable
  have common := agree u caller w receiver n k nBound kBound
  obtain ⟨checked, onChain, targetVotes, -, -, -⟩ := inputs
  have pending : head = (⟨head.root, .pending⟩ : ForkChoiceNode) := by
    have p := Store.getHead_pending preGloas headOk
    cases head
    simp_all
  have rootAbove : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true := by
    rw [pending]
    exact onChain
  have callerBase := baseCovers _ le_rfl (by omega) u caller n head rfl upToDate headOk
  have receiverBase := baseCovers (e.world k).time (by omega) (by omega) w receiver k hd rfl ready
    hdOk
  have receiverJ := Store.isAncestor_getHead hdOk
  obtain ⟨sb, sk⟩ := Store.held_of_isAncestor callerBase
  obtain ⟨rb, rk⟩ := Store.held_of_isAncestor rootAbove
  obtain ⟨rsb, rsk⟩ := Store.held_of_isAncestor receiverBase
  have seq := common _ _ _ sk rsk
  subst rsb
  obtain ⟨jb, jk⟩ := Store.held_of_isAncestor receiverJ
  obtain ⟨rootBlock, known⟩ := holds w receiver k (by omega) kBound ready
  -- Compare the base with the root before comparing the receiver's justification with the base.
  rcases Store.comparable_of_ancestors preGloas sk rk callerBase rootAbove with below | above
  · have copied := copy_ancestor anchorSlot sr rr preGloas common rsk below
    have supported := Store.isAncestor_trans_of_lt preGloas rsk known receiverBase copied
    exact Store.comparable_of_ancestors preGloas jk known receiverJ supported
  have baseBelow := copy_ancestor anchorSlot sr rr preGloas common known above
  rcases Store.comparable_of_ancestors preGloas jk rsk receiverJ receiverBase with aboveJ | belowJ
  swap
  · exact .inr (Store.isAncestor_trans_of_lt preGloas rsk jk baseBelow belowJ)
  by_cases reverse : ((e.world k).state w).isAncestor ⟨base, .pending⟩
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true
  · exact .inr (Store.isAncestor_trans_of_lt preGloas rsk jk baseBelow reverse)
  -- The justified block strictly descends from the base.
  have baseStrict : sb.slot < jb.slot := by
    by_contra notLt
    have walk := Store.getAncestor_of_isAncestor_of_lt preGloas rsk aboveJ
    rw [Store.getAncestor_of_le jk (UInt64.not_lt.mp notLt)] at walk
    have eq := Except.ok.inj walk
    exact reverse (eq ▸ Store.isAncestor_self jk)
  obtain ⟨epoch, slot, rootEpoch, baseEpoch, epochOk, slotOk, rootEpochOk, baseEpochOk,
    age, tests⟩ := checked
  have callerEq := Except.ok.inj (callerEpochOk.symm.trans epochOk)
  subst callerEpoch
  obtain ⟨current, currentOk, -, -⟩ :=
    (forward k w receiver).slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have currentEpochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have cpHorizon : ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon := UInt64.le_trans
    ((forward k w receiver).justified_epoch_le_current sound slots
      (UInt64.le_of_eq anchorSlot) currentEpochOk).1
    (bounded w receiver k _ kBound currentEpochOk)
  -- The receiver's justification is after the anchor: the anchor's block is below every block.
  obtain ⟨anchorRoot, hashed, -, -, aj, -⟩ := getForkchoiceStore_anchor anchored
  have anchorEq : anchorEpoch = getCurrentEpoch anchorState := by rw [← anchorOk, aj]
  have afterAnchor : anchorEpoch < ((e.world k).state w).justifiedCheckpoint.epoch := by
    have finalLower : getCurrentEpoch anchorState ≤
        ((e.world k).state w).finalizedCheckpoint.epoch := by
      rcases UInt64.le_total ((e.world k).state w).finalizedCheckpoint.epoch
          (getCurrentEpoch anchorState) with le | le
      · exact UInt64.le_of_eq (rr.finalized_eq_anchor_of_epoch_le le).1.symm
      · exact le
    have lower := UInt64.le_trans finalLower (rr.finalized_le_justified sound)
    rw [← anchorEq] at lower
    by_contra old
    have eq := UInt64.le_antisymm (UInt64.not_lt.mp old) lower
    have zeroBound : (e.world 0).time ≤ time := (e.monotone_time (Nat.zero_le k)).trans kBound
    have zeroJ : ((e.world 0).state w).justifiedCheckpoint = anchor.justifiedCheckpoint := by
      change (e.start w).justifiedCheckpoint = _
      rw [start w receiver]
    have same := selected w receiver w receiver k 0 kBound zeroBound _ _ (.inl rfl) (.inl rfl)
      (by rw [zeroJ, eq, anchorOk]) cpHorizon
    rw [same, zeroJ, aj] at jk
    obtain ⟨r, hr, held⟩ := rr.anchor_known
    cases Except.ok.inj (hr.symm.trans hashed)
    rw [held, Option.some.injEq] at jk
    subst jb
    exact UInt64.not_le.mpr baseStrict (sr.anchorSlot_le (UInt64.le_of_eq anchorSlot) sk)
  -- An honest signer of the justified checkpoint places its block at its epoch boundary.
  obtain ⟨v, honest, i, iLe, m, sent, data, member, target, dataBefore⟩ :=
    signed w receiver k current (Nat.zero_le _) kBound ready currentOk afterAnchor
  obtain ⟨k', k'Lt, duty⟩ := e.exists_maySign_of_signed sent member honest
  have k'Le : (e.world k').time ≤ (e.world k).time :=
    (e.monotone_time k'Lt.le).trans iLe
  have jkData : ((e.world k).state w).blocks[data.target.root]? = some jb := by
    rw [target]
    exact jk
  obtain ⟨boundary, boundaryOk, cpBefore⟩ := checkpoint_slot_le_of_duty anchored start anchorSlot
    anchorBoundary preGloas roots agree honest receiver duty (by omega) kBound jkData
  have baseEpochEq : computeEpochAtSlot preset sb.slot = baseEpoch := by
    simpa [Store.getBlockEpoch, Store.block_ok_iff.mpr sk, bind, Except.bind, pure,
      Except.pure] using baseEpochOk
  have epochStrict : baseEpoch < data.target.epoch := by
    have lt := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_lt_of_le baseStrict cpBefore)
    have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    rw [← baseEpochEq, UInt64.lt_iff_toNat_lt, computeEpochAtSlot, UInt64.toNat_div]
    exact (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
  have epochEq : data.target.epoch = epoch := by
    have lt := UInt64.lt_iff_toNat_lt.mp epochStrict
    have le := UInt64.le_iff_toNat_le.mp early
    rw [← target] at le
    exact UInt64.toNat_inj.mp (by omega)
  have cpEpoch : ((e.world k).state w).justifiedCheckpoint.epoch = epoch := target ▸ epochEq
  have boundaryEpochOk : computeStartSlotAtEpoch preset epoch = .ok boundary := epochEq ▸ boundaryOk
  obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := atSlot
  have callEq := Except.ok.inj (callSlotOk.symm.trans slotOk)
  subst callSlot
  have slotEpoch : computeEpochAtSlot preset slot = epoch := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using epochOk
  -- An honest duty for the receiver's checkpoint from the call's slot on settles it.
  have viaDuty {v : ValidatorIndex} (honest : v ∈ J) {k' : ℕ} {data : AttestationData}
      (duty : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k').time ((e.world k').view v) ((e.world k').state v) data)
      (dataTarget : data.target = ((e.world k).state w).justifiedCheckpoint)
      (after : slot ≤ data.slot) (before : data.slot < current) :
      ((e.world k).state w).isAncestor
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
        ((e.world k).state w).isAncestor ⟨root, .pending⟩
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true := by
    obtain ⟨low, lt⟩ := duty_window_of_slot_le start fits callBeginOk receiver ready currentOk
      honest duty after before
    have jk' : ((e.world k).state w).blocks[data.target.root]? = some jb := by
      rw [dataTarget]
      exact jk
    have low' : (e.world n).time ≤ (e.world k').time := by omega
    have lt' : (e.world k').time < T := by omega
    have result := comparable_of_duty anchored start anchorSlot anchorBoundary preGloas roots agree
      covers high honest receiver duty low' lt' kBound known jk'
    rwa [dataTarget] at result
  -- At the epoch's first slot, the justification's own signer votes from the call on.
  by_cases callBefore : slot ≤ boundary
  · exact viaDuty honest duty target
      (UInt64.le_trans callBefore (boundary_le_of_duty duty boundaryOk)) dataBefore
  have offStart : isStartSlotAtEpoch preset slot = .ok false := by
    unfold isStartSlotAtEpoch computeSlotsSinceEpochStart
    rw [slotEpoch, boundaryEpochOk]
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    apply decide_eq_false
    intro zero
    have below := UInt64.le_of_lt (UInt64.not_le.mp callBefore)
    have eqNat := congrArg UInt64.toNat zero
    rw [UInt64.toNat_sub_of_le _ _ below] at eqNat
    exact callBefore (UInt64.le_iff_toNat_le.mpr (by simpa using Nat.le_of_sub_eq_zero eqNat))
  -- The count carries the pin reserve of the call's pulled-up, target and finalized states.
  have nonzero := roots u caller n nBound
  obtain ⟨M, count, countMargin⟩ := pinned_count sr sound anchorSlot params nonzero preGloas
    (targetVotes slot slotOk offStart)
  -- Off the first slot, a counted quorum pins the justification to the target, or an unseen voter.
  have numeric {state : BeaconState preset fork} {total : Gwei} {target' : Checkpoint}
      {first last : Slot} {participants : Std.TreeSet ValidatorIndex}
      {voters : Finset ValidatorIndex}
      (stateOk : ((e.world n).state u).getPulledUpHeadState config head.root = .ok state)
      (totalOk : getTotalActiveBalance state = .ok total)
      (targetOk : ((e.world n).state u).getCurrentTarget config head.root = .ok target')
      (targetEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok target'.epoch)
      (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first)
      (lastOk : subChecked slot 1 = .ok last)
      (participantsOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
        .ok participants)
      (read : ((e.world n).state u).getCheckpointBlock head.root target'.epoch = .ok target'.root)
      (members : ∀ v ∈ voters, v ∈ J ∧
        v ∈ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ∧
        (SignsTarget e v target' (e.world n).time ∨ v ∉ participants))
      {support : Gwei} (check : total.toNat < 3 * support.toNat)
      (bound : 3 * support.toNat + M ≤ 3 * stake (fun v => balanceAt state v.toNat) voters) :
      ((e.world k).state w).isAncestor
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
        ((e.world k).state w).isAncestor ⟨root, .pending⟩
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true := by
    have targetEpoch : target'.epoch = epoch := Except.ok.inj (targetEpochOk.symm.trans epochOk)
    obtain ⟨anc, ancOk⟩ := exists_blockState_of_currentTarget sr preGloas targetOk
    obtain ⟨fin, finRead, finAnchor⟩ :=
      Store.Reachable.finalizedState_of_blockState sr sound anchorSlot params nonzero ancOk
    rw [countMargin stateOk targetOk ancOk finRead finAnchor] at bound
    have quorum := pin_quorum_of_count check bound
    rcases pin stateOk totalOk targetOk ancOk finRead finAnchor (cpEpoch ▸ afterAnchor)
        targetEpoch members quorum currentOk cpEpoch with
      eq | ⟨v, voter, unseen, i, -, m, sent, data, member, dataTarget, dataBefore⟩
    · rw [← eq] at read
      exact comparable_of_target_read anchorSlot sr rr preGloas common known jk onChain read
    · obtain ⟨honest, -, -⟩ := members v voter
      obtain ⟨k', -, duty⟩ := e.exists_maySign_of_signed sent member honest
      have dutyCopy := duty
      obtain ⟨index, assigned, -⟩ := dutyCopy
      have epochSlot : data.target.epoch = computeEpochAtSlot preset slot := by
        rw [dataTarget, cpEpoch, slotEpoch]
      have low := boundary_le_of_duty duty (by rw [epochSlot]; exact firstOk)
      have after := duty_after_call anchored start positive params.lookahead windows caller nBound
        headOk
        slotOk firstOk lastOk participantsOk honest unseen low assigned
      exact viaDuty honest duty dataTarget after dataBefore
  have baseNe : baseEpoch ≠ epoch := by
    rw [← epochEq]
    exact UInt64.ne_of_lt epochStrict
  by_cases rootCurrent : rootEpoch = epoch
  · have check : ((e.world n).state u).willCurrentTargetBeJustified config head.root =
        .ok true := by
      rcases tests with old | current
      · exact (old.2.1 rootCurrent).elim
      · exact current.2.1 rootCurrent baseNe
    obtain ⟨state, total, support, -, -, stateOk, totalOk, supportOk, -, -, -⟩ :=
      Store.willCurrentTargetBeJustified_eq_ok_true_iff.mp check
    have twoThirds := Store.two_mul_le_three_mul_of_willCurrentTargetBeJustified stateOk totalOk
      supportOk check
    obtain ⟨target', slot', first, last, participants, voters, targetOk, slotOk', targetEpochOk,
      firstOk, lastOk, participantsOk, read, members, bound⟩ :=
      quorum_of_count count stateOk supportOk
    cases Except.ok.inj (slotOk'.symm.trans slotOk)
    have floor := UInt64.le_iff_toNat_le.mp (le_getTotalBalance (getTotalActiveBalance_ok totalOk))
    exact numeric stateOk totalOk targetOk targetEpochOk firstOk lastOk participantsOk read members
      (by omega) bound
  · have check : ((e.world n).state u).willNoConflictingCheckpointBeJustified config head.root =
        .ok true := by
      rcases tests with old | current
      · exact (old.2.2.2 offStart).1
      · exact (current.2.2 rootCurrent).2 offStart
    obtain ⟨target0, target0Ok, _⟩ := bind_ok_iff.mp check
    rcases (Store.willNoConflictingCheckpointBeJustified_eq_ok_true_iff target0Ok).mp check with
      unrealized | ⟨state, total, support, thrice, stateOk, totalOk, supportOk, productOk, lt⟩
    · have targetOk := unrealized ▸ target0Ok
      obtain ⟨epoch', block, epochOk', read, eq⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
      cases Except.ok.inj (epochOk'.symm.trans epochOk)
      have same := selected w receiver u caller k n kBound nBound _ _ (.inl rfl) (.inr rfl)
        (by rw [eq, cpEpoch]) cpHorizon
      rw [same, eq] at jk ⊢
      exact comparable_of_target_read anchorSlot sr rr preGloas common known jk onChain read
    · obtain ⟨target', slot', first, last, participants, voters, targetOk, slotOk', targetEpochOk,
        firstOk, lastOk, participantsOk, read, members, bound⟩ :=
        quorum_of_count count stateOk supportOk
      cases Except.ok.inj (slotOk'.symm.trans slotOk)
      have productNat := (mulChecked_ok_iff.mp productOk).2
      have less := UInt64.lt_iff_toNat_lt.mp lt
      simp only [UInt64.toNat_ofNat] at productNat
      exact numeric stateOk totalOk targetOk targetEpochOk firstOk lastOk participantsOk read
        members (by omega) bound

/-- At a time `T`, an honest store's justified checkpoint is comparable with the confirmed root.

The checkpoint is of the call's epoch or earlier.

Otherwise two honest stores collide on a block, or hold conflicting justified checkpoints. -/
theorem Execution.justified_comparable_of_checked {anchor : Store preset fork} {Δ time T : ℕ}
    {anchorEpoch horizon : Epoch} {margin : ℕ} {g : ForkedBeaconState preset}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    (slots : 0 < config.SLOT_DURATION_MS)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (windows : AssignmentWindowAgreement (e := e) time)
    (params : DirectSafety.Parameters preset)
    (incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (bounded : HonestStoreEpochsBounded (e := e) horizon time)
    (roots : HeldBlockStateRootsNonzero (e := e) time)
    (absent : AnchorParentAbsent (e := e) time) (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) time)
    (enough : HeldRunStakeFloor (e := e) pre horizon time)
    (terminal : HeldTerminalStakeFloor (e := e) horizon time)
    (pins : JustifiedPinned (e := e) anchorEpoch margin 0 time)
    (signed : JustifiedHonestlySigned (e := e) anchorEpoch 0 time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {base root : Root}
    {callerEpoch : Epoch}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (inputs : CallCheckpointInputs (e := e) margin anchor.finalizedCheckpoint.root u n fcr head
      base root)
    (callLe : (e.world n).time ≤ T) (high : T ≤ time)
    (baseCovers : HonestHeadsCover (e := e) base (e.world n).time (time + 1))
    (covers : HonestHeadsCover (e := e) root (e.world n).time T)
    (holds : HonestHoldsFrom (e := e) root (e.world n).time time)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {hd : ForkChoiceNode}
    (atTime : (e.world k).time = T)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (hdOk : ((e.world k).state w).getHead config = .ok hd)
    (early : ((e.world k).state w).justifiedCheckpoint.epoch ≤ callerEpoch) :
    (((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true) ∨
      HonestCollision (e := e) time ∨ CrossStoreJustifiedEvidence (e := e) pre time := by
  rcases e.blocksAgree_or_collision time with agree | collision
  swap
  · exact .inr (.inl collision)
  rcases e.selectedCheckpointsAgree_or_evidence anchored start anchorSlot roots absent params
      genesis pre heldEarly enough terminal with selected | evidence
  swap
  · exact .inr (.inr evidence)
  exact .inl (justified_comparable_of_pin anchored sound anchorSlot anchorBoundary start preGloas
    slots fits windows params incrementPositive anchorOk bounded roots agree selected signed caller
    upToDate atSlot headOk callerEpochOk inputs callLe high baseCovers covers holds receiver atTime
    ready hdOk early
    (fun stateOk totalOk targetOk ancOk finRead finAnchor after targetEpoch members quorum
        currentOk cpEpoch =>
      (Execution.target_eq_or_unseen_signer slots pins caller (callLe.trans high)
        ⟨head, headOk, rfl⟩ stateOk totalOk callerEpochOk targetOk ancOk finRead finAnchor after
        targetEpoch members quorum receiver (Nat.zero_le _) (atTime ▸ high) ready currentOk
        cpEpoch).resolve_right (e.not_honestCollision_of_agree agree)))

end EthLib.Consensus.Models.Network
