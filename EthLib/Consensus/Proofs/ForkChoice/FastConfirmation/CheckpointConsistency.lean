module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve

/-!
# Checkpoint consistency of a fast-confirmation call

A call of the fast confirmation rule counts honest voters for its current target.

An honest set with more than a third of the stake, plus a reserve, pins each justified checkpoint.

One of its members signed that checkpoint.

If that member was counted for the target, it signed both, so the two checkpoints are one.
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

The set holds more than a third of the call's stake, plus a reserve.

The call reads its fork-choice head, and the set is active in its pulled-up head state.

There its stake exceeds a third of the total, with `margin` and the call's pin reserve on top.

The pin reserve reads that state and the state of the call's target block.

It also reads the state of that block's finalized checkpoint, or the anchor state before then.

Take an up-to-date honest store in the interval whose justified checkpoint is of the call's epoch.

If that epoch is after the anchor's, a member of the set signed the checkpoint.

It signed before the store's slot. -/
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
      ∃ v ∈ voters, ∃ i, (e.world i).time ≤ (e.world k).time ∧ ∃ m ∈ (e.world i).sent, ∃ data,
        (v, data) ∈ statements config checks anchorState anchorBlock m ∧
        data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < slot

/-- A pinned justified checkpoint of the target's epoch is the call's target, or a voter signed it.

That voter is outside the committees seen so far, and it signed before the receiver's slot.

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
    ((e.world k).state w).justifiedCheckpoint = target ∨
      ∃ v ∈ voters, v ∉ participants ∧ ∃ i, (e.world i).time ≤ (e.world k).time ∧
        ∃ m ∈ (e.world i).sent, ∃ data,
          (v, data) ∈ statements config checks anchorState anchorBlock m ∧
          data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < slot := by
  obtain ⟨v, member, i, iLe, m, sent, data, signed, dataTarget, dataSlot⟩ :=
    pins u caller n head state total epoch voters nBound headOk stateOk totalOk epochOk target anc
      fin targetOk ancOk finRead finAnchor (fun v hv => ⟨(members v hv).1, (members v hv).2.1⟩)
      quorum w receiver k slot kFirst kLast upToDate slotOk justifiedEpoch afterAnchor
  rcases (members v member).2.2 with ⟨_, _, other, otherSent, otherData, otherSigned, otherTarget⟩ |
    unseen
  · have same := Execution.data_eq_of_signed_of_target_epoch slots sent otherSent signed
      otherSigned (members v member).1
      (by rw [dataTarget, otherTarget, justifiedEpoch, targetEpoch])
    exact .inl (dataTarget.symm.trans ((congrArg AttestationData.target same).trans otherTarget))
  · exact .inr ⟨v, member, unseen, i, iLe, m, sent, data, signed, dataTarget, dataSlot⟩

end EthLib.Consensus.Models.Network
