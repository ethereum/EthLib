module

public import EthLib.Consensus.Proofs.ForkChoice.HonestProposal
public import EthLib.Consensus.Proofs.ForkChoice.ProposerBoost
import EthLib.Consensus.Proofs.Time

/-!
# Proofs: a timely honest block heads an honest store

Before Gloas, take an honest proposal at the start of a slot.

A store that takes it on its head, before the attestations are due, boosts it for the slot.

While the votes against it weigh less than the boost, it is the head of that store.

The network model is §2 of [arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Under synchrony, an up-to-date honest store holds a proposal that its handler accepts. -/
theorem ProposalAt.contains_of_synchronous {Δ : ℕ} (sync : e.Synchronous Δ)
    {v u : ValidatorIndex} (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {time n : ℕ}
    {signed : SignedBeaconBlock preset fork} (proposal : ProposalAt e v slot time n signed)
    {root : Root} (rooted : SszType.hashTreeRoot signed.message = .ok root) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    (accepted : ∃ after, ((e.world k).state u).onBlock config checks sources signed = .ok after) :
    ((e.world k).state u).blocks.contains root := by
  -- The block is in the view by then, and an up-to-date store has taken each block it accepts.
  obtain ⟨after, step⟩ := accepted
  exact upToDate.contains_of_onBlock (proposal.mem_view sync honest receiver late) step rooted

/-- Before Gloas, a timely honest block heads an honest store that took it on its head.

The store holds the block before the attestations of the slot are due.

It assumes that until then, in the slot, its head is the parent and nothing is boosted.

It assumes that later in the slot the votes against the block weigh less than the boost. -/
theorem getHead_eq_of_proposal (before : fork < .glamsterdam) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) (start : ∀ u ∈ J, e.start u = anchor)
    {v u : ValidatorIndex} (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {time n : ℕ}
    {signed : SignedBeaconBlock preset fork} (proposal : ProposalAt e v slot time n signed)
    {root : Root} (rooted : SszType.hashTreeRoot signed.message = .ok root)
    -- The root is not 32 zero bytes, the value that means no boost.
    (nonzero : root ≠ Vector.replicate 32 0) {due : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok due) (duePositive : 0 < due)
    (inSlot : due < config.SLOT_DURATION_MS)
    -- The receiver holds the block at an event before the attestations are due.
    {k₀ : ℕ} (early : (e.world k₀).time < time + due.toNat)
    (held : ((e.world k₀).state u).blocks[root]? = some signed.message)
    -- Before it holds the block, in the slot, its head is the parent and nothing is boosted.
    (headed : ∀ m ≤ k₀, ((e.world m).state u).blocks[root]? = none →
      ((e.world m).state u).getCurrentSlot config = .ok slot →
      (∃ head, ((e.world m).state u).getHead config = .ok head ∧
          head.root = signed.message.parentRoot) ∧
        ((e.world m).state u).proposerBoostRoot = Vector.replicate 32 0)
    -- A later event of the slot.
    {k : ℕ} (later : k₀ ≤ k) (stays : ((e.world k).state u).getCurrentSlot config = .ok slot)
    -- An assumption on roots: no block that the store holds has the parent root of the anchor.
    (unknown : ((e.world k).state u).blocks[anchorBlock.parentRoot]? = none)
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode} {score : Gwei}
    (justifiedState : ((e.world k).state u).checkpointState
      ((e.world k).state u).justifiedCheckpoint = .ok state)
    (tree : ((e.world k).state u).getFilteredNodeTree config = .ok nodes)
    (viable : ⟨root, .pending⟩ ∈ nodes)
    (proposerScore : ((e.world k).state u).getProposerScore config = .ok score)
    -- The votes against the block weigh less than the boost.
    (light : ∀ lower, ((e.world k).state u).stakeAgainst lower state root < score.toNat)
    {head : ForkChoiceNode} (found : ((e.world k).state u).getHead config = .ok head) :
    head = ⟨root, .pending⟩ := by
  have sameSlot := proposal.inSlot
  subst sameSlot
  have positive : 0 < config.SLOT_DURATION_MS := UInt64.lt_of_le_of_lt UInt64.zero_le inSlot
  have forward := e.forwardReachable
    (fun w hw => (start w hw) ▸ Store.ForwardReachable.anchor anchored)
  -- Blocks only grow, so the parent root of the anchor is unknown at every earlier event.
  have unknownAt : ∀ m ≤ k, ((e.world m).state u).blocks[anchorBlock.parentRoot]? = none := by
    intro m le
    cases known : ((e.world m).state u).blocks[anchorBlock.parentRoot]? with
    | none => rfl
    | some block =>
      rw [e.blocks_of_le le known] at unknown
      cases unknown
  have lower : ∀ m ≤ k, ((e.world m).state u).ParentsBelow := fun m le =>
    (forward m u receiver).reachable.parentsBelow anchorSlot (unknownAt m le)
  -- The proposer lacks the block when it proposes, so the anchor lacks it too.
  have fresh : (e.start u).blocks[root]? = none := by
    cases known : (e.start u).blocks[root]? with
    | none => rfl
    | some block =>
      have atStart : ((e.world 0).state v).blocks[root]? = some block := by
        simpa [Execution.world_zero, World.initial, start v honest, ← start u receiver]
          using known
      have kept := e.blocks_of_le (Nat.zero_le n) atStart
      have notHeld := proposal.fresh root rooted
      simp [Std.TreeMap.contains_eq_isSome_getElem?, kept] at notHeld
  -- The clock of the receiver has the time of genesis of the proposer.
  obtain ⟨genesisU, -, upper⟩ := e.clock_bounds u k₀
  obtain ⟨genesisV, startLe, -⟩ := e.clock_bounds v n
  rw [start u receiver] at genesisU upper
  rw [start v honest] at genesisV startLe
  have genesis : ((e.world k₀).state u).genesisTimeMs = genesisTimeMs :=
    genesisU.trans (genesisV.symm.trans proposal.genesis)
  have anchorLe : anchor.timeMs.toNat ≤ time := by
    have := UInt64.le_iff_toNat_le.mp startLe
    have := proposal.upToDate.1
    omega
  obtain ⟨startTime, startOk, timeEq⟩ := proposal.atStart
  -- The clock is no earlier than the slot of a held block, so no earlier than the slot start.
  obtain ⟨now, nowOk, blocksLe, -⟩ := (forward k₀ u receiver).slots_le_current positive anchorSlot
  have low := blocksLe root signed.message held
  have read : computeSlotAtTimeMs config genesisTimeMs ((e.world k₀).state u).timeMs =
      .ok now := by
    unfold Store.getCurrentSlot at nowOk
    rw [genesis] at nowOk
    exact mapError_ok_iff.mp nowOk
  obtain ⟨startTime', startOk', began⟩ := slotStart_le_of_slotAtTime read low
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  -- The clock is before the deadline, since the anchor clock is at most the slot start.
  have dueNat := UInt64.lt_iff_toNat_lt.mp duePositive
  have insideNat := UInt64.lt_iff_toNat_lt.mp inSlot
  have below : ((e.world k₀).state u).timeMs.toNat < time + due.toNat := by
    have := Nat.max_le.mpr ⟨Nat.le_of_lt (Nat.lt_of_le_of_lt anchorLe
      (Nat.lt_add_of_pos_right dueNat)), Nat.le_of_lt early⟩
    omega
  have elapsedNat : (((e.world k₀).state u).timeMs - startTime).toNat =
      ((e.world k₀).state u).timeMs.toNat - startTime.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr began)
  have current : ((e.world k₀).state u).getCurrentSlot config = .ok signed.message.slot := by
    unfold Store.getCurrentSlot
    rw [genesis]
    refine mapError_ok_iff.mpr (computeSlotAtTimeMs_inside startOk
      (due := ((e.world k₀).state u).timeMs - startTime) (by omega) ?_)
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  have into : ((e.world k₀).state u).getTimeIntoSlotMs config =
      .ok (((e.world k₀).state u).timeMs - startTime) := by
    simp [Store.getTimeIntoSlotMs, current, genesis, startOk, Except.mapError, bind,
      Except.bind, pure, Except.pure]
  -- The receiver boosts the block for the rest of the slot.
  have boosted := e.proposerBoostRoot_of_held later (fun m le => lower m (le.trans later))
    nonzero fresh held current into dueOk (UInt64.lt_iff_toNat_lt.mpr (by omega)) headed stays
  -- No held block builds on a block of the current slot, so the boosted block is a leaf.
  have leaf := (forward k u receiver).not_parentRoot_of_current positive anchorSlot
    (lower k (Nat.le_refl k)) (e.blocks_of_le later held) stays
  exact Store.getHead_eq_of_boost (lower := lower k (Nat.le_refl k)) before justifiedState tree
    viable boosted nonzero proposerScore (light _) leaf found

end EthLib.Consensus.Models.Network
