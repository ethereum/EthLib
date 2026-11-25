module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ReceiverExits
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.RootViability
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetCount
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedVotes
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HonestHeads
public import EthLib.Consensus.Proofs.ForkChoice.HeadTotality
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedWalk
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalCoverage
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDrift
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.ForkChoice.ProposerHead
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# The walk of a confirming call and its invariant

One honest validator calls the rule at consecutive slots.

Each call stores a confirmed root, the start it selected or a root of the walk from its head.

The call invariant of a stored root says that up-to-date honest heads descend from it.

Given the invariant and the coverage of the start, each walked member is covered to the horizon.

Otherwise two honest stores collide, or accountable-safety evidence holds.
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

/-! ## The calls of one validator and their obligations

Each call assumes inputs that the rule does not check, for the call and for each walked member.
-/

/-- One call of the rule in a run of calls by one validator. -/
def CallAt (u : ValidatorIndex) (events : List ℕ) (first : FastConfirmationStore)
    (i n : ℕ) (fcr after : FastConfirmationStore) : Prop :=
  events[i]? = some n ∧
    ((events.take i).map fun k => (e.world k).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) first = .ok fcr ∧
    ((e.world n).state u).onFastConfirmation config fcr = .ok after

/-- The inputs of the coverage step for one walked member of one call. -/
def MemberObligations [DecidablePred (· ∈ J)] (u : ValidatorIndex) (n : ℕ) (head : Root)
    (source : BeaconState preset fork) (slot : Slot) (member : Root) (limit : ℕ) : Prop :=
  -- They read the member's block, its parent, the proposer score and the windows of the parent.
  ∀ (block parent : BeaconBlock preset fork) (first last beforeBlock : Slot)
    (boost maximum support discount adversary : Gwei)
    (parentParticipants : Std.TreeSet ValidatorIndex),
    ((e.world n).state u).block member = .ok block →
    ((e.world n).state u).block block.parentRoot = .ok parent →
    computeProposerScore config source = .ok boost →
    addChecked parent.slot 1 = .ok first → subChecked slot 1 = .ok last →
    subChecked block.slot 1 = .ok beforeBlock →
    ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum →
    ((e.world n).state u).getCommitteesBetweenSlots head first beforeBlock =
      .ok parentParticipants →
    ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨member, .pending⟩ = .ok support →
    ((e.world n).state u).computeEmptySlotSupportDiscount config head source member =
      .ok discount →
    ((e.world n).state u).getAdversarialWeight config head source member = .ok adversary →
    -- The member's margin then exceeds the committee weight, the boost and the adversary's weight.
    --
    -- With a positive `shift`, the margin asks more than the rule's one-confirmation test.
    ∃ shift, maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
        discount.toNat + 2 * support.toNat ∧
      -- The excess `shift` pays for the drift of each later window from the source's balances.
      --
      -- An assumption on the run: the drift bound of the excess.
      WindowMarginDrift (e := e) n limit source shift ∧
      -- Each later window keeps the near exit reserve of the source.
      --
      -- The reserve of each later window is an assumption on the run too.
      (∀ x ∈ J, ∀ m (referenceSlot finish : Slot), limit ≤ (e.world m).time →
        UpToDate config checks sources (e.world m).time ((e.world m).view x)
          ((e.world m).state x) →
        ((e.world m).state x).getCurrentSlot config = .ok referenceSlot →
        subChecked referenceSlot 1 = .ok finish →
        SourceWindowReserveWith (J := J) (config := config) ((e.world n).state u) head source
          first finish (exitReserveNear source)) ∧
      -- The late duty majority of the parent's epoch holds from the call to the horizon.
      --
      -- An assumption on the run: the late duty majority and the newly active voters of the window.
      --
      -- The majority buys the receivers more than two epochs after the parent's epoch.
      --
      -- It needs one epoch's honest duties to outweigh the rest of the active stake and the boost.
      LateDutyMajority (e := e) (computeEpochAtSlot preset parent.slot) (e.world n).time limit ∧
      -- The newly active voters of the parent's window also hold from the call to the horizon.
      --
      -- They buy the voters activated two epochs after the parent.
      NewlyActiveVotersInHeadWindow (e := e) block.parentRoot (e.world n).time limit

/-- The inputs of one confirming call that the call step assumes.

They apply only when the call walks from its head to the start it selected, through the stored root.

An assumption on the run: the source reads, the count bounds and the realized guards.

The rule checks none of them.

They buy the call's honest target count and the realized justification of each walked root.

A call that keeps its start walks no roots, so it assumes nothing. -/
def CallObligations [DecidablePred (· ∈ J)] (margin limit : ℕ) (u : ValidatorIndex) (n : ℕ)
    (fcr after : FastConfirmationStore) : Prop :=
  ∀ (head : ForkChoiceNode) (slot : Slot) (start : Root) (source : BeaconState preset fork)
    (chain later : List Root),
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot start →
    ((e.world n).state u).checkpointState after.currentEpochObservedJustifiedCheckpoint =
      .ok source →
    ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later) →
    -- They are the source reads of the later windows and the count.
    --
    -- The source reads fail for a window member deposited after the source state, and on overflow.
    SourceWindowReads (e := e) n limit source ∧
    -- The count bounds carry the call's pin reserve on top of the margin.
    (∀ slot (pulled anc fin : BeaconState preset fork) (target : Checkpoint),
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok false →
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok pulled →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
        ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
      (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
      TargetCountBounds (e := e) (margin + pinReserve config pulled anc fin) u n head.root) ∧
    -- They include the realized justification guards of the accepted roots.
    AcceptedRealizedRecent ((e.world n).state u) (chain ++ [after.confirmedRoot]) ∧
    AcceptedRealizedHead ((e.world n).state u) config head.root (chain ++ [after.confirmedRoot]) ∧
    -- They include each member's inputs.
    ∀ member ∈ chain ++ [after.confirmedRoot],
      MemberObligations (e := e) u n head.root source slot member limit

namespace ConfirmedCalls

/-! ## The balance source of a walked member

The balance source of a call is on the chain of the parent of each walked member.
-/

/-- The anchor state does not hash to the zero root, as no honest store holds a zero state root. -/
theorem anchorState_hash_nonzero {anchor : Store preset fork}
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

/-- A block epoch read names a held block. -/
theorem found_of_blockEpoch {store : Store preset fork} {root : Root} {epoch : Epoch}
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
  rw [isStartSlotAtEpoch_eq, Except.ok.injEq, decide_eq_false_iff_not]
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
  obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
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
  have current := forward.block_epoch_le_current slots anchorSlot slotOk parentFound
  refine ⟨by omega, by omega, ?_⟩
  exact Store.getCheckpointBlock_of_ancestor_epoch startFound descends (by omega) T

/-- A checked walk's confirmed root keeps the recency facts of its start.

A root of the current epoch is not at the epoch's first slot, so the call kept a realized check.

That check reads the root's unrealized justification, which the store's bounds.

An older root reads a voting source two epochs back at most, which the store's also bounds. -/
private theorem root_recent {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
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
  obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
  obtain rfl : be = rootEpoch := Except.ok.inj (beOk.symm.trans rootOk)
  have descends := Store.isAncestor_terminal_of_getAncestorRoots (member := root) walked (by simp)
  refine ⟨?_, R, Store.getCheckpointBlock_of_ancestor_epoch startFound descends
    (by omega) T⟩
  by_cases same : be = computeEpochAtSlot preset slot
  · have inside := not_start_of_confirmed forward slots anchorSlot slotOk (same ▸ rootOk)
      confirmed
    rcases branches with ⟨-, different, -⟩ | ⟨nonStart, -, -⟩
    · exact absurd same different
    · obtain ⟨j, jOk, jLe⟩ := nonStart inside
      have := UInt64.le_iff_toNat_le.mp (forward.unrealizedJustification_epoch_le sound positive
        slots (Store.unrealizedJustification_found jOk))
      rw [same]
      omega
  · obtain ⟨rootBlock, rootFound, rfl⟩ := found_of_blockEpoch rootOk
    have current := forward.block_epoch_le_current slots anchorSlot slotOk rootFound
    have voting : ∃ voteSource : Checkpoint, ∃ r,
        store.getVotingSource config r = .ok voteSource ∧
        (computeEpochAtSlot preset slot).toNat ≤ voteSource.epoch.toNat + 2 := by
      rcases branches with ⟨-, -, ⟨voteSource, voteOk, voteLe, -⟩, -⟩ | ⟨-, -, older⟩
      · exact ⟨voteSource, _, voteOk, voteLe⟩
      · obtain ⟨voteSource, voteOk, voteLe⟩ := (older same).1
        exact ⟨voteSource, _, voteOk, voteLe⟩
    obtain ⟨voteSource, r, voteOk, voteLe⟩ := voting
    have := UInt64.le_iff_toNat_le.mp (forward.votingSource_epoch_le sound positive slots voteOk)
    have := UInt64.toNat_inj.not.mpr same
    omega

/-- A successful call returns a held block. -/
theorem root_known {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0))
    {fcr after : FastConfirmationStore}
    (called : store.onFastConfirmation config fcr = .ok after) :
    ∃ epoch, store.getBlockEpoch after.confirmedRoot = .ok epoch := by
  obtain ⟨head, slot, start, -, -, selected, result⟩ := Store.onFastConfirmation_checked called
  rcases result with same | ⟨-, checked, -⟩
  · rw [same]
    obtain ⟨base, baseCase, startCase⟩ := selected
    rcases startCase with ⟨rfl, _⟩ | ⟨rfl, _, ⟨block, _, found, _⟩, _⟩
    · rcases baseCase with ⟨rfl, ⟨_, blockEpoch, _, known, _⟩, _⟩ | ⟨rfl, _⟩
      · exact ⟨blockEpoch, known⟩
      · obtain ⟨block, found⟩ := reached.finalized_known sound (UInt64.le_of_eq anchorSlot)
          positive window fun zero => nonzero (by rw [reached.anchorState_root, zero])
        exact blockEpoch_of_found found
    · exact blockEpoch_of_found (Store.block_ok_iff.mp found)
  · obtain ⟨_, _, rootEpoch, _, _, _, known, _⟩ := checked
    exact ⟨rootEpoch, known⟩

/-- A call after the first one has the call before it, whose result the call reads. -/
theorem callAt_previous {u : ValidatorIndex} {events : List ℕ}
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

/-- The premises of the run of calls, bundled once. -/
structure CallsCtx (anchor : Store preset fork) (u : ValidatorIndex) (events : List ℕ)
    (firstSlot : Slot) (limit : ℕ) : Prop where
  anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor
  sound : Invariant anchorState
  anchorSlot : anchorBlock.slot = anchorState.slot
  anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true
  start : ∀ w ∈ J, e.start w = anchor
  slots : 0 < config.SLOT_DURATION_MS
  positive : 0 < preset.SLOTS_PER_EPOCH.toNat
  long : 1 < preset.SLOTS_PER_EPOCH
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
theorem CallsCtx.forward (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
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
theorem call_order (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
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
theorem call_zero (long : 1 < preset.SLOTS_PER_EPOCH) {n : ℕ}
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
      rw [isStartSlotAtEpoch_eq]
      simp [zero]
    obtain ⟨next, nextOk⟩ := next_exists called slotOk
    rw [(atStart st).1, keepPrev next nextOk (isStartSlotAtEpoch_next_eq_false long nextOk st)]
    rfl
  · have st : isStartSlotAtEpoch preset slot = .ok false := by
      rw [isStartSlotAtEpoch_eq]
      simp [zero]
    rw [(notStart st).1]
    rfl

/-- A later call reads the call before it.

At an epoch's first slot, its observed checkpoint is the earlier call's unrealized justified one.

At any other slot, it keeps the observed checkpoint of the earlier call. -/
theorem call_succ (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {j n : ℕ}
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
      rw [isStartSlotAtEpoch_eq]
      simp [zero]
    obtain ⟨next, nextOk⟩ := next_exists calls.2.2 slotNOk
    have step : addChecked slotM 1 = .ok slotN := addChecked_ok_iff.mpr ⟨by
      have := slotN.toNat_lt
      simp only [UInt64.toNat_one]
      omega, by simp only [UInt64.toNat_one]; omega⟩
    refine .inl ⟨st, ?_⟩
    rw [(atStart st).1, keepPrev next nextOk (isStartSlotAtEpoch_next_eq_false ctx.long nextOk st),
      toPrev slotN step st]
  · have st : isStartSlotAtEpoch preset slotN = .ok false := by
      rw [isStartSlotAtEpoch_eq]
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
  have mono := e.anchor_unrealized_le ctx.start ctx.caller n
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

/-- A reachable store past the anchor epoch reads its finalized checkpoint at some root.

The checkpoint comes from a held state or from its pull-up, whose block reads it on its chain.

The anchor state must not hash to the zero root. -/
theorem finalized_read {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0))
    (later : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch) :
    ∃ root, store.getCheckpointBlock root store.finalizedCheckpoint.epoch =
      .ok store.finalizedCheckpoint.root := by
  have known := fun {root : Root} {state : BeaconState preset fork}
      (stored : store.blockStates[root]? = some state) member =>
    reached.getCheckpointBlock_of_blockState sound anchorSlot positive window stored
      (checkpoint := store.finalizedCheckpoint) member later
  rcases reached.finalized_origins _ (Or.inl rfl) with ⟨root, -, same⟩ |
      ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, pulledOk, same⟩
  · rw [same] at later
    exact absurd later (UInt64.lt_irrefl _)
  · rcases known stored (.inl (by simp [same])) with ⟨read, -⟩ | zero
    · exact ⟨root, read⟩
    · exact absurd zero nonzero
  · rcases known stored (.inr ⟨pulled, pulledOk, by simp [same]⟩) with ⟨read, -⟩ | zero
    · exact ⟨root, read⟩
    · exact absurd zero nonzero

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
    obtain ⟨root, r⟩ := finalized_read reached ctx.sound (UInt64.le_of_eq ctx.anchorSlot)
      ctx.positive ctx.window nonzero lt
    obtain ⟨b, bFound, bLe, -⟩ := Store.getCheckpointBlock_self ctx.positive r
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
        rw [isStartSlotAtEpoch_eq, Except.ok.injEq, decide_eq_true_eq, slotNNat,
          ← Nat.add_assoc] at st'
        simp only [st', ↓reduceIte] at succ
        exact .inl ⟨st, cEq, succ⟩
      · have st' := st
        rw [isStartSlotAtEpoch_eq, Except.ok.injEq, decide_eq_false_iff_not, slotNNat,
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
        Except.ok.inj (beOk.symm.trans (e.getBlockEpoch_of_le mn.le beOk'))
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
            (Store.unrealizedJustification_found ujHead) lt with
          ⟨read, -⟩ | zero
        · obtain ⟨b, bFound, bLe, self⟩ :=
            Store.getCheckpointBlock_self ctx.positive read
          obtain ⟨b', bFound', rfl⟩ := found_of_blockEpoch beOk
          obtain rfl : b' = b := Option.some.inj (bFound'.symm.trans bFound)
          have := UInt64.le_iff_toNat_le.mp (forward.unrealizedJustification_epoch_le ctx.sound
            ctx.positive ctx.slots (Store.unrealizedJustification_found ujHead))
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
      (UInt64.le_of_eq ctx.anchorSlot) slotOk hE cb startFacts checked walked
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
theorem sourceOnParentChain_of_walk {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (long : 1 < preset.SLOTS_PER_EPOCH)
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
    ⟨anchored, sound, anchorSlot, anchorBoundary, start, slots, positive, long, window,
      roots, absent, caller, anchorEpochBefore, atSlots⟩
  obtain ⟨below, -, startRec⟩ := start_recent ctx calls nBound
    (fun j _ m fcr' c b => facts ctx j m fcr' fcr c b)
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  obtain rfl : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  have hE : (computeEpochAtSlot preset slotN).toNat =
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div, slotNNat]
  intro member mem block parent blockOk parentOk
  exact parent_source (ctx.forward n) slots (UInt64.le_of_eq anchorSlot) slotNOk hE below
    (startRec head slotN startRoot headOk slotNOk selects) checked walked mem blockOk parentOk

/-! ## The call invariant -/

/-- The call invariant of the root that a call of one validator stores. -/
def CallInvariant (margin limit : ℕ) (anchorRoot : Root) (u : ValidatorIndex) (n : ℕ)
    (root : Root) : Prop :=
  -- The up-to-date honest heads descend from the root from the next slot to the horizon.
  (∀ slot next following, ((e.world n).state u).getCurrentSlot config = .ok slot →
    addChecked slot 1 = .ok next →
    computeTimeAtSlotMs config genesisTimeMs next = .ok following →
    HonestHeadsCover (e := e) root following.toNat (limit + 1)) ∧
  -- If the root is of the current epoch or the one before, an ancestor of it is too.
  --
  -- That ancestor covers the honest heads from the start of the current epoch.
  (∀ epoch rootEpoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
    epoch.toNat ≤ rootEpoch.toNat + 1 →
    ∃ (historical : Root) (historicalEpoch : Epoch) (epochStart : Slot) (epochStartTime : UInt64),
      ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨historical, .pending⟩ = .ok true ∧
      ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch ∧
      epoch.toNat ≤ historicalEpoch.toNat + 1 ∧
      computeStartSlotAtEpoch preset epoch = .ok epochStart ∧
      computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime ∧
      HonestHeadsCover (e := e) historical epochStartTime.toNat (limit + 1)) ∧
  -- A root of the current epoch passes the target checks of the call, covered to the horizon.
  (∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch root = .ok epoch →
    TargetChecked (e := e) margin anchorRoot u n epoch root (limit + 1))

/-- The evidence alternatives of the call step, in its order. -/
def Bad {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (limit : ℕ) : Prop :=
  HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
    CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
    CrossStoreJustifiedEvidence (e := e) pre limit ∨ HeldStateFinalityEvidence (e := e) pre limit

/-- The facts that the walk reads up to the horizon.

Three hold once the evidence alternatives are split off.

The quorum drift follows from the parameters. -/
structure Good (horizon : Epoch) (limit : ℕ) : Prop where
  agree : SelectedCheckpointsAgree (e := e) horizon limit
  finality : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
    ((e.world i).state a).finalizedCheckpoint.epoch ≤
      ((e.world j).state b).justifiedCheckpoint.epoch →
    ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
        .ok ((e.world i).state a).finalizedCheckpoint.root
  blocks : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
    ∀ (r : Root) (left right : BeaconBlock preset fork),
    ((e.world i).state a).blocks[r]? = some left →
    ((e.world j).state b).blocks[r]? = some right → left = right
  quorum : QuorumDriftWithin (e := e) horizon limit

/-- The premises of the call step that do not depend on the call.

They extend the premises of the run of calls. -/
structure StepCtx {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (Δ : ℕ) (anchor : Store preset fork) (limit : ℕ) (horizon anchorEpoch : Epoch)
    (u : ValidatorIndex) (events : List ℕ) (firstSlot : Slot) : Prop
    extends CallsCtx (e := e) anchor u events firstSlot limit where
  bls : checks = .bls
  anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs
  sync : e.Synchronous Δ
  minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat
  exitWindow : preset.SeedLookaheadAtLeastThree
  ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
  room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon
  weights : .glamsterdam ≤ fork → config.HeadWeightsFit preset (2 * 10 ^ 17)
  supply : .glamsterdam ≤ fork → CheckpointHeadWeightCeiling (e := e) (2 * 10 ^ 17) limit
  admitted : BlocksAdmitted e 0 Δ limit
  half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100
  maxAligned : MaxEffectiveBalancesAligned preset
  incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  votes : ValidatedDutyVotes (e := e) limit
  fits : DelayFits fork config genesisTimeMs Δ
  prompt : Prompt e limit
  windows : AssignmentWindowAgreement (e := e) limit
  fit : config.CommitteeWindowsFit preset
  anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch
  increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0
  bounded : HonestStoreEpochsBounded (e := e) horizon limit
  unslashed : HonestCountedStatesUnslashed (e := e) limit
  ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit
  scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17)
  parameters : DirectSafety.Parameters preset
  genesis : Genesis config checks g
  heldEarly : HeldStatesBeforeUpgrade (e := e) limit
  enough : HeldRunStakeFloor (e := e) pre horizon limit
  terminal : HeldTerminalStakeFloor (e := e) horizon limit
  pinned : JustifiedPinned (e := e) anchorEpoch 0 0 limit
  signedAll : JustifiedHonestlySigned (e := e) anchorEpoch 0 limit
  fusaka : .fusaka ≤ fork
  included : TargetIncluded (e := e) limit
  stale : StaleHeadVotersInWindow (e := e) limit
  reference : ∃ x ∈ J, ∃ m, ∃ referenceSlot finish : Slot, limit ≤ (e.world m).time ∧
    UpToDate config checks sources (e.world m).time ((e.world m).view x)
      ((e.world m).state x) ∧
    ((e.world m).state x).getCurrentSlot config = .ok referenceSlot ∧
    subChecked referenceSlot 1 = .ok finish
  confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot
  upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
    ((e.world n).view u) ((e.world n).state u)

/-- A balance source no later than a held parent's epoch has its registry within the limit.

From Gloas the anchor's room bounds it.

The source is at its checkpoint's epoch or at a held block's epoch, and the horizon bounds both. -/
private theorem source_within {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {n : ℕ} (nBound : (e.world n).time ≤ limit) {checkpoint : Checkpoint}
    {source : BeaconState preset fork}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    {parent : Root} {parentBlock : BeaconBlock preset fork}
    (parentOk : ((e.world n).state u).block parent = .ok parentBlock)
    (notAfter : checkpoint.epoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat) :
    source.RegistryWithinLimit := by
  by_cases gloas : .glamsterdam ≤ fork
  swap
  · exact BeaconState.registryWithinLimit_of_lt (Nat.lt_of_not_le gloas) source
  have forward := ctx.forward n
  have anchorLe : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq ctx.anchorSlot
  obtain ⟨now, nowOk, blocksLe, -⟩ := forward.slots_le_current ctx.slots anchorLe
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset now) := by
    simp [Store.getCurrentStoreEpoch, nowOk, bind, Except.bind, pure, Except.pure]
  have nowLe := ctx.bounded u ctx.caller n _ nBound epochOk
  have blockLe := forward.blockState_epoch_le_current ctx.slots anchorLe epochOk
  have found := Store.checkpointState_ok_iff.mp sourceOk
  have size := (forward.reachable.validators_size_le_of_gloas gloas).2 _ source found
  -- The source is within the horizon: at a held block's epoch, or at its checkpoint's.
  have sourceLe : getCurrentEpoch source ≤ horizon := by
    obtain ⟨base, startSlot, baseHeld, startOk, kept⟩ :=
      forward.reachable.checkpointStatesFromBlocks found
    rcases kept with ⟨-, rfl⟩ | ⟨-, _, -, processed⟩
    · exact UInt64.le_trans (blockLe _ _ baseHeld) nowLe
    have sourceEpoch : getCurrentEpoch source = checkpoint.epoch := by
      rw [getCurrentEpoch, (processSlots_slot processed).2]
      exact computeEpochAtSlot_computeStartSlotAtEpoch
        (UInt64.lt_iff_toNat_lt.mpr ctx.positive) startOk
    have parentLe :=
      UInt64.le_iff_toNat_le.mp (blocksLe _ _ (Store.block_ok_iff.mp parentOk))
    have parentEpochLe : (computeEpochAtSlot preset parentBlock.slot).toNat ≤
        (computeEpochAtSlot preset now).toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right parentLe
    rw [sourceEpoch, UInt64.le_iff_toNat_le]
    exact Nat.le_trans notAfter (Nat.le_trans parentEpochLe (UInt64.le_iff_toNat_le.mp nowLe))
  exact registryWithinLimit_of_anchorRoom size sourceLe (ctx.room gloas)

/-! ## The walk of a call -/

/-- The checkpoint inputs of a call that confirms a walked root. -/
theorem walk_inputs [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      start)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (sourceOk : ((e.world n).state u).checkpointState
      after.currentEpochObservedJustifiedCheckpoint = .ok source)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (obligations : CallObligations (e := e) 0 limit u n fcr after)
    (startInv : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start) :
    CallCheckpointInputs (e := e) 0 anchor.finalizedCheckpoint.root u n after head start
      after.confirmedRoot := by
  obtain ⟨rootBlock, -, rootFound, -, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots (member := after.confirmedRoot) walked (by simp)
      (by simp)
  have headAbove := (Store.parentRoot_of_getAncestorRoots walked rootFound).2.1
  have forward := e.forwardReachable
    (fun x hx => (ctx.start x hx).symm ▸ Store.ForwardReachable.anchor ctx.anchored) n u
    ctx.caller
  refine ⟨checked, headAbove, ?_, ?_, ?_, ?_⟩
  · -- The call's count bounds give its reserved count off the epoch's first slot.
    --
    -- The count bounds give the honest count.
    intro slot' slotOk' inside pulled anc fin target pulledOk targetOk ancOk finOk finAnchor
    have bounds := (obligations head slot start source chain later headOk slotOk selects
      sourceOk walked).2.1 slot' pulled anc fin target slotOk' inside pulledOk targetOk ancOk
      finOk finAnchor
    have maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := by
      have : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := ctx.exitWindow
      omega
    exact Execution.honestTargetVotes_of_byzantineStakeAtMost ctx.anchored ctx.start
      (UInt64.le_of_eq ctx.anchorSlot) ctx.sound ctx.maxAligned ctx.slots
      ctx.minLookahead maxLookahead (by have := ctx.ring; omega) ctx.stale ctx.increment ctx.caller
      nBound ⟨head, headOk, rfl⟩ bounds
  · -- The start's checked target is covered up to `limit + 1`, so up to the next instant.
    intro epoch currentOk startOk
    obtain ⟨k, before, origin, rootOk, originOk, below, checkedOrigin, cover⟩ :=
      startInv.2.2 epoch currentOk startOk
    exact ⟨k, before, origin, rootOk, originOk, below, checkedOrigin,
      honestHeadsCover_mono cover le_rfl (by omega)⟩
  -- At the epoch's first slot the root is of an earlier epoch, as none of that epoch is confirmed.
  --
  · -- At an epoch start no walked root of the current epoch is one-confirmed.
    intro slot' epoch rootEpoch slotOk' boundary currentOk rootOk same
    have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst slot'
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    subst rootEpoch
    have inside := not_start_of_confirmed forward ctx.slots
      (UInt64.le_of_eq ctx.anchorSlot) slotOk rootOk (confirmedAll _ (by simp))
    rw [boundary] at inside
    cases inside
  · -- Each call is at or after the first slot, so in epoch 2 or later and after the anchor's.
    intro epoch currentOk
    obtain ⟨slot', -, slotOk', index, -, -⟩ := ctx.atSlots i n calls.1
    have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst slot'
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    have mono : (computeEpochAtSlot preset firstSlot).toNat ≤
        (computeEpochAtSlot preset slot).toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (by omega)
    have two := UInt64.le_iff_toNat_le.mp ctx.confirmationEpoch
    have before := UInt64.lt_iff_toNat_lt.mp ctx.anchorEpochBefore
    refine ⟨UInt64.lt_iff_toNat_lt.mpr ?_, UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
    simp only [GENESIS_EPOCH, UInt64.toNat_add, UInt64.toNat_zero, UInt64.toNat_one] at two ⊢
    simp only [UInt64.toNat_ofNat] at two
    omega

/-- A call that confirms a walked root keeps the call invariant for that root. -/
theorem walk_invariant [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (startInv : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start)
    (inputs : CallCheckpointInputs (e := e) 0 anchor.finalizedCheckpoint.root u n after head
      start after.confirmedRoot)
    (rootCovers : HonestHeadsCover (e := e) after.confirmedRoot (e.world n).time (limit + 1)) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n after.confirmedRoot := by
  obtain ⟨epoch, slot', rootEpoch, startEpoch, epochOk, slotOk', rootEpochOk, startEpochOk,
    recent, cases⟩ := checked
  have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
  subst slot'
  obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
  have rootAbove := Store.isAncestor_terminal_of_getAncestorRoots walked
    (by simp : after.confirmedRoot ∈ chain ++ after.confirmedRoot :: later)
  obtain ⟨startBlock, startHeld, -⟩ := found_of_blockEpoch startEpochOk
  have member : n ∈ events := List.mem_of_getElem? calls.1
  obtain ⟨callSlot, begin, callSlotOk, -, beginOk, atSlot⟩ := ctx.atSlots i n calls.1
  have sameCall : callSlot = slot := Except.ok.inj (callSlotOk.symm.trans slotOk)
  subst callSlot
  refine ⟨?_, ?_, ?_⟩
  · -- The root covers honest heads from the call on, so from the next slot's start.
    intro readSlot next following readOk nextOk followingOk
    have sameRead : readSlot = slot := Except.ok.inj (readOk.symm.trans slotOk)
    subst readSlot
    have nextNat := (addChecked_ok_iff.mp nextOk).2
    obtain ⟨time, timeOk, -, timeLe⟩ := exists_timeAtSlotMs_of_le (slot := slot) (last := next)
      (UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.toNat_one] at nextNat; omega))
      followingOk
    obtain rfl : time = begin := Except.ok.inj (timeOk.symm.trans beginOk)
    exact honestHeadsCover_mono rootCovers
      (by rw [atSlot]; exact UInt64.le_iff_toNat_le.mp timeLe) le_rfl
  · -- The start's recent historical root is below the root too, since the start is below it.
    intro epoch readRootEpoch currentOk readRootOk _
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    obtain ⟨historical, historicalEpoch, epochStart, epochStartTime, above, historicalOk,
      historicalRecent, epochStartOk, epochStartTimeOk, cover⟩ :=
      startInv.2.1 _ startEpoch currentOk startEpochOk recent
    obtain ⟨_, found, -⟩ := found_of_blockEpoch historicalOk
    exact ⟨historical, historicalEpoch, epochStart, epochStartTime,
      Store.isAncestor_trans startHeld found rootAbove above,
      historicalOk, historicalRecent, epochStartOk, epochStartTimeOk, cover⟩
  · intro epoch currentOk readRootOk
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    have rootSame : rootEpoch = computeEpochAtSlot preset slot :=
      Except.ok.inj (rootEpochOk.symm.trans readRootOk)
    -- The root here is of the current epoch.
    --
    -- The start's checked origin serves if the start is of that epoch.
    by_cases startSame : startEpoch = computeEpochAtSlot preset slot
    · -- The start's checked origin is below the root.
      obtain ⟨k, before, origin, -, originOk, below, checkedOrigin, cover⟩ :=
        startInv.2.2 _ currentOk (startSame ▸ startEpochOk)
      obtain ⟨_, found, -⟩ := found_of_blockEpoch originOk
      exact ⟨k, before, origin, readRootOk, originOk,
        Store.isAncestor_trans startHeld found rootAbove below,
        checkedOrigin, cover⟩
    · -- Otherwise the root is its own origin, checked by this call.
      have target : ((e.world n).state u).willCurrentTargetBeJustified config head.root =
          .ok true := by
        rcases cases with old | current
        · exact False.elim (old.2.1 rootSame)
        · exact current.2.1 rootSame startSame
      have forward := e.forwardReachable
        (fun x hx => (ctx.start x hx).symm ▸ Store.ForwardReachable.anchor ctx.anchored) n u
        ctx.caller
      have inside := not_start_of_confirmed forward ctx.slots
        (UInt64.le_of_eq ctx.anchorSlot) slotOk readRootOk (confirmedAll _ (by simp))
      obtain ⟨_, found, -⟩ := found_of_blockEpoch readRootOk
      exact ⟨n, le_rfl, after.confirmedRoot, readRootOk, readRootOk,
        Store.isAncestor_self found,
        Or.inr ⟨head, ctx.upToDate n member, currentOk, headOk, target, inputs.2.1,
          inputs.2.2.1 slot slotOk inside, slot, begin, slotOk, beginOk, atSlot⟩, rootCovers⟩

/-- The root that a confirming call stores, read from its accepted walk, is held from the call.

Every up-to-date honest store holds it from the call to `limit`, or evidence appears.

It needs the call's realized guard, and the source window's reserve over the adversary. -/
theorem walk_holds [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      start)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (sourceOk : ((e.world n).state u).checkpointState
      after.currentEpochObservedJustifiedCheckpoint = .ok source)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (obligations : CallObligations (e := e) 0 limit u n fcr after) :
    HonestHoldsFrom (e := e) after.confirmedRoot (e.world n).time limit ∨
      Bad (e := e) pre limit := by
  have rootMem : after.confirmedRoot ∈ chain ++ [after.confirmedRoot] := by simp
  have rootWalked : after.confirmedRoot ∈ chain ++ after.confirmedRoot :: later := by simp
  have current := ctx.upToDate n (List.mem_of_getElem? calls.1)
  -- The root's realized post-state, from the call's realized guard.
  obtain ⟨-, -, realized, -, members⟩ :=
    obligations head slot start source chain later headOk slotOk selects sourceOk walked
  obtain ⟨block, rootState, blockFound, stateFound, recent⟩ := realized _ rootMem
  have blockOk := Store.block_ok_iff.mpr blockFound
  -- The call's time is the start of its slot.
  obtain ⟨callSlot, begin, callSlotOk, -, beginOk, timeEq⟩ := ctx.atSlots i n calls.1
  rw [slotOk, Except.ok.injEq] at callSlotOk
  subst callSlot
  -- The caller's store is reachable, with a forward clock.
  have forwardWith := e.forwardReachableWith
    (fun a ha => (ctx.start a ha) ▸ Store.ForwardReachableWith.anchor ctx.anchored) n u
    ctx.caller
  have reached := forwardWith.reachable
  have anchorLe : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq ctx.anchorSlot
  -- The balance source is on the chain of each walked member's parent.
  have onChainAll := sourceOnParentChain_of_walk ctx.anchored ctx.sound ctx.anchorSlot
    ctx.anchorBoundary ctx.start ctx.slots ctx.positive ctx.long ctx.window ctx.roots ctx.absent
    ctx.caller ctx.anchorEpochBefore ctx.atSlots calls nBound headOk slotOk selects checked walked
  -- The root is above the start, and the call is at most one epoch after the start.
  obtain ⟨rootBlock, startBlock, rootBlockOk, startBlockOk, aboveStart⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) rootWalked
  rw [blockOk, Except.ok.injEq] at rootBlockOk
  subst rootBlock
  obtain ⟨epoch, checkedSlot, rootEpoch, startEpoch, epochOk, checkedSlotOk, -, startEpochOk,
    epochLe, -⟩ := checked
  have epochEq : computeEpochAtSlot preset slot = epoch :=
    (Store.getCurrentStoreEpoch_eq slotOk epochOk).symm
  have startEpochEq : computeEpochAtSlot preset startBlock.slot = startEpoch := by
    simpa [Store.getBlockEpoch, startBlockOk, bind, Except.bind, pure, Except.pure] using
      startEpochOk
  subst epochEq startEpochEq
  have startRoot := epoch_le_of_slot_le (preset := preset) startBlock.slot block.slot
    (UInt64.lt_iff_toNat_lt.mp aboveStart).le
  have callNear : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset block.slot).toNat + 1 := by
    omega
  have recency : (computeEpochAtSlot preset slot).toNat ≤
      rootState.currentJustifiedCheckpoint.epoch.toNat + 2 := by
    omega
  -- The terms of the root's one-confirmation.
  have confirmed := confirmedAll _ rootMem
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    Store.isOneConfirmed_eq_ok_true_iff.mp confirmed
  obtain ⟨readSlot, readBlock, parent, boost, first, last, maximum, discount, adversary,
    readSlotOk, readBlockOk, parentOk, boostOk, firstOk, lastOk, maximumOk, discountOk,
    adversaryOk⟩ := Store.computeSafetyThreshold_eq_ok thresholdOk
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  rw [blockOk, Except.ok.injEq] at readBlockOk
  subst readBlock
  obtain ⟨beforeBlock, parentParticipants, -, beforeOk, parentParticipantsOk, -, -⟩ :=
    Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk
      firstOk discountOk
  -- The source window's reserve, at the reference store.
  obtain ⟨shift, -, -, reserveAll, -, -⟩ := members _ rootMem block parent first last
    beforeBlock boost maximum support discount adversary parentParticipants blockOk parentOk
    boostOk firstOk lastOk beforeOk maximumOk parentParticipantsOk supportOk discountOk
    adversaryOk
  obtain ⟨x, xJ, m, referenceSlot, finish, limitLe, xCurrent, referenceOk, finishOk⟩ :=
    ctx.reference
  have reserve := reserveAll x xJ m referenceSlot finish limitLe xCurrent referenceOk finishOk
  -- The reference store's last slot is no earlier than the call's.
  have lastLe : last ≤ finish := e.previousSlot_le_of_time_le ctx.start ctx.caller xJ
    (by omega) xCurrent slotOk referenceOk lastOk finishOk
  -- The range of the adversary and its committees.
  have lower := reached.parentsBelow anchorLe (ctx.absent u ctx.caller n nBound)
    after.confirmedRoot block parent blockFound (Store.block_ok_iff.mp parentOk)
  obtain ⟨startSlot, firstLe, startLe, startEpochLe, rangeOk⟩ :=
    Store.adversaryRange_start slotOk blockOk parentOk firstOk lastOk lower adversaryOk
  obtain ⟨weight, equivocation, -, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨participants, participantsOk, -⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have byzantine : ByzantineStakeAtMost (fun v => balanceAt source v.toNat)
      (Store.activeMembers source participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100 := by
    by_cases ordered : startSlot ≤ last
    · exact ⟨by norm_num, le_trans (Nat.le_add_right _ _)
        (reserve startSlot last participants firstLe ordered lastLe participantsOk)⟩
    · have empty : last < startSlot := by
        rw [UInt64.lt_iff_toNat_lt]
        rw [UInt64.le_iff_toNat_le] at ordered
        omega
      rw [Store.getCommitteesBetweenSlots_of_gt empty, Except.ok.injEq] at participantsOk
      subst participants
      have none : Store.activeMembers source ∅ = ∅ := by
        simp [Store.activeMembers]
      refine ⟨by norm_num, ?_⟩
      rw [none]
      simp [stake_empty]
  -- Lemmas 4 and 3: the honest supporters of the root carry positive stake.
  have descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨after.confirmedRoot, .pending⟩ = .ok true :=
    (Store.parentRoot_of_getAncestorRoots walked blockOk).2.1
  have inside := forwardWith.supportersOf_mem_committees_of_near (balanceSource := source) anchorLe
    ctx.minLookahead (by have : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := ctx.exitWindow; omega)
    (by have := ctx.ring; omega) slotOk blockOk startLe lastOk descends (by omega)
    participantsOk
  have noEquivocator : ∀ w ∈ J, ∀ v ∈ (e.start w).equivocatingIndices, v ∉ J := by
    intro w hw v member
    rw [ctx.start w hw, Store.getForkchoiceStore_equivocatingIndices ctx.anchored] at member
    simp at member
  have positive := e.lt_two_mul_honest_supportersOf_of_isOneConfirmed ctx.slots noEquivocator n
    ctx.caller (source_within ctx nBound sourceOk parentOk
      (onChainAll _ rootMem block parent blockOk parentOk).1) slotOk blockOk
    parentOk boostOk firstOk lastOk maximumOk discountOk adversaryOk rangeOk participantsOk
    confirmed inside (reached.checkpointState_aligned ctx.sound ctx.maxAligned sourceOk)
    ctx.increment byzantine
  obtain ⟨readSlot, readSlotOk, blocksLe, -⟩ :=
    forwardWith.forwardReachable.slots_le_current ctx.slots anchorLe
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  have discountLe := UInt64.le_iff_toNat_le.mp
    (Store.computeEmptySlotSupportDiscount_le blockOk parentOk firstOk lastOk maximumOk
      discountOk (blocksLe _ _ blockFound))
  obtain ⟨v, supporter, honest⟩ : ∃ v ∈ ((e.world n).state u).supportersOf source
      ⟨after.confirmedRoot, .pending⟩, v ∈ J := by
    by_contra absent
    have empty : {v ∈ ((e.world n).state u).supportersOf source
        ⟨after.confirmedRoot, .pending⟩ | v ∈ J} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v member
      exact absent ⟨v, (Finset.mem_filter.mp member).1, (Finset.mem_filter.mp member).2⟩
    rw [empty, stake_empty] at positive
    omega
  -- The supporter's vote is a sent honest statement before the call slot, for a descendant.
  have vote : ∃ v ∈ J, ∃ k, (e.world k).time ≤ (e.world n).time ∧ ∃ m ∈ (e.world k).sent,
      ∃ data, (v, data) ∈ statements config checks anchorState anchorBlock m ∧
        data.slot < slot ∧
        ((e.world n).state u).isAncestor ⟨data.beaconBlockRoot, .pending⟩
          ⟨after.confirmedRoot, .pending⟩ = .ok true := by
    obtain ⟨message, supported, latest, -, supportedOk, voteDescends⟩ :=
      ((e.world n).state u).exists_of_voteCountsFor
        (Store.voteCountsFor_of_mem_supportersOf supporter)
    obtain ⟨attestation, sentMessage, inView, messageEq, signed, origin⟩ :=
      e.exists_signed_origin_of_latestMessages ctx.anchored ctx.start ctx.caller latest
    subst messageEq
    rw [Store.isAncestor_getSupportedNode supportedOk] at voteDescends
    obtain ⟨readSlot, readSlotOk, past⟩ := origin.past
    rw [slotOk, Except.ok.injEq] at readSlotOk
    subst readSlot
    exact ⟨v, honest, n, le_rfl, sentMessage, e.view_subset_sent n u inView, attestation.data,
      signed, past, voteDescends⟩
  rcases Execution.rootHeld_of_honest_vote pre ctx.sync ctx.slots ctx.fits
      ctx.admitted ctx.prompt ctx.anchored ctx.sound ctx.anchorSlot
      ctx.anchorBoundary ctx.start ctx.bounded ctx.roots ctx.absent ctx.parameters ctx.genesis
      ctx.heldEarly ctx.enough ctx.terminal ctx.caller beginOk timeEq nBound blockFound
      stateFound recency vote with
    holds | collision | evidence
  · exact .inl holds
  · exact .inr (.inl collision)
  · exact .inr (.inr (.inr (.inr (.inr evidence))))

/-- The block parent of a root in a store, or the root itself when the store lacks it. -/
private def parentOrSelf (store : Store preset fork) (r : Root) : Root :=
  match store.block r with
  | .ok b => b.parentRoot
  | .error _ => r

/-- In a walk from a head down to a start, each member's parent is the member before it.

The first member's parent is the start. -/
private theorem parentOrSelf_of_walk {store : Store preset fork} {head start : Root}
    {members later : List Root}
    (walked : store.getAncestorRoots head start = .ok (members ++ later)) :
    ∀ i (h : i < members.length), parentOrSelf store members[i] =
      if _ : i = 0 then start else members[i - 1]'(by omega) := by
  intro i h
  have inAll : i < (members ++ later).length := by simp; omega
  have get : (members ++ later)[i] = members[i] := List.getElem_append_left h
  obtain ⟨b, -, found, -, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) (List.getElem_mem inAll)
  have split : store.getAncestorRoots head start = .ok ((members ++ later).take i ++
      (members ++ later)[i] :: (members ++ later).drop (i + 1)) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
    exact walked
  rw [← get, show parentOrSelf store (members ++ later)[i] = b.parentRoot by
    simp [parentOrSelf, found], (Store.parentRoot_of_getAncestorRoots split found).1]
  rcases i with _ | j
  · simp
  · have hj : j < members.length := by omega
    simp [List.getLast?_take, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

/-- The last root of a walk's prefix descends from every member of that prefix. -/
private theorem root_descends_of_walk {store : Store preset fork} {head start root m : Root}
    {chain later : List Root}
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    (mem : m ∈ chain ++ [root]) :
    store.isAncestor ⟨root, .pending⟩ ⟨m, .pending⟩ = .ok true := by
  obtain ⟨rootBlock, -, rootFound, -, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots (member := root) walked (by simp) (by simp)
  rcases List.mem_append.mp mem with inChain | isRoot
  · obtain ⟨s, t, rfl⟩ := List.append_of_mem inChain
    have sub := Store.getAncestorRoots_of_append (older := s) (newer := t ++ root :: later)
      (by simpa using walked)
    exact (Store.parentRoot_of_getAncestorRoots (older := t) (newer := later) sub rootFound).2.2
  · rw [List.mem_singleton.mp isRoot]
    exact Store.isAncestor_self (Store.block_ok_iff.mp rootFound)

/-- Every member of an accepted walk is covered by honest heads from the call to the horizon.

Otherwise one of the five evidence alternatives holds.

The confirmed root is viable at each time it is covered, and each member below it then is too.

An induction on time and along the walk covers the members one by one. -/
theorem walkMembers_cover [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    (good : Good (e := e) horizon limit)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      start)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (sourceOk : ((e.world n).state u).checkpointState
      after.currentEpochObservedJustifiedCheckpoint = .ok source)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (obligations : CallObligations (e := e) 0 limit u n fcr after)
    (startInv : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start)
    (startCovers : HonestHeadsCover (e := e) start (e.world n).time (limit + 1))
    (inputs : CallCheckpointInputs (e := e) 0 anchor.finalizedCheckpoint.root u n after head
      start after.confirmedRoot)
    (holds : HonestHoldsFrom (e := e) after.confirmedRoot (e.world n).time limit)
    (onChainAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ∀ (block parent : BeaconBlock preset fork),
      ((e.world n).state u).block member = .ok block →
      ((e.world n).state u).block block.parentRoot = .ok parent →
      SourceOnParentChain ((e.world n).state u) after.currentEpochObservedJustifiedCheckpoint
        block.parentRoot parent) :
    (∀ m ∈ chain ++ [after.confirmedRoot],
      HonestHeadsCover (e := e) m (e.world n).time (limit + 1)) ∨ Bad (e := e) pre limit := by
  have upToDate := ctx.upToDate n (List.mem_of_getElem? calls.1)
  obtain ⟨slot', begin, slotOk', -, beginOk, timeEq⟩ := ctx.atSlots i n calls.1
  obtain rfl : slot = slot' := Except.ok.inj (slotOk.symm.trans slotOk')
  obtain ⟨sourceReads, -, recent, realizedHead, memberObligations⟩ :=
    obligations head slot start source chain later headOk slotOk selects sourceOk walked
  have reach := fun k w (hw : w ∈ J) =>
    e.reachable (fun a ha => (ctx.start a ha) ▸ Store.Reachable.anchor ctx.anchored) k w hw
  have maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := by
    have : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := ctx.exitWindow
    omega
  -- The caller reads its head at each rollover, unless stores collide or historical evidence holds.
  have signed : JustifiedHonestlySigned (e := e) anchor.justifiedCheckpoint.epoch 0 limit :=
    ctx.anchorEpochOk ▸ ctx.signedAll
  rcases e.callRolloverRead_or_evidence ctx.sync ctx.slots ctx.admitted
      ctx.fits ctx.prompt ctx.votes ctx.anchored ctx.start ctx.anchorSlot ctx.anchorBoundary signed
      ctx.roots ctx.absent ctx.bounded ctx.parameters ctx.genesis pre ctx.heldEarly ctx.enough
      ctx.terminal ctx.ceiling ctx.scoreFits ctx.fit.seeds ctx.caller n head.root
      ctx.room ctx.weights ctx.supply (fun _ => ctx.fit) with
    rollover | collision | evidence
  rotate_left
  · exact .inr (.inl collision)
  · exact .inr (.inr (.inl evidence))
  -- The root is viable at each covered time, unless stores collide or held-state evidence holds.
  by_cases collision : HonestCollision (e := e) limit
  · exact .inr (.inl collision)
  by_cases heldEvidence : HeldStateFinalityEvidence (e := e) pre limit
  · exact .inr (.inr (.inr (.inr (.inr heldEvidence))))
  by_cases cross : CrossStoreJustifiedEvidence (e := e) pre limit
  · exact .inr (.inr (.inr (.inr (.inl cross))))
  have rootViable : ∀ T, (e.world n).time ≤ T → T ≤ limit →
      HonestHeadsCover (e := e) after.confirmedRoot (e.world n).time T →
      RootViableAt (e := e) after.confirmedRoot T := fun T low high covers =>
    (e.rootViableAt_of_checked (room := ctx.room)
      pre ctx.sync ctx.slots ctx.admitted
      ctx.fits ctx.prompt ctx.votes ctx.windows ctx.fit ctx.ring ctx.incrementPositive
      ctx.anchored ctx.sound ctx.anchorSlot ctx.anchorBoundary ctx.start ctx.anchorEpochOk
      ctx.bounded ctx.roots ctx.absent ctx.pinned ctx.signedAll
      good.quorum ctx.unslashed ctx.terminal ctx.anchorGenesis ctx.parameters ctx.genesis
      ctx.heldEarly ctx.enough ctx.included ctx.caller upToDate slotOk beginOk timeEq
      headOk rollover inputs walked recent realizedHead startCovers holds T low high
      covers).resolve_right (not_or.mpr ⟨collision, not_or.mpr ⟨heldEvidence, cross⟩⟩)
  -- The start's recent historical root, from the call invariant at the start.
  obtain ⟨epoch, -, -, startEpoch, epochOk, -, -, startEpochOk, recentStart, -⟩ := checked
  obtain ⟨historical, historicalEpoch, epochStart, epochStartTime, startBelow,
    historicalEpochOk, near, epochStartOk, epochStartTimeOk, historyCovers⟩ :=
    startInv.2.1 epoch startEpoch epochOk startEpochOk recentStart
  obtain ⟨_, historicalKnown, -⟩ := found_of_blockEpoch historicalEpochOk
  have walkedAll : ((e.world n).state u).getAncestorRoots head.root start =
      .ok ((chain ++ [after.confirmedRoot]) ++ later) := by
    simpa using walked
  -- An induction on time and along the walk.
  refine Execution.walk_covers (chain ++ [after.confirmedRoot])
    (parentOrSelf ((e.world n).state u)) (parentOrSelf_of_walk walkedAll) startCovers ?_
  intro T hT earlier m hm parentCovers
  by_cases early : T + 1 ≤ (e.world n).time
  · exact .inl fun _ low high => absurd high (by omega)
  have callerTime : (e.world n).time ≤ T := by omega
  have collisionAt : HonestCollision (e := e) T → HonestCollision (e := e) limit :=
    fun ⟨a, ha, b, hb, i, j, hi, hj, rest⟩ => ⟨a, ha, b, hb, i, j, hi.trans hT, hj.trans hT, rest⟩
  have memWalk : m ∈ chain ++ after.confirmedRoot :: later := by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_left _ h
    · simp [List.mem_singleton.mp h]
  -- The member's reads, from its confirmation.
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    Store.isOneConfirmed_eq_ok_true_iff.mp (confirmedAll m hm)
  obtain ⟨s, block, parent, boost, first, last, maximum, discount, adversary, sOk, blockOk,
    parentOk, boostOk, firstOk, lastOk, maximumOk, discountOk, adversaryOk⟩ :=
    Store.computeSafetyThreshold_eq_ok thresholdOk
  obtain rfl : slot = s := Except.ok.inj (slotOk.symm.trans sOk)
  obtain ⟨beforeBlock, participants, -, beforeOk, participantsOk, -, -⟩ :=
    Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk
      firstOk discountOk
  obtain ⟨shift, margin, drift, reserveAll, late, newlyActive⟩ :=
    memberObligations m hm block parent first last beforeBlock boost maximum support discount
      adversary participants blockOk parentOk boostOk firstOk lastOk beforeOk maximumOk
      participantsOk supportOk discountOk adversaryOk
  obtain ⟨x, hx, mRef, referenceSlot, finish, referenceTime, referenceUpToDate, referenceSlotOk,
    finishOk⟩ := ctx.reference
  rw [show parentOrSelf ((e.world n).state u) m = block.parentRoot by
    simp [parentOrSelf, blockOk]] at parentCovers
  -- The member's near exit bound at time T, or a collision.
  have onChain := onChainAll m hm block parent blockOk parentOk
  have within := source_within ctx nBound sourceOk parentOk onChain.1
  rcases Execution.receiverWindowExitsNear_of_sourceOnParentChain ctx.anchored ctx.start
      ctx.anchorSlot ctx.positive ctx.exitWindow ctx.caller callerTime sourceOk within
      parentOk firstOk onChain parentCovers
    with exits | collision
  swap
  · exact .inr (.inl (collisionAt collision))
  -- The member's walk relations in the caller's store.
  obtain ⟨-, startBlock, -, startFound, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) memWalk
  have startHeld := Store.block_ok_iff.mp startFound
  have headDescends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨m, .pending⟩ =
      .ok true := by
    obtain ⟨older, newer, split⟩ := List.append_of_mem memWalk
    exact (Store.parentRoot_of_getAncestorRoots (split ▸ walked) blockOk).2.1
  have historicalBelow := Store.isAncestor_trans startHeld historicalKnown
    (parent_above startHeld walked hm blockOk) startBelow
  have rootAbove := root_descends_of_walk walked hm
  have membership := Execution.votersInHeadWindow_of_newlyActive ctx.anchored ctx.start
    (UInt64.le_of_eq ctx.anchorSlot) ctx.positive ctx.minLookahead maxLookahead ctx.ring
    (fun w hw k low high => newlyActive w hw k low (high.trans hT))
  -- Each member is viable wherever the root is.
  have viableAt : ∀ T', (e.world n).time ≤ T' → T' ≤ T →
      HonestHeadsCover (e := e) m (e.world n).time T' → RootViableAt (e := e) m T' := by
    intro T' low high _ w hw k nodes hd atTime ready receiverHead tree
    have rootCovers : HonestHeadsCover (e := e) after.confirmedRoot (e.world n).time T' :=
      fun t lo hi => earlier after.confirmedRoot (by simp) t lo (Nat.lt_of_lt_of_le hi high)
    have kLow : (e.world n).time ≤ (e.world k).time := by omega
    have kHigh : (e.world k).time ≤ limit := by omega
    have below : ((e.world k).state w).isAncestor ⟨after.confirmedRoot, .pending⟩
        ⟨m, .pending⟩ = .ok true :=
      Store.isAncestor_of_same_blocks (reach k w hw)
        (fun r b c hb hc => good.blocks u ctx.caller w hw n k nBound kHigh r b c hb hc)
        (Store.block_ok_iff.mp blockOk)
        ((reach n u ctx.caller).anchorSlot_le (UInt64.le_of_eq ctx.anchorSlot)
          (Store.block_ok_iff.mp blockOk))
        (holds w hw k kLow kHigh ready) rootAbove
    exact Store.viable_of_ancestor tree below
      (rootViable T' low (high.trans hT) rootCovers w hw k nodes hd atTime ready receiverHead
        tree)
  -- The member's step at time T.
  rcases Execution.honestHeadsCover_of_viableAt
      (room := ctx.room) ctx.sync ctx.slots
      ctx.minLookahead maxLookahead ctx.ring
      (fun v hv w hw n k le => ctx.admitted v hv w hw n k (le.trans hT)) ctx.half
      (fun v hv s c d a b early le => ctx.votes v hv s c d a b early (le.trans hT)) ctx.fits
      (fun w hw s st a b le => ctx.prompt w hw s st a b (le.trans hT))
      (fun w hw k le => ctx.windows w hw k (le.trans hT)) membership
      ctx.anchored ctx.sound ctx.anchorSlot ctx.anchorBoundary ctx.start ctx.caller upToDate
      ⟨head, headOk, rfl⟩ slotOk beginOk timeEq blockOk parentOk sourceOk boostOk firstOk lastOk
      beforeOk maximumOk participantsOk within
      (Store.Reachable.checkpointState_aligned ctx.sound (reach n u ctx.caller) ctx.maxAligned
        sourceOk)
      ctx.increment supportOk discountOk adversaryOk margin callerTime
      (fun w hw k hd st c f fi mx lo hi => sourceReads w hw k hd st c f fi mx lo (hi.trans hT))
      (fun w hw k hd st sc ss f fi mx smx lo hi =>
        drift w hw k hd st sc ss f fi mx smx lo (hi.trans hT))
      (reserveAll x hx mRef referenceSlot finish referenceTime referenceUpToDate referenceSlotOk
        finishOk)
      hx (hT.trans referenceTime) referenceUpToDate referenceSlotOk finishOk
      (fun w hw k ep le => ctx.bounded w hw k ep (le.trans hT))
      (fun w hw k le => ctx.roots w hw k (le.trans hT))
      (fun w hw k s le => ctx.unslashed w hw k s (le.trans hT))
      (fun w hw k c s le => ctx.ceiling w hw k c s (le.trans hT)) ctx.scoreFits
      ctx.parameters ctx.genesis pre (fun w hw k le => ctx.heldEarly w hw k (le.trans hT))
      (fun w hw k le => ctx.enough w hw k (le.trans hT))
      (fun w hw k le => ctx.terminal w hw k (le.trans hT)) headDescends
      historicalBelow epochOk historicalEpochOk near epochStartOk epochStartTimeOk
      (fun t lo hi => historyCovers t lo (by omega))
      (fun a ha i le => ctx.absent a ha i (le.trans hT)) parentCovers
      ctx.fit viableAt exits (fun w hw k ep st lo hi => late w hw k ep st lo (hi.trans hT))
    with covered | collision | historicalEvidence
  · exact .inl covered
  · exact .inr (.inl (collisionAt collision))
  · obtain ⟨w, hw, i, k, ik, hk, rest⟩ := historicalEvidence
    exact .inr (.inr (.inl ⟨w, hw, i, k, ik, hk.trans hT, rest⟩))

end ConfirmedCalls

end EthLib.Consensus.Models.Network
