module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
public import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
public import EthLib.Consensus.Proofs.ForkChoice.Reachable
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.Totality.Bound
import EthLib.Base.Proofs.MapM
import EthLib.Consensus.Proofs.Containers.State
import EthLib.Consensus.Proofs.ForkChoice.AttestationScores
import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.Ghost
import EthLib.Consensus.Proofs.ForkChoice.StoreEntries
import EthLib.Consensus.Proofs.ForkChoice.Supporters

/-!
# Proofs: the head of the fork choice can be computed

The head of a store that the handlers build can be computed.

The store must hold the state of its justified checkpoint, and the viable nodes must be computed.

Before Gloas, its active stake must be at most `2 * 10^17` Gwei, so that no weight overflows.

The proposer boost must fit the same cap.

The walk weighs only children among the viable nodes, and each of them is a held block.

The votes for a held block can be read: each latest vote names a held block, whose walk succeeds.

Their sum is at most the active stake, so it stays below `2^64`.

The boosted root is zero or a held block, so its walk succeeds too.

A held child sits at a later slot than its held parent, so the walk descends and ends.

From Gloas, the boost also asks whether the parent of the boosted block is weak.

It asks only when that parent is from the slot just before the boosted block.

That test adds the equivocators of the parent's committees to its votes.

So the effective balances of the justified state's whole registry must add up to at most the cap.

It must also hold each equivocator that is active in a held block's state, at that block's epoch.

Each held state must have its registry within the limit, so that its committees can be read.

An empty tree of viable nodes gives the empty node of the justified block.

This is part of [#2060][issue].

[issue]: https://github.com/ethereum/EthLib/issues/2060
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- From Gloas, the head reads that fit 64 bits for active stakes up to a cap.

A slot longer than one millisecond leaves room to name the slot after a held block.

The reorg threshold, a share of the stake up to the cap, fits too. -/
structure Config.HeadWeightsFit (config : Config) (preset : Preset) (cap : ℕ) : Prop where
  /-- A slot lasts more than one millisecond. -/
  slots : 1 < config.SLOT_DURATION_MS
  /-- The reorg threshold of a stake up to the cap fits in 64 bits. -/
  reorg : max preset.EFFECTIVE_BALANCE_INCREMENT.toNat cap *
    config.REORG_HEAD_WEIGHT_THRESHOLD.toNat < 2 ^ 64

/-- The mainnet head reads fit for an active stake up to `2 * 10^17` Gwei. -/
theorem Config.headWeightsFit_mainnet :
    Config.mainnet.HeadWeightsFit Preset.mainnet (2 * 10 ^ 17) := by
  constructor <;> decide

/-- The minimal head reads fit for an active stake up to `2 * 10^17` Gwei. -/
theorem Config.headWeightsFit_minimal :
    Config.minimal.HeadWeightsFit Preset.minimal (2 * 10 ^ 17) := by
  constructor <;> decide

/-- Every equivocator of a store has a place in a state, when it is active in a held block's state.

It is active there at the epoch of that block's slot.

The weak-head test reads the justified state's balance of each equivocator in a held committee. -/
def ActiveEquivocatorsRegistered (store : Store preset fork) (state : BeaconState preset fork) :
    Prop :=
  ∀ (root : Root) (block : BeaconBlock preset fork) (held : BeaconState preset fork),
    store.blocks[root]? = some block → store.blockStates[root]? = some held →
    ∀ i ∈ store.equivocatingIndices, ∀ validator : Validator,
      held.validators.data[i.toNat]? = some validator →
      isActiveValidator validator (computeEpochAtSlot preset block.slot) →
      i.toNat < state.validators.data.size

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The votes for a held node can be read from any state of small enough stake.

The registry of that state must be within its limit.

The score is the stake of the supporters of the node, at most the active stake of that state. -/
private theorem getAttestationScore_exists
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit)
    (small : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset < 2 ^ 64) :
    ∃ score, store.getAttestationScore node state = .ok score ∧
      score.toNat ≤ stake (fun v => balanceAt state v.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ∧
      score.toNat = stake (fun v => balanceAt state v.toNat) (store.supportersOf state node) := by
  -- Each counted vote names a held block, so its check can be computed.
  have checked : ∀ entry ∈ unslashedActiveBalances state, ∀ message,
      store.latestMessages[entry.1]? = some message →
      store.equivocatingIndices.contains entry.1 = false →
      ∃ d, (store.getSupportedNode message >>= (store.isAncestor · node)) = .ok d := by
    intro entry _ message latest _
    obtain ⟨attestation, rfl, origin⟩ := forward.votesHaveOrigins latest
    obtain ⟨voted, votedFound, -⟩ := origin.voted
    obtain ⟨supported, supportedOk⟩ := getSupportedNode_exists (store := store)
      (message := LatestMessage.ofAttestation attestation) votedFound
    obtain ⟨d, dOk⟩ := isAncestor_ok_of_orphans_le
      (forward.reachable.parentsBelow anchorSlot unknown) found
      (fun _ _ f orphan => forward.reachable.orphans_le anchorSlot f orphan found)
      (start := supported) (by rw [getSupportedNode_root supportedOk]; exact votedFound)
    exact ⟨d, by rw [supportedOk]; exact dOk⟩
  -- The counted balances are the stake of the supporters, all of them active.
  have bound : ((unslashedActiveBalances state).map fun entry =>
      if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum ≤
      stake (fun v => balanceAt state v.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset := by
    rw [← stake_supportersOf_eq_sum within]
    exact stake_mono fun v member => List.mem_toFinset.mpr
      (mem_getActiveValidatorIndices_of_isActiveAt (isActiveAt_of_mem_supportersOf within member))
  rw [store.getAttestationScore_eq_of_checked checked]
  dsimp only
  have fits : ¬ 2 ^ 64 ≤ ((unslashedActiveBalances state).map fun entry =>
      if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum := by omega
  simp only [fits, ↓reduceIte]
  have scoreEq := UInt64.toNat_ofNat_of_lt' (n := ((unslashedActiveBalances state).map fun entry =>
      if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum)
    (by simp only [UInt64.size]; omega)
  exact ⟨_, rfl, by rw [scoreEq]; exact bound, by rw [scoreEq, stake_supportersOf_eq_sum within]⟩

/-- The children of a held node can be computed, when parents sit below their children.

Each child is a held node of lower rank. -/
theorem getNodeChildren_held (lower : store.ParentsBelow) {node : ForkChoiceNode}
    {block : BeaconBlock preset fork} (found : store.blocks[node.root]? = some block) :
    ∃ children, store.getNodeChildren node = .ok children ∧ ∀ child ∈ children,
      ∃ childBlock, store.blocks[child.root]? = some childBlock ∧
        store.nodeRank child < store.nodeRank node := by
  -- A child block sits at a later slot than its parent, so its rank is lower.
  have climbs : ∀ (child : ForkChoiceNode) (childBlock : BeaconBlock preset fork),
      child.payloadStatus = .pending → store.blocks[child.root]? = some childBlock →
      childBlock.parentRoot = node.root → store.nodeRank child < store.nodeRank node := by
    intro child childBlock pending childFound parent
    have below : childBlock.slot.toNat > block.slot.toNat :=
      UInt64.lt_iff_toNat_lt.mp (lower _ childBlock block childFound (parent ▸ found))
    have := childBlock.slot.toNat_lt
    simp only [nodeRank, childFound, found, pending, ↓reduceIte]
    split <;> omega
  by_cases gloas : .glamsterdam ≤ fork
  · by_cases pending : node.payloadStatus = .pending
    · -- A pending node has the empty node and maybe the full node of its block.
      refine ⟨_, getNodeChildren_of_pending gloas pending, fun child member => ⟨block, ?_, ?_⟩⟩ <;>
        · simp only [List.mem_cons] at member
          rcases member with rfl | member
          · simp [nodeRank, found, pending]
          · split at member
            · rw [List.mem_singleton.mp member]
              simp [nodeRank, found, pending]
            · cases member
    · obtain ⟨children, childrenOk⟩ :=
        getNodeChildren_ok_of_known (status := node.payloadStatus) found
      refine ⟨children, childrenOk, fun child member => ?_⟩
      obtain ⟨childPending, childBlock, -, childFound, parent, -⟩ :=
        (mem_getNodeChildren_of_gloas gloas pending childrenOk).mp member
      exact ⟨childBlock, childFound, climbs child childBlock childPending childFound parent⟩
  · have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
    obtain ⟨children, childrenOk⟩ :=
      getNodeChildren_ok_of_known (status := node.payloadStatus) found
    refine ⟨children, childrenOk, fun child member => ?_⟩
    obtain ⟨childPending, childBlock, childFound, parent⟩ :=
      (mem_getNodeChildren before childrenOk).mp member
    exact ⟨childBlock, childFound, climbs child childBlock childPending childFound parent⟩

/-- The walk from a held node can be computed when every held node weighs and has a tiebreaker. -/
private theorem getHeadFrom_exists (lower : store.ParentsBelow)
    {tally : Except ForkChoiceError VoteTally} {nodes : List ForkChoiceNode}
    (weighs : ∀ (n : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[n.root]? = some block → ∃ w, store.getWeight config tally n = .ok w)
    (breaks : ∀ (n : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[n.root]? = some block → ∃ t, store.tiebreaker config n = .ok t) :
    ∀ (head : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[head.root]? = some block →
      ∃ result, store.getHeadFrom config tally nodes head = .ok result := by
  intro head
  induction head using getHeadFrom.induct store with
  | _ head ih =>
  intro block found
  obtain ⟨children, childrenOk, held⟩ := getNodeChildren_held lower found
  -- Every child among the nodes weighs.
  obtain ⟨weighted, weightedOk⟩ :
      ∃ weighted, (children.filter (· ∈ nodes)).mapM (store.weighNode config tally) =
        .ok weighted := by
    refine mapM_exists_ok fun c mem => ?_
    obtain ⟨cBlock, cFound, -⟩ := held c (List.mem_filter.mp mem).1
    obtain ⟨w, wOk⟩ := weighs c cBlock cFound
    obtain ⟨t, tOk⟩ := breaks c cBlock cFound
    exact ⟨(c, w, t), weighNode_ok_iff.mpr ⟨rfl, wOk, tOk⟩⟩
  have heaviest : store.heaviestChild config tally nodes head =
      .ok (chooseHeaviest weighted) := by
    simp [heaviestChild, childrenOk, weightedOk, bind, Except.bind, pure, Except.pure]
  rw [getHeadFrom, heaviest]
  cases choice : chooseHeaviest weighted with
  | none => exact ⟨head, by simp [bind, Except.bind, pure, Except.pure]⟩
  | some child =>
    obtain ⟨key, mem, -⟩ := chooseHeaviest_some choice
    obtain ⟨c, cMem, cWeighed⟩ := mapM_ok_mem weightedOk _ mem
    obtain ⟨rfl, -, -⟩ := weighNode_ok_iff.mp cWeighed
    obtain ⟨cBlock, cFound, lowerRank⟩ := held _ (List.mem_filter.mp cMem).1
    simp only [bind, Except.bind, lowerRank, ↓reduceDIte]
    exact ih _ lowerRank cBlock cFound

/-- Every proposer score is at most `(2^64 - 1) / 100`.

It is a 64-bit product divided by 100. -/
private theorem computeProposerScore_le {config : Config} {state : BeaconState preset fork}
    {score : Gwei}
    (computed : computeProposerScore config state = .ok score) :
    score.toNat ≤ (2 ^ 64 - 1) / 100 := by
  unfold computeProposerScore calculateCommitteeFraction at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, product, -, rfl⟩ := computed
  rw [UInt64.toNat_div]
  have := product.toNat_lt
  exact Nat.div_le_div_right (by omega)

/-! ## The boosted root is zero or a held block -/

private theorem updateCheckpoints_boost (j f : Checkpoint) :
    (store.updateCheckpoints j f).proposerBoostRoot = store.proposerBoostRoot := by
  unfold updateCheckpoints
  by_cases a : store.justifiedCheckpoint.epoch < j.epoch <;>
    by_cases b : store.finalizedCheckpoint.epoch < f.epoch <;> simp [a, b]

private theorem updateUnrealizedCheckpoints_boost (j f : Checkpoint) :
    (store.updateUnrealizedCheckpoints j f).proposerBoostRoot = store.proposerBoostRoot := by
  unfold updateUnrealizedCheckpoints
  by_cases a : store.unrealizedJustifiedCheckpoint.epoch < j.epoch <;>
    by_cases b : store.unrealizedFinalizedCheckpoint.epoch < f.epoch <;> simp [a, b]

private theorem onTickPerSlot_boost {timeMs : UInt64} {after : Store preset fork}
    (ticked : store.onTickPerSlot config timeMs = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot ∨
      after.proposerBoostRoot = Vector.replicate 32 0 := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked <;>
      · simp only [pure, Except.pure, Except.ok.injEq] at ticked
        subst ticked
        simp [updateCheckpoints_boost]

private theorem storeTargetCheckpointState_boost {checks : SignatureChecks} {target : Checkpoint}
    {after : Store preset fork}
    (stored : store.storeTargetCheckpointState config checks target = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  unfold storeTargetCheckpointState at stored
  split at stored
  · simp only [pure, Except.pure, Except.ok.injEq] at stored; subst stored; rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at stored
    obtain ⟨_, _, rfl⟩ := stored; rfl

private theorem onAttestation_boost {checks : SignatureChecks}
    {attestation : Attestation preset fork}
    {isFromBlock : Bool} {after : Store preset fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, _, _, valid, _, attested⟩ := attested
  have := storeTargetCheckpointState_boost storing
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact this
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

private theorem onAttesterSlashing_boost {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} {after : Store preset fork}
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  rfl

private theorem recordBlockTimeliness_boost {root : Root} {after : Store preset fork}
    (recorded : store.recordBlockTimeliness config root = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, pure, Except.pure] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, recorded⟩ := recorded
  split at recorded
  · simp only [bind_ok_iff, Except.ok.injEq] at recorded
    obtain ⟨_, _, rfl⟩ := recorded
    rfl
  · cases recorded
    rfl

private theorem updateProposerBoostRoot_boost {head root : Root} {after : Store preset fork}
    (updated : store.updateProposerBoostRoot config head root = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot ∨ after.proposerBoostRoot = root := by
  unfold updateProposerBoostRoot at updated
  split at updated
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at updated
  simp only [bind_ok_iff, pure_bind] at updated
  obtain ⟨_, _, _, _, _, _, updated⟩ := updated
  split at updated <;> simp only [pure, Except.pure, Except.ok.injEq] at updated <;>
    subst updated <;> simp

private theorem computePulledUpTip_boost {root : Root} {after : Store preset fork}
    (pulled : store.computePulledUpTip config root = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, found, counted, countedOk, block, -, epoch, -, pulled⟩ := pulled
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled <;>
    simp [updateCheckpoints_boost, updateUnrealizedCheckpoints_boost]

/-- The boosted root of a reachable store is zero, or a held block whose parent is held.

The anchor store has none, a new slot drops it, and a block can only boost itself.

A new block's parent is held, since the store holds its state.

The other handlers keep the boost and the blocks. -/
private theorem Reachable.boostHeld {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock store) :
    store.proposerBoostRoot = Vector.replicate 32 0 ∨
      ∃ block parent, store.blocks[store.proposerBoostRoot]? = some block ∧
        store.blocks[block.parentRoot]? = some parent := by
  -- Same boost and same blocks keep the property.
  have keep : ∀ {s s' : Store preset fork}, s'.proposerBoostRoot = s.proposerBoostRoot →
      s'.blocks = s.blocks →
      (s.proposerBoostRoot = Vector.replicate 32 0 ∨ ∃ block parent,
        s.blocks[s.proposerBoostRoot]? = some block ∧ s.blocks[block.parentRoot]? = some parent) →
      (s'.proposerBoostRoot = Vector.replicate 32 0 ∨ ∃ block parent,
        s'.blocks[s'.proposerBoostRoot]? = some block ∧
          s'.blocks[block.parentRoot]? = some parent) := by
    intro s s' boost blocks holds
    rw [boost, blocks]; exact holds
  induction reachable with
  | anchor made =>
    left
    unfold getForkchoiceStore at made
    cases stateRoot : Serialization.Ssz.SszType.hashTreeRoot anchorState with
    | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
    | ok stateRoot' =>
      simp only [stateRoot, Except.mapError, bind, Except.bind] at made
      split at made
      · simp [throw, throwThe, MonadExceptOf.throw] at made
      · cases blockRoot : Serialization.Ssz.SszType.hashTreeRoot anchorBlock with
        | error e => simp [blockRoot] at made
        | ok anchorRoot =>
          simp only [blockRoot] at made
          cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
              anchorState.slot with
          | error e => simp [time] at made
          | ok timeMs =>
            simp only [time, pure, Except.pure, Except.ok.injEq] at made
            subst made
            rfl
  | tick _ ticked ih =>
    obtain ⟨tickSlot, caught, -, caughtUp, last⟩ := onTick_ok ticked
    have caughtHolds := catchUp_preserves (P := fun s : Store preset fork =>
        s.proposerBoostRoot = Vector.replicate 32 0 ∨ ∃ block parent,
          s.blocks[s.proposerBoostRoot]? = some block ∧ s.blocks[block.parentRoot]? = some parent)
      (fun holds tick => by
        rcases onTickPerSlot_boost tick with same | zero
        · exact keep same (onTickPerSlot_frame tick).2.2.2.1 holds
        · exact .inl zero) ih caughtUp
    rcases onTickPerSlot_boost last with same | zero
    · exact keep same (onTickPerSlot_frame last).2.2.2.1 caughtHolds
    · exact .inl zero
  | @block s a c src sg prior added ih =>
    cases rootOk : Serialization.Ssz.SszType.hashTreeRoot sg.message with
    | error e => simp [onBlock, rootOk, bind, Except.bind, Except.mapError] at added
    | ok blockRoot =>
    by_cases known : s.blocks.contains blockRoot
    · rw [onBlock_known rootOk known, Except.ok.injEq] at added
      subst added
      exact ih
    obtain ⟨-, pre, -, preFound, -⟩ := onBlock_insert rootOk known added
    obtain ⟨parent, parentFound⟩ := prior.known_of_blockState preFound
    simp only [onBlock, rootOk, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, -, head, -, recorded, recordedOk, timed, timedOk, boosted, boostedOk,
      pulledOk⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes recordedOk
    have tBoost := recordBlockTimeliness_boost timedOk
    have tBlocks := (recordBlockTimeliness_frame timedOk).2.1
    have bBoost := updateProposerBoostRoot_boost boostedOk
    have bBlocks := (updateProposerBoostRoot_frame boostedOk).2.1
    have pBoost := computePulledUpTip_boost pulledOk
    have pBlocks := (computePulledUpTip_frame pulledOk).2.1
    rw [pBoost, pBlocks, updateCheckpoints_boost, updateCheckpoints_blocks, bBlocks, tBlocks]
    -- Every block held before stays held, and the new block's parent is held.
    have kept : ∀ {r : Root} {b : BeaconBlock preset fork}, s.blocks[r]? = some b →
        ∃ b', (s.blocks.insert blockRoot sg.message)[r]? = some b' := by
      intro r b found
      by_cases eq : blockRoot = r
      · exact ⟨sg.message, by simp [eq]⟩
      · exact ⟨b, by simp [Std.TreeMap.getElem?_insert, eq, found]⟩
    rcases bBoost with same | inserted
    · rw [same, tBoost]
      rcases ih with zero | ⟨b, p, held, parentHeld⟩
      · exact .inl zero
      · right
        have fresh : blockRoot ≠ s.proposerBoostRoot := fun eq =>
          known (Std.TreeMap.contains_iff_mem.mpr
            (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by rw [eq, held]; rfl)))
        obtain ⟨p', parentHeld'⟩ := kept parentHeld
        exact ⟨b, p', by simp [Std.TreeMap.getElem?_insert, fresh, held], parentHeld'⟩
    · right
      obtain ⟨p', parentHeld'⟩ := kept parentFound
      exact ⟨sg.message, p', by simp [inserted], parentHeld'⟩
  | attestation _ attested ih =>
    exact keep (onAttestation_boost attested) (onAttestation_frame attested).2.1 ih
  | attesterSlashing _ slashed ih =>
    exact keep (onAttesterSlashing_boost slashed) (onAttesterSlashing_frame slashed).2.1 ih
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := recordEnvelope_frame record
    exact ih
  | @inclusionList _ _ _ heze _ _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := onInclusionList_ok heze accepted
    exact ih

/-- Before Gloas, the weight of a held node can be computed from the tally of the justified state.

The store must hold that state, with active stake at most `2 * 10^17` Gwei.

The proposer boost must fit that cap. -/
private theorem getWeight_exists (before : fork < .glamsterdam)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (boostHeld : store.proposerBoostRoot = Vector.replicate 32 0 ∨
      ∃ block parent, store.blocks[store.proposerBoostRoot]? = some block ∧
        store.blocks[block.parentRoot]? = some parent)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17)) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (bounded : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤ 2 * 10 ^ 17)
    {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) :
    ∃ weight, store.getWeight config store.justifiedTally node = .ok weight := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  obtain ⟨votes, votesOk, votesLe, -⟩ := getAttestationScore_exists (config := config) forward
    anchorSlot unknown found (BeaconState.registryWithinLimit_of_lt before state) (by omega)
  have scoreOk : store.scoreFromTally (store.tallyVotes state) node = .ok votes := votesOk
  rw [justifiedTally_of_state stateOk]
  by_cases zero : store.proposerBoostRoot = Vector.replicate 32 0
  · exact ⟨votes, by simp [getWeight, notGloas, zero, scoreOk, bind, Except.bind, pure,
      Except.pure]⟩
  obtain ⟨boostBlock, -, boostFound, -⟩ := boostHeld.resolve_left zero
  obtain ⟨d, dOk⟩ := isAncestor_ok_of_orphans_le
    (forward.reachable.parentsBelow anchorSlot unknown) found
    (fun _ _ f orphan => forward.reachable.orphans_le anchorSlot f orphan found)
    (start := ⟨_, .pending⟩) boostFound
  obtain ⟨proposer, proposerOk⟩ := computeProposerScore_exists fits positive
    (BeaconState.registryWithinLimit_of_lt before state) bounded
  have proposerLe := computeProposerScore_le proposerOk
  have getOk : store.getProposerScore config = .ok proposer := by
    simp [getProposerScore, stateOk, proposerOk, bind, Except.bind]
  have sumLt : votes.toNat + proposer.toNat < 2 ^ 64 := by omega
  cases d
  · refine ⟨votes + 0, ?_⟩
    simp [getWeight, notGloas, zero, scoreOk, dOk, bind, Except.bind, pure, Except.pure,
      Except.mapError, addChecked_of_lt (a := votes) (b := 0) (by simp; omega)]
  · refine ⟨votes + proposer, ?_⟩
    simp [getWeight, notGloas, zero, scoreOk, dOk, getOk, bind, Except.bind, pure, Except.pure,
      Except.mapError, addChecked_of_lt sumLt]

/-- Before Gloas, the head can be computed when the boosted root is zero or held. -/
private theorem getHead_exists_of_boostHeld (before : fork < .glamsterdam)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (boostHeld : store.proposerBoostRoot = Vector.replicate 32 0 ∨
      ∃ block parent, store.blocks[store.proposerBoostRoot]? = some block ∧
        store.blocks[block.parentRoot]? = some parent)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17)) {nodes : List ForkChoiceNode}
    (tree : store.getFilteredNodeTree config = .ok nodes) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (bounded : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤ 2 * 10 ^ 17) :
    ∃ head, store.getHead config = .ok head := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  obtain ⟨justified, justifiedFound⟩ := filterNodeTree_known tree
  obtain ⟨head, headOk⟩ := getHeadFrom_exists (config := config) (nodes := nodes)
    (forward.reachable.parentsBelow anchorSlot unknown)
    (fun n b f => getWeight_exists before forward anchorSlot unknown boostHeld positive fits
      stateOk bounded f)
    (fun n _ _ => ⟨0, by simp [tiebreaker, notGloas, pure, Except.pure]⟩) _ justified
    justifiedFound
  exact ⟨head, by simp [getHead, tree, notGloas, headOk, bind, Except.bind]⟩

/-- Before Gloas, the head of a store that the handlers build can be computed.

The anchor block must not be after the anchor state, and its parent root must name no held block.

The viable nodes must be computed, and the store must hold the state of the justified checkpoint.

That state must have active stake at most `2 * 10^17` Gwei.

The proposer boost must fit that cap.

An epoch must have a slot. -/
theorem getHead_exists (before : fork < .glamsterdam) {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17)) {nodes : List ForkChoiceNode}
    (tree : store.getFilteredNodeTree config = .ok nodes) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (bounded : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤ 2 * 10 ^ 17) :
    ∃ head, store.getHead config = .ok head :=
  getHead_exists_of_boostHeld before forward anchorSlot unknown
    forward.reachable.boostHeld positive fits tree stateOk bounded

/-! ## From Gloas: the payload decisions and the tiebreaker -/

/-- A held block of a forward store sits at or before its current slot, whose next slot fits.

A slot must last more than one millisecond. -/
private theorem nextSlot_of_held {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) (slots : 1 < config.SLOT_DURATION_MS)
    {root : Root} {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    ∃ current, store.getCurrentSlot config = .ok current ∧ block.slot ≤ current ∧
      addChecked block.slot 1 = .ok (block.slot + 1) := by
  have long := UInt64.lt_iff_toNat_lt.mp slots
  obtain ⟨current, currentOk, blocksLe, -⟩ :=
    forward.slots_le_current (UInt64.lt_trans (by decide) slots) anchorSlot
  have below := blocksLe root block found
  have bound := computeSlotAtTimeMs_le (mapError_ok_iff.mp currentOk)
  have fits : block.slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := UInt64.le_iff_toNat_le.mp below
    have : (2 ^ 64 - 1) / config.SLOT_DURATION_MS.toNat ≤ (2 ^ 64 - 1) / 2 :=
      Nat.div_le_div_left (by simp at long; omega) (by omega)
    simp only [UInt64.toNat_one]
    omega
  exact ⟨current, currentOk, below, addChecked_of_lt fits⟩

/-- The decision on the payload of a held node can be computed. -/
private theorem isPreviousSlotPayloadDecision_ok {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) (slots : 1 < config.SLOT_DURATION_MS)
    {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) :
    ∃ current, store.getCurrentSlot config = .ok current ∧
      addChecked block.slot 1 = .ok (block.slot + 1) ∧
      store.isPreviousSlotPayloadDecision config node = .ok
        ((block.slot + 1 == current) &&
          (node.payloadStatus == .empty || node.payloadStatus == .full)) := by
  obtain ⟨current, currentOk, -, nextOk⟩ := nextSlot_of_held forward anchorSlot slots found
  refine ⟨current, currentOk, nextOk, ?_⟩
  simp [isPreviousSlotPayloadDecision, block_ok_iff.mpr found, nextOk, currentOk, bind,
    Except.bind, pure, Except.pure, Except.mapError]

/-- From Gloas, whether to extend the payload of a held block of the previous slot can be computed.

The votes of the payload committee, the boosted block and its parent are held.

From Heze the answer on the inclusion lists of a verified payload is held. -/
private theorem shouldExtendPayload_ok {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (reachable : Reachable config anchorState anchorBlock store) {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) {current : Slot}
    (currentOk : store.getCurrentSlot config = .ok current)
    (previous : addChecked block.slot 1 = .ok current) :
    ∃ extend, store.shouldExtendPayload config gloas root = .ok extend := by
  have contains : store.blocks.contains root := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, found]; rfl
  obtain ⟨timely, timelyFound⟩ :=
    Option.isSome_iff_exists.mp (reachable.payloadTimelinessVote_isSome contains gloas)
  obtain ⟨available, availableFound⟩ :=
    Option.isSome_iff_exists.mp (reachable.payloadDataAvailabilityVote_isSome contains gloas)
  have timelyRead : ptcVotes (store.payloadTimelinessVote gloas) root = .ok timely := by
    simp [ptcVotes, timelyFound, pure, Except.pure]
  have availableRead :
      ptcVotes (store.payloadDataAvailabilityVote gloas) root = .ok available := by
    simp [ptcVotes, availableFound, pure, Except.pure]
  have timelyOk : ∀ b, ∃ v, store.payloadTimeliness gloas root b = .ok v := by
    intro b
    unfold payloadTimeliness
    rw [timelyRead]
    by_cases verified : store.isPayloadVerified gloas root <;>
      simp [verified, bind, Except.bind, pure, Except.pure]
  have availableOk : ∀ b, ∃ v, store.payloadDataAvailability gloas root b = .ok v := by
    intro b
    unfold payloadDataAvailability
    rw [availableRead]
    by_cases verified : store.isPayloadVerified gloas root <;>
      simp [verified, bind, Except.bind, pure, Except.pure]
  have satisfiedOk : ∀ heze : .hegota ≤ fork, store.isPayloadVerified gloas root = true →
      ∃ v, store.isPayloadInclusionListSatisfied heze root = .ok v := by
    intro heze verified
    obtain ⟨v, vFound⟩ := Option.isSome_iff_exists.mp
      (reachable.payloadInclusionListSatisfaction_isSome heze verified)
    unfold isPayloadInclusionListSatisfied
    simp only [vFound]
    by_cases held : store.isPayloadVerified (Nat.le_trans (by decide) heze) root <;>
      simp [held, pure, Except.pure]
  obtain ⟨t, tOk⟩ := timelyOk true
  obtain ⟨a, aOk⟩ := availableOk true
  -- The boosted block and its parent are held.
  have boosted : store.proposerBoostRoot = Vector.replicate 32 0 ∨ ∃ boostBlock,
      store.block store.proposerBoostRoot = .ok boostBlock ∧
        ∃ parent, store.block boostBlock.parentRoot = .ok parent := by
    rcases reachable.boostHeld with zero | ⟨boostBlock, parent, held, parentHeld⟩
    · exact .inl zero
    · exact .inr ⟨boostBlock, block_ok_iff.mpr held, parent, block_ok_iff.mpr parentHeld⟩
  unfold shouldExtendPayload
  simp only [block_ok_iff.mpr found, previous, currentOk, Except.mapError, bind, Except.bind,
    ne_eq, not_true_eq_false, ↓reduceIte]
  by_cases verified : store.isPayloadVerified gloas root = true
  · simp only [verified, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- From Heze the answer on the inclusion lists comes first.
    have tail : ∃ extend, (do
        let payloadIsTimely ← store.payloadTimeliness gloas root true
        let payloadDataIsAvailable ← store.payloadDataAvailability gloas root true
        if payloadIsTimely && payloadDataIsAvailable then return true
        if store.proposerBoostRoot = Vector.replicate 32 0 then return true
        let proposerBlock ← store.block store.proposerBoostRoot
        if proposerBlock.parentRoot ≠ root then return true
        store.isParentNodeFull proposerBlock : Except ForkChoiceError Bool) = .ok extend := by
      simp only [tOk, aOk, bind, Except.bind]
      split
      · exact ⟨_, rfl⟩
      rcases boosted with zero | ⟨boostBlock, boostOk, parent, parentOk⟩
      · simp [zero, pure, Except.pure]
      split
      · exact ⟨_, rfl⟩
      simp only [boostOk]
      split
      · exact ⟨_, rfl⟩
      exact ⟨parentPayloadStatus boostBlock parent == .full, by
        simp [isParentNodeFull, getParentPayloadStatus, parentOk, bind, Except.bind, pure,
          Except.pure]⟩
    split
    · rename_i heze
      obtain ⟨v, vOk⟩ := satisfiedOk heze verified
      simp only [vOk]
      split
      · exact ⟨_, rfl⟩
      · exact tail
    · exact tail
  · simp [verified, pure, Except.pure]

/-- From Gloas, the payload-status tiebreaker of a held node can be computed. -/
private theorem tiebreaker_exists_of_gloas {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) (slots : 1 < config.SLOT_DURATION_MS)
    {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) :
    ∃ t, store.tiebreaker config node = .ok t := by
  obtain ⟨current, currentOk, nextOk, decided⟩ :=
    isPreviousSlotPayloadDecision_ok forward anchorSlot slots found
  simp only [tiebreaker, gloas, ↓reduceDIte, getPayloadStatusTiebreaker, decided, bind,
    Except.bind]
  split
  · rename_i decision
    split
    · exact ⟨_, rfl⟩
    have same : block.slot + 1 = current := by
      simp only [Bool.and_eq_true, beq_iff_eq] at decision
      exact decision.1
    obtain ⟨extend, extendOk⟩ := shouldExtendPayload_ok gloas forward.reachable found currentOk
      (same ▸ nextOk)
    simp only [extendOk]
    split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-! ## The weak-head test -/

/-- The stake of any set of validators of a state is at most the effective balances of its registry.
-/
private theorem stake_le_registry (state : BeaconState preset fork) (T : Finset ValidatorIndex) :
    stake (fun v => balanceAt state v.toNat) T ≤ effectiveBalanceSum state := by
  have whole : stake (balanceAt state) (Finset.range state.validators.data.size) =
      effectiveBalanceSum state := by
    rw [effectiveBalanceSum_eq_sum_range, stake, ← List.sum_toFinset _ List.nodup_range]
    congr 1
    ext
    simp
  rw [← whole]
  unfold stake
  rw [← Finset.sum_image (f := balanceAt state) (g := UInt64.toNat)
    (fun a _ b _ same => UInt64.toNat_inj.mp same)]
  -- A position outside the registry weighs nothing.
  refine Finset.sum_le_sum_of_ne_zero fun n _ nonzero => Finset.mem_range.mpr ?_
  refine Nat.lt_of_not_le fun outside => nonzero ?_
  simp [balanceAt, Array.getElem?_eq_none outside]

/-- The equivocator weight of some validators sums the stake of each equivocator among them. -/
private theorem equivocatorWeight_eq (equivocators : List ValidatorIndex)
    (state : BeaconState preset fork) (validators : List ValidatorIndex) :
    equivocatorWeight equivocators state validators =
      ((validators.filter equivocators.contains).map fun v => balanceAt state v.toNat).sum := by
  unfold equivocatorWeight
  generalize validators.filter equivocators.contains = members
  induction members with
  | nil => rfl
  | cons v rest ih =>
    cases found : state.validators.data[v.toNat]? <;>
      simp_all [balanceAt]

/-- The weak-head test of a held block can be computed.

The store must hold the state of its justified checkpoint.

The effective balances of that state's registry must add up to at most `2 * 10^17` Gwei.

Each held state must have its registry within the limit.

Each equivocator active in a held block's state, at its epoch, needs a place in the justified state.

The committee windows and the head reads must fit. -/
private theorem isHeadWeak_exists {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (fit : config.CommitteeWindowsFit preset)
    (weights : config.HeadWeightsFit preset (2 * 10 ^ 17)) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (within : state.RegistryWithinLimit) (held : HeldRegistriesWithinLimit store)
    (supply : effectiveBalanceSum state ≤ 2 * 10 ^ 17)
    (registered : ActiveEquivocatorsRegistered store state) {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    ∃ weak, store.isHeadWeak config root = .ok weak := by
  have justifiedFound := checkpointState_ok_iff.mp stateOk
  obtain ⟨headState, headFound, -, -⟩ := forward.reachable.blockStatesFromParents found
  have headWithin := held root headState headFound
  have activeLe := (stake_le_registry state
    (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset).trans supply
  -- The reorg threshold is the proposer score of a config whose boost is that threshold.
  obtain ⟨threshold, thresholdOk⟩ := computeProposerScore_exists
    (config := { config with PROPOSER_SCORE_BOOST := config.REORG_HEAD_WEIGHT_THRESHOLD })
    ⟨by decide, weights.reorg⟩ fit.positive within activeLe
  obtain ⟨votes, votesOk, -, votesEq⟩ := getAttestationScore_exists (config := config) forward
    anchorSlot unknown (node := ⟨root, .pending⟩) found within (by omega)
  -- The committees of the block's slot read from its state, whose epoch is not past the clock.
  obtain ⟨current, currentOk, slotLe, -⟩ := nextSlot_of_held forward anchorSlot weights.slots found
  have currentLe := computeSlotAtTimeMs_le (mapError_ok_iff.mp currentOk)
  have seedRoom : (computeEpochAtSlot preset block.slot).toNat +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64 := by
    have slotNat := UInt64.le_iff_toNat_le.mp slotLe
    have epochLe : (computeEpochAtSlot preset block.slot).toNat ≤
        (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) := by
      rw [computeEpochAtSlot, UInt64.toNat_div, ← Nat.div_div_eq_div_mul]
      exact Nat.div_le_div_right (by omega)
    have := fit.seeds
    omega
  have committeeRoom : headState.validators.data.size *
      (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ headWithin))
      fit.committees
  obtain ⟨committees, mapped⟩ := mapM_exists_ok (xs := List.range
      (getCommitteeCountPerSlot headState (computeEpochAtSlot preset block.slot)).toNat)
    (f := fun index => getBeaconCommittee headState block.slot index.toUInt64) fun i mem => by
      have lt := List.mem_range.mp mem
      refine getBeaconCommittee_exists seedRoom fit.lookahead (Nat.le_trans headWithin fit.registry)
        committeeRoom fit.positive ?_
      rw [UInt64.lt_iff_toNat_lt, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt'
        (Nat.lt_trans lt (UInt64.toNat_lt _))]
      exact lt
  -- Each equivocating member is active in the block's state, so the justified state holds it.
  have known : ∀ v ∈ committees.flatMap Array.toList,
      store.equivocatingIndices.contains v = true → state.validators.data[v.toNat]?.isSome := by
    intro v mem equivocates
    obtain ⟨c, cMem, vIn⟩ := List.mem_flatMap.mp mem
    obtain ⟨i, -, cOk⟩ := mapM_ok_mem mapped c cMem
    obtain ⟨validator, vFound, active⟩ := (mem_getActiveValidatorIndices headWithin).mp
      (mem_getActiveValidatorIndices_of_getBeaconCommittee cOk (Array.mem_toList_iff.mp vIn))
    have lt := registered root block headState found headFound v (List.elem_iff.mp equivocates)
      validator vFound active
    simp [lt]
  -- The votes leave out the equivocators, and the members are distinct, so the sum is a stake.
  have distinct := getBeaconCommittees_nodup headWithin
    (committeeCount_fits (computeEpochAtSlot preset block.slot) committeeRoom).2 mapped
  set members := (committees.flatMap Array.toList).filter store.equivocatingIndices.contains
  have weightEq : equivocatorWeight store.equivocatingIndices state
      (committees.flatMap Array.toList) =
        stake (fun v => balanceAt state v.toNat) members.toFinset := by
    rw [equivocatorWeight_eq, stake, List.sum_toFinset _ (distinct.filter _)]
  have apart : Disjoint (store.supportersOf state ⟨root, .pending⟩) members.toFinset := by
    rw [Finset.disjoint_left]
    intro v supporter equivocator
    simp only [supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at supporter
    obtain ⟨⟨index, gwei⟩, ⟨-, counts⟩, rfl⟩ := supporter
    have contained := (List.mem_filter.mp (List.mem_toFinset.mp equivocator)).2
    simp only [voteCountsFor] at counts
    split at counts <;> simp_all
  have sumLe : votes.toNat + equivocatorWeight store.equivocatingIndices state
      (committees.flatMap Array.toList) ≤ 2 * 10 ^ 17 := by
    rw [votesEq, weightEq, stake, stake, ← Finset.sum_union apart]
    exact (stake_le_registry state _).trans supply
  exact ⟨_, isHeadWeak_ok_iff.mpr ⟨state, threshold, headState, block, votes, committees,
    justifiedFound, thresholdOk, headFound, found, votesOk, mapped, known, by omega, rfl⟩⟩

/-! ## From Gloas: the weight of a held node -/

/-- From Gloas, whether the boost applies can be computed, under the premises of the weak-head test.
-/
private theorem shouldApplyProposerBoost_exists {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (fit : config.CommitteeWindowsFit preset)
    (weights : config.HeadWeightsFit preset (2 * 10 ^ 17)) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (within : state.RegistryWithinLimit) (held : HeldRegistriesWithinLimit store)
    (supply : effectiveBalanceSum state ≤ 2 * 10 ^ 17)
    (registered : ActiveEquivocatorsRegistered store state) :
    ∃ apply, store.shouldApplyProposerBoost config gloas = .ok apply := by
  rcases forward.reachable.boostHeld with zero | ⟨block, parent, found, parentFound⟩
  · exact ⟨false, shouldApplyProposerBoost_of_zero gloas zero⟩
  by_cases zero : store.proposerBoostRoot = Vector.replicate 32 0
  · exact ⟨false, shouldApplyProposerBoost_of_zero gloas zero⟩
  -- The slot after each held block fits in 64 bits.
  have nextFits : ∀ (root : Root) (other : BeaconBlock preset fork),
      store.blocks[root]? = some other → other.slot.toNat + 1 < 2 ^ 64 := by
    intro root other otherFound
    obtain ⟨-, -, -, nextOk⟩ := nextSlot_of_held forward anchorSlot weights.slots otherFound
    exact (Uint64.addChecked_ok_iff.mp nextOk).1
  have fits := nextFits _ parent parentFound
  by_cases old : parent.slot.toNat + 1 < block.slot.toNat
  · exact ⟨true, shouldApplyProposerBoost_of_old_parent gloas zero found parentFound old⟩
  obtain ⟨weak, weakOk⟩ := isHeadWeak_exists forward anchorSlot unknown fit weights stateOk within
    held supply registered parentFound
  cases weak
  · exact ⟨true, shouldApplyProposerBoost_of_not_weak gloas zero found parentFound
      (by omega) fits weakOk⟩
  -- After a weak parent, every held block has its timeliness for the payload committee.
  classical
  refine ⟨decide (∀ (root : Root) (other : BeaconBlock preset fork),
      store.blocks[root]? = some other → (store.ptcTimeliness gloas)[root]? = some true →
      other.proposerIndex = parent.proposerIndex →
      other.slot.toNat + 1 = block.slot.toNat → root = block.parentRoot),
    (shouldApplyProposerBoost_eq_ok_iff gloas).mpr (.inr ⟨zero, block, parent, found,
      parentFound, fits, .inr ⟨by omega, .inr ⟨weakOk, fun root other otherFound => ?_,
        decide_eq_true_iff⟩⟩⟩)⟩
  have contains : store.blocks.contains root := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, otherFound]
    rfl
  obtain ⟨timely, timelyFound⟩ :=
    Option.isSome_iff_exists.mp (forward.reachable.ptcTimeliness_isSome contains gloas)
  exact ⟨timely, timelyFound, fun _ _ => nextFits root other otherFound⟩

/-- From Gloas, the weight of a held node can be computed from the tally of the justified state.

The premises are those of the weak-head test, and the proposer boost must fit the same cap. -/
private theorem getWeight_exists_of_gloas {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (fit : config.CommitteeWindowsFit preset)
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (weights : config.HeadWeightsFit preset (2 * 10 ^ 17)) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (within : state.RegistryWithinLimit) (held : HeldRegistriesWithinLimit store)
    (supply : effectiveBalanceSum state ≤ 2 * 10 ^ 17)
    (registered : ActiveEquivocatorsRegistered store state) {node : ForkChoiceNode}
    {block : BeaconBlock preset fork} (found : store.blocks[node.root]? = some block) :
    ∃ weight, store.getWeight config store.justifiedTally node = .ok weight := by
  obtain ⟨_, _, _, decided⟩ :=
    isPreviousSlotPayloadDecision_ok forward anchorSlot weights.slots found
  have activeLe := (stake_le_registry state
    (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset).trans supply
  obtain ⟨votes, votesOk, votesLe, -⟩ := getAttestationScore_exists (config := config) forward
    anchorSlot unknown found within (by omega)
  have scoreOk : store.scoreFromTally (store.tallyVotes state) node = .ok votes := votesOk
  obtain ⟨apply, applyOk⟩ := shouldApplyProposerBoost_exists gloas forward anchorSlot unknown fit
    weights stateOk within held supply registered
  obtain ⟨proposer, proposerOk⟩ := computeProposerScore_exists fits fit.positive within activeLe
  have proposerLe := computeProposerScore_le proposerOk
  have getOk : store.getProposerScore config = .ok proposer := by
    simp [getProposerScore, stateOk, proposerOk, bind, Except.bind]
  have sumLt : votes.toNat + proposer.toNat < 2 ^ 64 := by omega
  rw [justifiedTally_of_state stateOk]
  simp only [getWeight, gloas, ↓reduceIte, ↓reduceDIte, decided, scoreOk, applyOk, bind,
    Except.bind]
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  -- The boost applies only to a boosted block, which the store holds.
  rcases forward.reachable.boostHeld with zero | ⟨boostBlock, -, boostFound, -⟩
  · rw [shouldApplyProposerBoost_of_zero gloas zero, Except.ok.injEq] at applyOk
    subst applyOk
    simp_all
  obtain ⟨d, dOk⟩ := isAncestor_ok_of_orphans_le
    (forward.reachable.parentsBelow anchorSlot unknown) found
    (fun _ _ f orphan => forward.reachable.orphans_le anchorSlot f orphan found)
    (start := ⟨_, .pending⟩) boostFound
  cases d
  · exact ⟨votes + 0, by simp [dOk, pure, Except.pure, Except.mapError,
      addChecked_of_lt (a := votes) (b := 0) (by simp; omega)]⟩
  · exact ⟨votes + proposer, by simp [dOk, getOk, Except.mapError, addChecked_of_lt sumLt]⟩

/-- From Gloas, the head of a store that the handlers build can be computed.

The anchor block must not be after the anchor state, and its parent root must name no held block.

The viable nodes must be computed, and the store must hold the state of the justified checkpoint.

That state must have its registry within the limit.

Its effective balances must add up to at most `2 * 10^17` Gwei.

Each held state must have its registry within the limit too.

Each equivocator active in a held block's state, at its epoch, needs a place in the justified state.

The committee windows must fit, and the proposer boost and the head reads must fit that cap. -/
theorem getHead_exists_of_gloas (gloas : .glamsterdam ≤ fork)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (fit : config.CommitteeWindowsFit preset)
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (weights : config.HeadWeightsFit preset (2 * 10 ^ 17)) {nodes : List ForkChoiceNode}
    (tree : store.getFilteredNodeTree config = .ok nodes) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (within : state.RegistryWithinLimit) (held : HeldRegistriesWithinLimit store)
    (supply : effectiveBalanceSum state ≤ 2 * 10 ^ 17)
    (registered : ActiveEquivocatorsRegistered store state) :
    ∃ head, store.getHead config = .ok head := by
  cases nodes with
  | nil => exact ⟨_, getHead_of_empty gloas tree⟩
  | cons first rest =>
  -- A tree that is not empty is walked from the justified node, with every weight and tiebreaker.
  obtain ⟨justified, justifiedFound⟩ := filterNodeTree_known tree
  obtain ⟨head, headOk⟩ := getHeadFrom_exists (config := config) (nodes := first :: rest)
    (forward.reachable.parentsBelow anchorSlot unknown)
    (fun _ _ f => getWeight_exists_of_gloas gloas forward anchorSlot unknown fit fits weights
      stateOk within held supply registered f)
    (fun _ _ f => tiebreaker_exists_of_gloas gloas forward anchorSlot weights.slots f) _ justified
    justifiedFound
  exact ⟨head, by simp [getHead, tree, headOk, bind, Except.bind]⟩

end Store

end EthLib.Consensus
