module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Base.Proofs.MapM
import EthLib.Consensus.Proofs.Containers.State
import EthLib.Consensus.Proofs.ForkChoice.AttestationScores
import EthLib.Consensus.Proofs.ForkChoice.Ghost
import EthLib.Consensus.Proofs.ForkChoice.Supporters

/-!
# Proofs: the head of the fork choice can be computed

Before Gloas, the head of a store that the handlers build can be computed.

The store must hold the state of its justified checkpoint, and the viable nodes must be computed.

The active stake of that state must be at most `2 * 10^17` Gwei, so that no weight overflows.

The proposer boost must fit the same cap.

The walk weighs only children among the viable nodes, and each of them is a held block.

The votes for a held block can be read: each latest vote names a held block, whose walk succeeds.

Their sum is at most the active stake, so it stays below `2^64`.

The boosted root is zero or a held block, so its walk succeeds too.

A held child sits at a later slot than its held parent, so the walk descends and ends.

This is part of [#2060][issue], for the forks before Gloas.

[issue]: https://github.com/ethereum/EthLib/issues/2060
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- A vote for a held block supports a node. -/
private theorem getSupportedNode_exists {message : LatestMessage fork}
    {block : BeaconBlock preset fork} (found : store.blocks[message.root]? = some block) :
    ∃ node, store.getSupportedNode message = .ok node := by
  by_cases gloas : .glamsterdam ≤ fork
  · by_cases lt : block.slot < message.slot gloas
    · exact ⟨_, getSupportedNode_of_lt_slot gloas found lt⟩
    · exact ⟨_, getSupportedNode_of_same_slot gloas found (UInt64.not_lt.mp lt)⟩
  · exact ⟨_, getSupportedNode_of_lt (Nat.lt_of_not_le gloas)⟩

/-- The votes for a held node can be read from any state of small enough stake.

The registry of that state must be within its limit.

The score is at most the active stake of that state. -/
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
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset := by
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
  exact ⟨_, rfl, by rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; exact bound⟩

/-- The children of a held node can be computed.

Each child is a held node, of lower rank when parents sit below their children. -/
private theorem getNodeChildren_held (lower : store.ParentsBelow) {node : ForkChoiceNode}
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
    · obtain ⟨children, childrenOk⟩ : ∃ children, store.getNodeChildren node = .ok children := by
        simp only [getNodeChildren, gloas, pending, and_false, ↓reduceDIte, true_and]
        split
        · simp [Store.block, found, bind, Except.bind, pure, Except.pure]
        · exact ⟨_, rfl⟩
      refine ⟨children, childrenOk, fun child member => ?_⟩
      obtain ⟨childPending, childBlock, -, childFound, parent, -⟩ :=
        (mem_getNodeChildren_of_gloas gloas pending childrenOk).mp member
      exact ⟨childBlock, childFound, climbs child childBlock childPending childFound parent⟩
  · have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
    obtain ⟨children, childrenOk⟩ : ∃ children, store.getNodeChildren node = .ok children := by
      simp [getNodeChildren, gloas, pure, Except.pure]
    refine ⟨children, childrenOk, fun child member => ?_⟩
    obtain ⟨childPending, childBlock, childFound, parent⟩ :=
      (mem_getNodeChildren before childrenOk).mp member
    exact ⟨childBlock, childFound, climbs child childBlock childPending childFound parent⟩

/-- The walk from a held node can be computed when every held node weighs and has a tiebreaker.

The given nodes must be held. -/
private theorem getHeadFrom_exists (lower : store.ParentsBelow)
    {tally : Except ForkChoiceError VoteTally} {nodes : List ForkChoiceNode}
    (heldNodes : ∀ n ∈ nodes, ∃ block, store.blocks[n.root]? = some block)
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
    obtain ⟨-, cIn⟩ := List.mem_filter.mp mem
    obtain ⟨cBlock, cFound⟩ := heldNodes c (of_decide_eq_true cIn)
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
  obtain ⟨votes, votesOk, votesLe⟩ := getAttestationScore_exists (config := config) forward
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
  obtain ⟨head, headOk⟩ := getHeadFrom_exists (config := config)
    (forward.reachable.parentsBelow anchorSlot unknown)
    (fun n mem => (filterNodeTree_mem tree n mem).2.1)
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

end Store

end EthLib.Consensus
