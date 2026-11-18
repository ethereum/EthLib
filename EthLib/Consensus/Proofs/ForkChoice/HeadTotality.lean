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

/-- The balances of the unslashed active list sum to at most the active stake.

The registry must stay within the limit of the preset, so that the positions keep their value. -/
private theorem unslashedActiveBalances_sum_le {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) :
    ((unslashedActiveBalances state).map (·.2.toNat)).sum ≤
      stake (fun v => balanceAt state v.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset := by
  classical
  set p : Validator × ℕ → Bool := fun x =>
    isActiveValidator x.1 (getCurrentEpoch state) && !x.1.slashed with hp
  set M := state.validators.data.toList.zipIdx.filter p with hM
  have shape : unslashedActiveBalances state =
      M.map fun x => (x.2.toUInt64, x.1.effectiveBalance) := by
    simp only [unslashedActiveBalances, hM, hp]
    generalize state.validators.data.toList.zipIdx = l
    induction l with
    | nil => rfl
    | cons x rest ih =>
      by_cases h : (isActiveValidator x.1 (getCurrentEpoch state) && !x.1.slashed) = true
      · simp only [List.filterMap_cons, List.filter_cons, h, ↓reduceIte, List.map_cons, ih]
      · simp only [Bool.not_eq_true] at h
        simp only [List.filterMap_cons, List.filter_cons, h, Bool.false_eq_true, ↓reduceIte, ih]
  have inM : ∀ x ∈ M, state.validators.data[x.2]? = some x.1 := fun x mem => by
    have := (List.mem_filter.mp mem).1
    simpa using List.mem_zipIdx_iff_getElem?.mp this
  have ltM : ∀ x ∈ M, x.2 < state.validators.data.size := fun x mem => by
    simpa using (Array.getElem?_eq_some_iff.mp (inM x mem)).1
  -- Each entry's balance is the balance of its index.
  have values : (unslashedActiveBalances state).map (·.2.toNat) =
      ((unslashedActiveBalances state).map (·.1)).map fun v => balanceAt state v.toNat := by
    rw [shape, List.map_map, List.map_map, List.map_map]
    refine List.map_congr_left fun x mem => ?_
    simp [balanceAt, toNat_toUInt64_of_lt within (ltM x mem), inM x mem]
  have nodup : ((unslashedActiveBalances state).map (·.1)).Nodup := by
    rw [shape, List.map_map]
    have snd : (M.map Prod.snd).Nodup :=
      (show (state.validators.data.toList.zipIdx.map Prod.snd).Nodup by
        rw [List.zipIdx_map_snd]; exact List.nodup_range').sublist
        (List.filter_sublist.map _)
    have : (M.map fun x => x.2.toUInt64) = (M.map Prod.snd).map Nat.toUInt64 := by
      simp [List.map_map, Function.comp_def]
    rw [show ((fun x : ValidatorIndex × Gwei => x.1) ∘
        fun x : Validator × ℕ => (x.2.toUInt64, x.1.effectiveBalance)) =
      fun x => x.2.toUInt64 from rfl, this]
    refine snd.map_on fun a ha b hb same => ?_
    obtain ⟨x, xm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, ym, rfl⟩ := List.mem_map.mp hb
    rw [← toNat_toUInt64_of_lt within (ltM x xm), ← toNat_toUInt64_of_lt within (ltM y ym), same]
  rw [values, ← List.sum_toFinset _ nodup]
  refine stake_mono (w := fun v : ValidatorIndex => balanceAt state v.toNat) fun v member => ?_
  obtain ⟨validator, found, active, -⟩ :=
    (mem_unslashedActiveBalances_iff within).mp (List.mem_toFinset.mp member)
  exact List.mem_toFinset.mpr
    ((mem_getActiveValidatorIndices within).mpr ⟨validator, found, active⟩)


namespace Store

variable {config : Config} {store : Store preset fork}

/-- Before Gloas, the votes for a held node can be read from any state of small enough stake.

The score is at most the active stake of that state. -/
private theorem getAttestationScore_exists (before : fork < .glamsterdam)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) {state : BeaconState preset fork}
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
    obtain ⟨d, dOk⟩ := isAncestor_ok_of_orphans_le
      (forward.reachable.parentsBelow anchorSlot unknown) found
      (fun _ _ f orphan => forward.reachable.orphans_le anchorSlot f orphan found)
      (start := ⟨_, .pending⟩) votedFound
    exact ⟨d, by rw [getSupportedNode_of_lt before]; exact dOk⟩
  -- The counted balances sum to at most all the balances of the list.
  have le : ∀ entries : List (ValidatorIndex × Gwei),
      (entries.map fun entry =>
        if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum ≤
        (entries.map (·.2.toNat)).sum := by
    intro entries
    induction entries with
    | nil => simp
    | cons entry rest ih =>
      simp only [List.map_cons, List.sum_cons]
      split <;> omega
  have bound := (le _).trans
    (unslashedActiveBalances_sum_le (BeaconState.registryWithinLimit_of_lt before state))
  rw [store.getAttestationScore_eq_of_checked checked]
  dsimp only
  have fits : ¬ 2 ^ 64 ≤ ((unslashedActiveBalances state).map fun entry =>
      if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum := by omega
  simp only [fits, ↓reduceIte]
  exact ⟨_, rfl, by rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; exact bound⟩

/-- Before Gloas, the walk from a pending held node can be computed when every held node weighs.

The given nodes must be pending held blocks. -/
private theorem getHeadFrom_exists (before : fork < .glamsterdam) (lower : store.ParentsBelow)
    {tally : Except ForkChoiceError VoteTally} {nodes : List ForkChoiceNode}
    (heldNodes : ∀ n ∈ nodes, n.payloadStatus = .pending ∧
      ∃ block, store.blocks[n.root]? = some block)
    (weighs : ∀ (n : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[n.root]? = some block → ∃ w, store.getWeight config tally n = .ok w) :
    ∀ (head : ForkChoiceNode) (block : BeaconBlock preset fork),
      head.payloadStatus = .pending → store.blocks[head.root]? = some block →
      ∃ result, store.getHeadFrom config tally nodes head = .ok result := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  intro head
  induction head using getHeadFrom.induct store with
  | _ head ih =>
  intro block pending found
  -- The children are pure before Gloas.
  obtain ⟨children, childrenOk⟩ : ∃ children, store.getNodeChildren head = .ok children := by
    simp [getNodeChildren, notGloas, pure, Except.pure]
  -- Every child among the nodes weighs.
  obtain ⟨weighted, weightedOk⟩ :
      ∃ weighted, (children.filter (· ∈ nodes)).mapM (store.weighNode config tally) =
        .ok weighted := by
    refine mapM_exists_ok fun c mem => ?_
    obtain ⟨-, cIn⟩ := List.mem_filter.mp mem
    obtain ⟨-, cBlock, cFound⟩ := heldNodes c (of_decide_eq_true cIn)
    obtain ⟨w, wOk⟩ := weighs c cBlock cFound
    refine ⟨(c, w, 0), ?_⟩
    simp [weighNode, wOk, tiebreaker, notGloas, bind, Except.bind, pure, Except.pure]
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
    obtain ⟨cChild, cIn⟩ := List.mem_filter.mp cMem
    obtain ⟨cPending, cBlock, cFound, cParent⟩ := (mem_getNodeChildren before childrenOk).mp cChild
    -- The child sits above its parent, so its rank is lower.
    have below : cBlock.slot.toNat > block.slot.toNat :=
      UInt64.lt_iff_toNat_lt.mp (lower _ cBlock block cFound (cParent ▸ found))
    have lowerRank : store.nodeRank child < store.nodeRank head := by
      simp only [nodeRank, cFound, found, pending, ↓reduceIte]
      rw [cPending]; simp only [↓reduceIte]
      have := cBlock.slot.toNat_lt
      have := block.slot.toNat_lt
      omega
    simp only [bind, Except.bind, lowerRank, ↓reduceDIte]
    exact ih child lowerRank cBlock cPending cFound

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

private theorem recordBlockTimeliness_boost (before : fork < .glamsterdam) {root : Root}
    {after : Store preset fork}
    (recorded : store.recordBlockTimeliness config root = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot ∧ after.blocks = store.blocks := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := recorded
  exact ⟨rfl, rfl⟩

private theorem updateProposerBoostRoot_boost {head root : Root} {after : Store preset fork}
    (updated : store.updateProposerBoostRoot config head root = .ok after) :
    (after.proposerBoostRoot = store.proposerBoostRoot ∨ after.proposerBoostRoot = root) ∧
      after.blocks = store.blocks := by
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

/-- Before Gloas, the boosted root of a reachable store is zero or a held block.

The anchor store has none, a new slot drops it, and a block can only boost itself.

The other handlers keep the boost and the blocks. -/
private theorem Reachable.boostHeld (before : fork < .glamsterdam)
    {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock store) :
    store.proposerBoostRoot = Vector.replicate 32 0 ∨
      ∃ block, store.blocks[store.proposerBoostRoot]? = some block := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  -- Same boost and same blocks keep the property.
  have keep : ∀ {s s' : Store preset fork}, s'.proposerBoostRoot = s.proposerBoostRoot →
      s'.blocks = s.blocks →
      (s.proposerBoostRoot = Vector.replicate 32 0 ∨
        ∃ block, s.blocks[s.proposerBoostRoot]? = some block) →
      (s'.proposerBoostRoot = Vector.replicate 32 0 ∨
        ∃ block, s'.blocks[s'.proposerBoostRoot]? = some block) := by
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
        s.proposerBoostRoot = Vector.replicate 32 0 ∨
          ∃ block, s.blocks[s.proposerBoostRoot]? = some block)
      (fun holds tick => by
        rcases onTickPerSlot_boost tick with same | zero
        · exact keep same (onTickPerSlot_frame tick).2.2.2.1 holds
        · exact .inl zero) ih caughtUp
    rcases onTickPerSlot_boost last with same | zero
    · exact keep same (onTickPerSlot_frame last).2.2.2.1 caughtHolds
    · exact .inl zero
  | @block s a c src sg _ added ih =>
    unfold onBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨blockRoot, -, added⟩ := added
    split at added
    · simp only [pure, Except.pure, Except.ok.injEq] at added
      subst added; exact ih
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, -, head, -, recorded, recordedOk, timed, timedOk, boosted, boostedOk,
      pulledOk⟩ := added
    unfold recordBlockPtcVotes at recordedOk
    simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    obtain ⟨tBoost, tBlocks⟩ := recordBlockTimeliness_boost before timedOk
    obtain ⟨bBoost, bBlocks⟩ := updateProposerBoostRoot_boost boostedOk
    have pBoost := computePulledUpTip_boost pulledOk
    have pBlocks := (computePulledUpTip_frame pulledOk).2.1
    rw [pBoost, pBlocks, updateCheckpoints_boost, updateCheckpoints_blocks, bBlocks, tBlocks]
    rcases bBoost with same | inserted
    · rw [same, tBoost]
      rcases ih with zero | ⟨b, held⟩
      · exact .inl zero
      · right
        by_cases eq : blockRoot = s.proposerBoostRoot
        · exact ⟨sg.message, by simp [eq]⟩
        · exact ⟨b, by simp [Std.TreeMap.getElem?_insert, eq, held]⟩
    · right
      exact ⟨sg.message, by simp [inserted]⟩
  | attestation _ attested ih =>
    exact keep (onAttestation_boost attested) (onAttestation_frame attested).2.1 ih
  | attesterSlashing _ slashed ih =>
    exact keep (onAttesterSlashing_boost slashed) (onAttesterSlashing_frame slashed).2.1 ih
  | payloadAttestation => exact absurd ‹.glamsterdam ≤ fork› notGloas
  | envelope => exact absurd ‹.glamsterdam ≤ fork› notGloas
  | inclusionList =>
    exact absurd (Nat.le_trans (by decide) ‹.hegota ≤ fork›) notGloas

/-- Before Gloas, the weight of a held node can be computed from the tally of the justified state.

The store must hold that state, with active stake at most `2 * 10^17` Gwei.

The proposer boost must fit that cap. -/
private theorem getWeight_exists (before : fork < .glamsterdam)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (boostHeld : store.proposerBoostRoot = Vector.replicate 32 0 ∨
      ∃ block, store.blocks[store.proposerBoostRoot]? = some block)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17)) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (bounded : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤ 2 * 10 ^ 17)
    {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) :
    ∃ weight, store.getWeight config store.justifiedTally node = .ok weight := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  obtain ⟨votes, votesOk, votesLe⟩ := getAttestationScore_exists (config := config) before forward
    anchorSlot unknown found (state := state) (by omega)
  have scoreOk : store.scoreFromTally (store.tallyVotes state) node = .ok votes := votesOk
  rw [justifiedTally_of_state stateOk]
  by_cases zero : store.proposerBoostRoot = Vector.replicate 32 0
  · exact ⟨votes, by simp [getWeight, notGloas, zero, scoreOk, bind, Except.bind, pure,
      Except.pure]⟩
  obtain ⟨boostBlock, boostFound⟩ := boostHeld.resolve_left zero
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
      ∃ block, store.blocks[store.proposerBoostRoot]? = some block)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17)) {nodes : List ForkChoiceNode}
    (tree : store.getFilteredNodeTree config = .ok nodes) {state : BeaconState preset fork}
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    (bounded : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤ 2 * 10 ^ 17) :
    ∃ head, store.getHead config = .ok head := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  obtain ⟨justified, justifiedFound⟩ := filterNodeTree_known tree
  have heldNodes : ∀ n ∈ nodes, n.payloadStatus = .pending ∧
      ∃ block, store.blocks[n.root]? = some block := fun n mem => by
    obtain ⟨-, held, -⟩ := filterNodeTree_mem tree n mem
    rcases filterNodeTree_parent before rfl tree n mem with ⟨-, rfl | ⟨pending, -⟩⟩
    · exact ⟨rfl, held⟩
    · exact ⟨pending, held⟩
  obtain ⟨head, headOk⟩ := getHeadFrom_exists (config := config) before
    (forward.reachable.parentsBelow anchorSlot unknown) heldNodes
    (fun n b f => getWeight_exists before forward anchorSlot unknown boostHeld positive fits
      stateOk bounded f) _ justified rfl justifiedFound
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
    (forward.reachable.boostHeld before) positive fits tree stateOk bounded

end Store

end EthLib.Consensus
