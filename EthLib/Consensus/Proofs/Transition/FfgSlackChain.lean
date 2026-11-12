module

public import EthLib.Consensus.Proofs.Transition.FfgRoots

/-!
# Proofs: a chain of beacon states keeps its justified checkpoints slack-justified

The genesis checkpoint is slack-justified, and each step of a chain keeps both justified ones so.

So along a chain from the genesis state built from deposits, both are slack-justified in the model.

That genesis state exists only before Altair, so a chain whose genesis is later is out of scope.

Each step needs hypotheses on the states before and after it.

The votes of the model are those of a set of votes of the beacon chain.

The target flags and pending attestations of each state come from votes of that set.

Each block step must cast only votes of that set, with the committees of the state before it.

The set of all votes meets these hypotheses.

So the theorem bounds who voted only for a set as small as the votes of the run.

At each end of an epoch, the sets and weights must match the state for both recent epochs.

The theorem takes the sets and weights as parameters, matched where a step may justify.

One choice of them can serve a whole chain, as a set of weights holds the balances of many states.

Nothing bounds them from below, so a choice far from the active sets and balances gives little.

Another module instantiates them with the active sets and balances that the chain reads.

An empty second set, or the zero weights, makes every ordered link a slack link.

Each step asks the map from roots to blocks to keep in order the roots of consecutive slots.

It also asks the zero root before the root of slot zero.

Each justified block is then in the chain of the block of its recent epoch.

Each vote that a block step casts comes from an attestation of the block.

The block checked the indexed form of that attestation, and the check accepted.

That state and the place of the check in the block are also given.

It holds for any signature checks, with more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {β : Type*} [Preorder β]
  {V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex}
  {W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)} {genesis : β}
  {attested : Set (ValidatorIndex × AttestationData)} {block : Root → β}

/-- The votes that a block step from one state to the next casts.

They are those of the attestations of a block whose application takes the first to the second.

The committees are those of the first state.

A block accepts an attestation only when the signature checks accept its aggregate signature. -/
def blockStepVotes (config : Config) (checks : SignatureChecks)
    (forked after : ForkedBeaconState preset) : Set (ValidatorIndex × AttestationData) :=
  {vote | ∃ (engine : ExecutionEngine preset forked.fork)
    (signed : SignedBeaconBlock preset forked.fork) (validateResult : Bool)
    (state : BeaconState preset forked.fork),
    after = ⟨forked.fork, state⟩ ∧
      applySignedBlock config checks engine forked.state signed validateResult = .ok state ∧
      vote ∈ blockVotes forked.state signed.message}

/-- The state on which an attestation checks its indexed form, and the check.

Before Altair it is the state that the attestation returns, and from Altair its input. -/
private theorem processAttestation_checked {fork : Fork} {state after : BeaconState preset fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ indexed,
      getIndexedAttestation (if .altair ≤ fork then state else after) attestation =
        .ok indexed ∧
      isValidIndexedAttestation config checks (if .altair ≤ fork then state else after)
        indexed = .ok true := by
  by_cases altair : Fork.altair ≤ fork
  · unfold processAttestation at computed
    simp only [altair, ↓reduceDIte] at computed
    unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok, ensure_ok_iff] at computed
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, indexed, indexedOk, valid, validOk, _,
      validTrue, -⟩ := computed
    subst validTrue
    simp only [altair, ↓reduceIte]
    exact ⟨indexed, indexedOk, validOk⟩
  · obtain ⟨_, _, _, _, _, _, indexed, indexedOk, validOk⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) computed
    simp only [altair, ↓reduceIte]
    exact ⟨indexed, indexedOk, validOk⟩

/-- Where the attestations of a block check an indexed attestation, and on which state.

The operations start at the given state, and the attestations read the given parent slot.

From Altair an attestation is checked on the state before it.

Before Altair it is checked on the state after its pending attestation is recorded.

That state is the one that the attestation returns. -/
inductive AttestationSite (config : Config) (checks : SignatureChecks) {fork : Fork}
    (input : BeaconState preset fork) (body : BeaconBlockBody preset fork) (parentSlot : Slot) :
    BeaconState preset fork → IndexedAttestation preset fork → Prop where
  | attestation {proposersDone slashingsDone mid next : BeaconState preset fork}
      {pre post : List (Attestation preset fork)} {attestation : Attestation preset fork}
      {indexed : IndexedAttestation preset fork}
      (split : body.attestations.data.toList = pre ++ attestation :: post)
      (proposers : body.proposerSlashings.data.toList.foldlM
        (processProposerSlashing config checks) input = .ok proposersDone)
      (slashings : body.attesterSlashings.data.toList.foldlM
        (processAttesterSlashing config checks) proposersDone = .ok slashingsDone)
      (earlier : pre.foldlM (processAttestation config checks · parentSlot ·) slashingsDone =
        .ok mid)
      (processed : processAttestation config checks mid parentSlot attestation = .ok next)
      (indexedOk : getIndexedAttestation (if .altair ≤ fork then mid else next) attestation =
        .ok indexed) :
      AttestationSite config checks input body parentSlot
        (if .altair ≤ fork then mid else next) indexed

/-- A vote of a block that applies comes from an attestation whose indexed form the block checked.

The voter is among its attesters, and its data is the data of the vote.

The check ran on a state inside the block, and it accepted.

The result also says where in the block the check ran.

It holds for any signature checks.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem blockVotes_verified
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} {vote : ValidatorIndex × AttestationData}
    (computed : processBlock config checks engine state block = .ok after)
    (cast : vote ∈ blockVotes state block) :
    ∃ (input checked : BeaconState preset fork) (indexed : IndexedAttestation preset fork),
      OperationsInput config checks engine state block input ∧
      AttestationSite config checks input block.body state.latestBlockHeader.slot checked
        indexed ∧
      vote.1 ∈ indexed.attestingIndices.data.toList ∧ indexed.data = vote.2 ∧
      isValidIndexedAttestation config checks checked indexed = .ok true := by
  obtain ⟨attestation, included, dataEq, indices, indicesOk, iMem⟩ := cast
  obtain ⟨input, proposersDone, slashingsDone, _, started, proposers, slashings, folded, -⟩ :=
    processBlock_folds computed
  -- The attestation sits at a position of the attestations of the block.
  obtain ⟨pre, post, mid, next, split, earlier, processedA⟩ :=
    foldlM_ok_of_mem (Array.mem_toList_iff.mpr included) folded
  have same := getAttestingIndices_attestationsStart apart started proposers slashings folded
    (Array.mem_toList_iff.mpr included)
  -- Up to the attestation, the registry and the mixes are those where the attestations start.
  have midKept : mid.validators = slashingsDone.validators ∧
      mid.randaoMixes = slashingsDone.randaoMixes :=
    foldlM_ok_invariant (fun s => s.validators = slashingsDone.validators ∧
        s.randaoMixes = slashingsDone.randaoMixes)
      (fun _ _ _ held ok => ⟨(processAttestation_registry ok).1.trans held.1,
        (processAttestation_registry ok).2.trans held.2⟩) ⟨rfl, rfl⟩ earlier
  have kept : (if .altair ≤ fork then mid else next).validators = slashingsDone.validators ∧
      (if .altair ≤ fork then mid else next).randaoMixes = slashingsDone.randaoMixes := by
    by_cases altair : Fork.altair ≤ fork
    · simp only [altair, ↓reduceIte]
      exact midKept
    · simp only [altair, ↓reduceIte]
      exact ⟨(processAttestation_registry processedA).1.trans midKept.1,
        (processAttestation_registry processedA).2.trans midKept.2⟩
  -- The attesters at the check are those that the vote used.
  obtain ⟨indexed, indexedOk, valid⟩ := processAttestation_checked processedA
  have attestersX : getAttestingIndices (if .altair ≤ fork then mid else next) attestation =
      .ok indices :=
    ((getAttestingIndices_eq_of_eq (congrArg (·.data) kept.1)
      (congrArg (·.elements) kept.2) attestation).trans same).trans indicesOk
  obtain ⟨indexed', indexedOk', listed, indexedData, -⟩ :=
    getIndexedAttestation_of_getAttestingIndices attestersX
  have indexedEq : indexed' = indexed := Except.ok.inj (indexedOk'.symm.trans indexedOk)
  subst indexedEq
  refine ⟨input, _, indexed', started,
    .attestation split proposers slashings earlier processedA indexedOk, ?_, ?_, valid⟩
  · rw [listed]
    simpa using iMem
  · rw [indexedData, ← dataEq]

/-- A vote that a block step casts comes from an attestation whose indexed form the block checked.

The step applies a signed block, and the check ran inside that block and accepted.

The voter is among its attesters, and its data is the data of the vote.

It holds for any signature checks.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem blockStepVotes_verified
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {forked after : ForkedBeaconState preset} {vote : ValidatorIndex × AttestationData}
    (cast : vote ∈ blockStepVotes config checks forked after) :
    ∃ (engine : ExecutionEngine preset forked.fork)
      (signed : SignedBeaconBlock preset forked.fork) (validateResult : Bool)
      (state input checked : BeaconState preset forked.fork)
      (indexed : IndexedAttestation preset forked.fork),
      after = ⟨forked.fork, state⟩ ∧
      applySignedBlock config checks engine forked.state signed validateResult = .ok state ∧
      OperationsInput config checks engine forked.state signed.message input ∧
      AttestationSite config checks input signed.message.body
        forked.state.latestBlockHeader.slot checked indexed ∧
      vote.1 ∈ indexed.attestingIndices.data.toList ∧ indexed.data = vote.2 ∧
      isValidIndexedAttestation config checks checked indexed = .ok true := by
  obtain ⟨engine, signed, validateResult, state, afterEq, applied, voted⟩ := cast
  obtain ⟨-, processed, -⟩ := applySignedBlock_ok applied
  obtain ⟨input, checked, indexed, started, site, signs, dataEq, valid⟩ :=
    blockVotes_verified apart processed voted
  exact ⟨engine, signed, validateResult, state, input, checked, indexed, afterEq, applied,
    started, site, signs, dataEq, valid⟩

/-- The properties of a state that the steps of a chain keep.

The state keeps the invariant of valid blocks.

In the first two epochs, its two justified checkpoints are equal.

Once justification runs, its previous justified epoch is below its previous epoch.

Its target flags and pending attestations come from votes of a set for their links.

Its justified checkpoints are below the roots it records from their epochs on.

Its two justified checkpoints are slack-justified in the model, for the votes of that set. -/
structure SlackChainInvariant (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)) (genesis : β)
    (attested : Set (ValidatorIndex × AttestationData)) (block : Root → β)
    (forked : ForkedBeaconState preset) : Prop where
  /-- The invariant of valid blocks. -/
  invariant : Invariant forked.state
  /-- In the first two epochs, the two justified checkpoints are equal. -/
  early : JustifiedEarly forked.state
  /-- Once justification runs, the previous justified epoch is below the previous epoch. -/
  separated : JustifiedSeparated forked.state
  /-- From Altair, each target flag comes from a vote of the set for its link. -/
  flagsVoted : TargetFlagsVoted attested forked.state
  /-- Before Altair, each pending attestation is a vote of the set for its link. -/
  pendingVoted : PendingVoted attested forked.state
  /-- The justified checkpoints are below the roots recorded from their epochs on. -/
  roots : RootsAbove block forked.state
  /-- The two justified checkpoints are slack-justified in the model. -/
  slack : SlackJustifiedCheckpoints V U W genesis (ffgVotes block attested) block forked.state

/-- The bounds that one step of a chain needs, apart from its sets, weights and votes.

The bound on the stake is asked only of a step that moves the slot, when that slot ends an epoch.

Then the active stake of the current epoch must be more than one and a half increments.

The map from roots to blocks must keep in order the roots of consecutive slots after the step.

It must also keep the zero root before the root of slot zero.

The order of the blocks of the model is an assumption on the map from roots to blocks.

The meaningful choice orders the roots by the links that the states of the chains record. -/
structure SlackStepBounds (block : Root → β) (forked after : ForkedBeaconState preset) : Prop where
  /-- At the end of an epoch, the active stake is more than one and a half increments.

  It is asked only when the slot moves. -/
  large : after.state.slot ≠ forked.state.slot →
    (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt forked.state index.toNat)
        (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset
  /-- The map from roots to blocks keeps the roots of consecutive slots in order. -/
  links : ∀ link ∈ rootLinks after.state, block link.1 ≤ block link.2

/-- The hypotheses that one step of a chain needs, on the states before and after it.

They are the bounds of a step, and two conditions on the sets, weights and votes.

The set of votes must hold each vote that the step casts, when the step is a block.

At a slot that ends an epoch, the sets and weights must match the state for both recent epochs.

The rules of finalization read both as justified, even when the step keeps neither.

The meaningful sets are the active sets of the epoch and the next one.

The meaningful weights are the effective balances. -/
structure SlackStepHypotheses (config : Config) (checks : SignatureChecks)
    (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ))
    (attested : Set (ValidatorIndex × AttestationData)) (block : Root → β)
    (forked after : ForkedBeaconState preset) : Prop extends SlackStepBounds block forked after
    where
  /-- The set holds each vote that a block step casts. -/
  applied : blockStepVotes config checks forked after ⊆ attested
  /-- At the end of an epoch, the sets and weights match the state for both recent epochs. -/
  sets : after.state.slot ≠ forked.state.slot →
    (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 → ∀ current : Bool,
      TargetSetsMatch V U W block forked.state
        (if current then getCurrentEpoch forked.state else getPreviousEpoch forked.state)

/-- One step of a chain that meets the hypotheses of a step. -/
def SlackStep (config : Config) (checks : SignatureChecks)
    (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ))
    (attested : Set (ValidatorIndex × AttestationData)) (block : Root → β)
    (forked after : ForkedBeaconState preset) : Prop :=
  ChainStep config checks forked after ∧
    SlackStepHypotheses config checks V U W attested block forked after

/-- A slot step of a chain moves the slot, which the upgrades keep. -/
theorem advanceSlotAcross_slot_ne {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) :
    after.state.slot ≠ forked.state.slot := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  intro same
  have next := advanceSlot_slot advancedOk
  rw [← processUpgrades_slot upgraded, same] at next
  omega

/-- One step of a chain keeps the properties of its states.

An epoch must have at least one slot, and the buffer of roots must cover two epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes. -/
theorem SlackChainInvariant.of_chainStep (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {forked after : ForkedBeaconState preset}
    (holds : SlackChainInvariant V U W genesis attested block forked)
    (hypotheses : SlackStepHypotheses config checks V U W attested block forked after)
    (step : ChainStep config checks forked after) :
    SlackChainInvariant V U W genesis attested block after := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    have early := holds.early.of_advanceSlot advancedOk
    have moved := advanceSlotAcross_slot_ne computed
    obtain ⟨previousKept, currentKept⟩ := processUpgrades_justified upgraded
    have pending : PendingVoted attested advanced := by
      by_cases before : forked.fork < .altair
      · exact holds.pendingVoted.of_advanceSlot before apart holds.early advancedOk
      · exact fun before' => absurd before' before
    have flags := holds.flagsVoted.of_advanceSlot positive window holds.early advancedOk
    have slack := advanceSlot_slackJustifiedCheckpoints window holds.flagsVoted
      holds.pendingVoted (hypotheses.large moved) block subset_rfl
      holds.invariant.settled
      holds.separated (fun ne => by
        obtain ⟨recent | recent, -, boundary⟩ :=
          advanceSlot_getBlockRoot_currentJustified_of_ne window advancedOk ne
        · rw [recent]
          exact hypotheses.sets moved boundary false
        · rw [recent]
          exact hypotheses.sets moved boundary true)
      (fun _ => holds.roots.le_of_getBlockRoot) holds.slack advancedOk
    refine ⟨(advanceSlotAcross_invariant holds.invariant computed).1,
      early.of_processUpgrades upgraded,
      (holds.separated.of_advanceSlot holds.early holds.invariant.settled
        advancedOk).of_processUpgrades upgraded, ?_, pending.of_processUpgrades upgraded,
      RootsAbove.of_chainStep positive window holds.roots hypotheses.links (.slot computed), ?_⟩
    · by_cases altair : .altair ≤ forked.fork
      · exact TargetFlagsVoted.of_processUpgrades (forked := ⟨forked.fork, advanced⟩) altair
          flags upgraded
      · exact TargetFlagsVoted.of_processUpgrades_of_lt_altair (forked := ⟨forked.fork, advanced⟩)
          (Nat.lt_of_not_le altair) pending upgraded
    · unfold SlackJustifiedCheckpoints
      rw [previousKept, currentKept]
      exact slack
  | @block _ pre _ engine signed validateResult applied =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
    have frame := frame_processBlock blockOk
    have voteFrame := voteFrame_processBlock apart blockOk
    have sub : blockVotes pre signed.message ⊆ attested := fun vote member =>
      hypotheses.applied ⟨engine, signed, validateResult, _, rfl, applied, member⟩
    refine ⟨frame.invariant holds.invariant, holds.early.of_frame frame,
      holds.separated.of_frame frame,
      (holds.flagsVoted.of_voteFrame voteFrame).mono (Set.union_subset subset_rfl sub),
      fun before => (PendingVoted.of_processBlock before apart holds.pendingVoted blockOk).mono
        (Set.union_subset subset_rfl sub) before,
      RootsAbove.of_chainStep positive window holds.roots hypotheses.links
        (.block engine signed validateResult applied), ?_⟩
    unfold SlackJustifiedCheckpoints
    rw [frame.previousJustified, frame.currentJustified]
    exact holds.slack

/-- A chain keeps the properties of its states, from its first state to its last.

Each step must meet its hypotheses. -/
theorem SlackChainInvariant.of_chain (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {first last : ForkedBeaconState preset}
    (holds : SlackChainInvariant V U W genesis attested block first)
    (steps : Relation.ReflTransGen (SlackStep config checks V U W attested block) first last) :
    SlackChainInvariant V U W genesis attested block last := by
  induction steps with
  | refl => exact holds
  | tail _ step ih => exact ih.of_chainStep positive window apart step.2 step.1

/-- The genesis state has the properties of the states of a chain.

The genesis block of the model is the block of the zero root, the root of its checkpoints. -/
theorem initializeBeaconStateFromEth1_slackChainInvariant {fork : Fork}
    {state : BeaconState preset fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    SlackChainInvariant V U W (block (Vector.replicate 32 0)) attested block
      ⟨fork, state⟩ := by
  obtain ⟨before, holds⟩ := initializeBeaconStateFromEth1_invariant computed
  obtain ⟨slot, previous, current⟩ := initializeBeaconStateFromEth1_checkpoints computed
  refine ⟨holds, JustifiedEarly.of_initializeBeaconStateFromEth1 computed, fun later => ?_,
    fun altair => absurd altair (Nat.not_le_of_lt before), fun _ current pending member => ?_,
    RootsAbove.of_initializeBeaconStateFromEth1 computed, ?_⟩
  · simp [getCurrentEpoch, slot, computeEpochAtSlot, GENESIS_SLOT, GENESIS_EPOCH] at later
  · rw [initializeBeaconStateFromEth1_pending computed] at member
    simp at member
  · unfold SlackJustifiedCheckpoints
    rw [previous, current]
    exact ⟨JustifiedBy.root, JustifiedBy.root⟩

/-- Along a chain from genesis, the two justified checkpoints are slack-justified in the model.

Each step must meet its hypotheses.

The genesis block of the model is the block of the zero root.

The sets and weights are bounded from one side only.

So the result is meaningful for the active sets and the effective balances.

Each block step must cast only votes of the set, which holds them.

The meaningful set holds the votes that the block steps of the chain cast, and no others. -/
theorem slackJustifiedCheckpoints_of_chain (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last : ForkedBeaconState preset}
    (steps :
      Relation.ReflTransGen (SlackStep config checks V U W attested block) ⟨fork, state⟩ last) :
    SlackJustifiedCheckpoints V U W (block (Vector.replicate 32 0)) (ffgVotes block attested) block
      last.state :=
  (SlackChainInvariant.of_chain positive window apart
    (initializeBeaconStateFromEth1_slackChainInvariant computed) steps).slack

/-- Along a run of steps of a chain from genesis, the two justified checkpoints are slack-justified.

Each step must meet its hypotheses when a run from genesis reaches it and it reaches the last state.

That is every step between the two, on any run, not only the steps of one run.

A block that the state transition accepts is such a run.

The genesis block of the model is the block of the zero root. -/
theorem slackJustifiedCheckpoints_of_chainSteps (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last)
    (meets : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last →
      SlackStepHypotheses config checks V U W attested block forked after) :
    SlackJustifiedCheckpoints V U W (block (Vector.replicate 32 0)) (ffgVotes block attested) block
      last.state :=
  slackJustifiedCheckpoints_of_chain positive window apart computed (chainSteps_and steps meets)

end EthLib.Consensus
