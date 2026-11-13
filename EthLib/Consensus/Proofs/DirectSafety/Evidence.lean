module

public import EthLib.Consensus.Proofs.DirectSafety.Attestations
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Slashed validators come from evidence on the selected history

A slashed flag at the end of a run was set at its start or comes from a slashing of the run.

The walk follows the state transition operation by operation; no abstract protocol is an input.

The steps of an epoch use the generic splits of the epoch laws.

Slashings and upgrades use the slashed flags that their shared results state at each position.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Slashing operations carry evidence even when their votes were not included as attestations. -/
def _root_.EthLib.Consensus.Step.SlashingEvidence {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (key : BLSPubkey) : Prop :=
  match step with
  | .slot _ => False
  | .block _ signed _ _ =>
    (∃ sl ∈ signed.message.body.proposerSlashings.data.toList, ∃ v,
      x.state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some v ∧
      v.pubkey = key) ∨
    (∃ sl ∈ signed.message.body.attesterSlashings.data.toList, ∃ i ∈ slashingIndices sl, ∃ v,
      x.state.validators.data[i.toNat]? = some v ∧ v.pubkey = key)

/-- A block of the run carries a slashing that names `key`. -/
def _root_.EthLib.Consensus.Run.SlashingEvidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (key : BLSPubkey) : Prop :=
  ∃ x y, ∃ step : Step config checks x y, run.Contains step ∧ step.SlashingEvidence key

/-- Both header checks that a block of the run executed for one of its proposer slashings.

Each check is for `key`, the key of the proposer at the state of the check, and accepted. -/
structure HeaderCheck {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (key : BLSPubkey) extends CheckSite run where
  pre : List ProposerSlashing
  post : List ProposerSlashing
  slashing : ProposerSlashing
  checked : BeaconState preset fork
  next : BeaconState preset fork
  split : signed.message.body.proposerSlashings.data.toList = pre ++ slashing :: post
  earlier : pre.foldlM (processProposerSlashing config checks) input = .ok checked
  processed : processProposerSlashing config checks checked slashing = .ok next
  proposer : ∃ v,
    checked.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? = some v ∧
      v.pubkey = key
  first : checkHeaderSignature config checks checked key slashing.signedHeader1 = .ok ()
  second : checkHeaderSignature config checks checked key slashing.signedHeader2 = .ok ()

/-- Two different headers of one proposer at one slot, as a proposer slashing requires. -/
def ProposerConflict (slashing : ProposerSlashing) : Prop :=
  slashing.signedHeader1.message.slot = slashing.signedHeader2.message.slot ∧
    slashing.signedHeader1.message.proposerIndex =
      slashing.signedHeader2.message.proposerIndex ∧
    slashing.signedHeader1.message ≠ slashing.signedHeader2.message

-- The predicate follows public keys, so registry growth does not require a fixed index set.
private def SlashedBacked (evidence : BLSPubkey → Prop) {fork : Fork}
    (state : BeaconState preset fork) : Prop :=
  ∀ v ∈ state.validators.data.toList, v.slashed = true → evidence v.pubkey

-- Ordinary mutators cannot introduce a slashed key that lacked evidence before the mutation.
private def SlashedKept {fork post : Fork} (state : BeaconState preset fork)
    (after : BeaconState preset post) : Prop :=
  ∀ evidence, SlashedBacked evidence state → SlashedBacked evidence after

private theorem SlashedKept.refl {fork : Fork} (state : BeaconState preset fork) :
    SlashedKept state state := fun _ => id

private theorem SlashedKept.trans {f₁ f₂ f₃ : Fork} {s : BeaconState preset f₁}
    {t : BeaconState preset f₂} {u : BeaconState preset f₃}
    (one : SlashedKept s t) (two : SlashedKept t u) : SlashedKept s u :=
  fun evidence backed => two evidence (one evidence backed)

private theorem SlashedKept.of_validators {fork post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (same : after.validators.data = state.validators.data :=
      by rfl) : SlashedKept state after := by
  intro evidence backed
  simpa only [SlashedBacked, same] using backed

private theorem SlashedKept.foldlM {fork : Fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x t, step s x = .ok t → SlashedKept s t)
    {items : List α} {state after : BeaconState preset fork}
    (ok : items.foldlM step state = .ok after) : SlashedKept state after :=
  foldlM_ok_invariant (SlashedKept state)
    (fun _ _ _ before computed => before.trans (keeps _ _ _ computed)) (.refl state) ok

/-- A step keeps the keys before it and changes slashed flags only at its targets.

Each target inside the registry after the step was inside it at an earlier origin.

The step keeps the keys of the origin, and the key at each target there has evidence.

If each slashed key before the step has evidence, so does each slashed key after it. -/
private theorem SlashedBacked.of_flags {fork post : Fork} {origin state : BeaconState preset fork}
    {after : BeaconState preset post} {evidence : BLSPubkey → Prop} (target : Nat → Prop)
    (kept : validatorKeys state <+: validatorKeys after)
    (keptOrigin : validatorKeys origin <+: validatorKeys after)
    (flags : ∀ position, ¬ target position →
      slashedFlagAt after position = slashedFlagAt state position)
    (inside : ∀ position, target position → position < after.validators.data.size →
      position < origin.validators.data.size)
    (selected : ∀ position, target position → ∀ old,
      origin.validators.data[position]? = some old → evidence old.pubkey)
    (backed : SlashedBacked evidence state) : SlashedBacked evidence after := by
  intro v member slashed
  obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
  rw [Array.getElem?_toList] at found
  -- An earlier state whose keys the step keeps has evidence for the key at the same position.
  obtain ⟨earlier, prefixed, old, foundOld, evidenced⟩ : ∃ earlier : BeaconState preset fork,
      validatorKeys earlier <+: validatorKeys after ∧
        ∃ old, earlier.validators.data[position]? = some old ∧ evidence old.pubkey := by
    by_cases aimed : target position
    · have small := inside position aimed (Array.getElem?_eq_some_iff.mp found).1
      exact ⟨origin, keptOrigin, _, Array.getElem?_eq_getElem small,
        selected position aimed _ (Array.getElem?_eq_getElem small)⟩
    · have flag := flags position aimed
      rw [slashedFlagAt, slashedFlagAt, found, Option.map_some] at flag
      obtain ⟨old, foundOld, oldFlag⟩ := Option.map_eq_some_iff.mp flag.symm
      exact ⟨state, kept, old, foundOld,
        backed old (Array.mem_toList_iff.mpr (Array.mem_of_getElem? foundOld))
          (oldFlag.trans slashed)⟩
  -- The step keeps that key at its position.
  obtain ⟨current, foundCurrent, same⟩ :=
    validators_getElem?_of_validatorKeys_prefix prefixed foundOld
  obtain rfl : current = v := Option.some.inj (foundCurrent.symm.trans found)
  exact same ▸ evidenced

/-- A step that keeps the keys before it and every slashed flag keeps the evidence of each one. -/
private theorem SlashedKept.of_flags {fork post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (kept : validatorKeys state <+: validatorKeys after)
    (flags : ∀ position, slashedFlagAt after position = slashedFlagAt state position) :
    SlashedKept state after :=
  fun _ backed => .of_flags (origin := state) (fun _ => False) kept kept
    (fun position _ => flags position) (fun _ => False.elim) (fun _ => False.elim) backed

namespace SlashedKept

variable {fork : Fork} {state after : BeaconState preset fork}

private theorem setValidatorAt {position : Nat} {v old : Validator}
    (set : state.setValidatorAt position v = .ok after)
    (found : getValidatorAt state position = .ok old)
    (key : v.pubkey = old.pubkey) (flag : v.slashed = old.slashed)
    (le : ExitsOrdered state → v.exitEpoch ≤ v.withdrawableEpoch)
    (whole : MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state →
      v.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0) : SlashedKept state after :=
  SlashedKept.of_flags (frame_setValidatorAt_of_whole set found key le whole).pubkeysPrefix
    (slashed_setValidatorAt found set flag)

private theorem increaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (increaseBalance_validators ok))

private theorem decreaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (decreaseBalance_validators ok))

private theorem initiateValidatorExit {index : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config state index = .ok after) :
    SlashedKept state after :=
  SlashedKept.of_flags (frame_initiateValidatorExit ok).pubkeysPrefix
    (slashedFlag_initiateValidatorExit ok)

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v) (flag : v.slashed = false) :
    SlashedKept state after := by
  intro evidence backed current member slashed
  simp only [added, Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact backed current member slashed
  · simp [flag] at slashed

/-- A write keeps the key and the slashed flag of its validator.

Every other epoch step leaves both alone, so the generic traversal of an epoch applies.

The registry updates are among them, by the laws that the epoch traversal derives from the write.
-/
private theorem slashedKeptLaws :
    EpochFrameLaws (preset := preset) (fork := fork) fun s t => SlashedKept s t where
  refl := refl
  trans := trans
  setValidatorAt := setValidatorAt
  increaseBalance := increaseBalance
  decreaseBalance := decreaseBalance
  initiateValidatorExit := initiateValidatorExit
  addValidatorToRegistry := fun added _ =>
    append (addValidatorToRegistry_validators_eq_push added) rfl
  eth1DataVotes _ _ := of_validators
  inactivityScores _ _ := of_validators
  slashings _ _ := of_validators
  randaoMixes _ _ := of_validators
  historicalRoots _ _ := of_validators
  historicalSummaries _ _ := of_validators
  participationRecords _ := of_validators
  pendingDeposits _ _ _ := of_validators
  pendingConsolidations _ _ := of_validators
  syncCommittees _ _ _ := of_validators
  proposerLookahead _ _ := of_validators
  ptcWindow _ _ := of_validators

-- A step of a block that keeps the registry keeps the slashed flags.
private theorem keep {after : BeaconState preset fork} (_ : BlockFrame state after)
    (same : after.validators = state.validators) : SlashedKept state after :=
  of_validators (congrArg (·.data) same)

private theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    SlashedKept state after :=
  of_validators (by rw [(processJustificationAndFinalization_keeps ok).2.2.2.2.2.1])

-- From Altair the splits leave justification, the builder payments and the flag rotation to us.
private theorem processEpoch (ok : Consensus.processEpoch config checks state = .ok after) :
    SlashedKept state after := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [Consensus.processEpoch, altair, ↓reduceDIte] at ok
    obtain ⟨justified, rooted, justifiedOk, head, tail⟩ :=
      slashedKeptLaws.processEpochAltair_rotationSplit
        (fun _ paid => by rw [processBuilderPendingPayments_eq paid]; exact of_validators) ok
    exact (processJustificationAndFinalization justifiedOk).trans <| head.trans <|
      (of_validators (state := rooted)).trans tail
  · obtain ⟨justified, justifiedOk, rest⟩ :=
      slashedKeptLaws.processEpoch_split_of_lt_altair (Nat.lt_of_not_le altair) ok
    exact (processJustificationAndFinalization justifiedOk).trans rest

private theorem advanceSlot (ok : Consensus.advanceSlot config checks state = .ok after) :
    SlashedKept state after := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : SlashedKept state cached := of_validators (by rw [cachedEq])
  have second : SlashedKept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch epochedOk
    · cases epochedOk; exact refl _
  exact (first.trans second).trans of_validators

private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    SlashedKept pre.state post.val.state :=
  have frame := upgradeFrame_upgradeNext ok
  SlashedKept.of_flags frame.pubkeysPrefix frame.slashed

private theorem advanceSlotAcross {pre post : ForkedBeaconState preset}
    (ok : Consensus.advanceSlotAcross config checks pre = .ok post) :
    SlashedKept pre.state post.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  have rest := processUpgrades_induction
    (property := fun post => SlashedKept advanced post.state)
    (fun before ok => before.trans (upgradeNext ok)) (refl advanced) upgrades
  exact (advanceSlot slotOk).trans rest

end SlashedKept

/-- The steps of a block before its operations keep the slashed flags and the size of the registry.

The keys of the registry are a prefix, by the block frame of the same steps. -/
private theorem slashedKept_operationsInput {fork : Fork}
    {state input : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input) :
    SlashedKept state input ∧ input.validators.data.size = state.validators.data.size := by
  let Sized (s t : BeaconState preset fork) :=
    SlashedKept s t ∧ t.validators.data.size = s.validators.data.size
  have refl (s : BeaconState preset fork) : Sized s s := ⟨.refl _, rfl⟩
  have trans {s t u : BeaconState preset fork} (one : Sized s t) (two : Sized t u) : Sized s u :=
    ⟨one.1.trans two.1, two.2.trans one.2⟩
  have keep {s t : BeaconState preset fork} (frame : BlockFrame s t)
      (same : t.validators = s.validators) : Sized s t :=
    ⟨SlashedKept.keep frame same, congrArg (·.data.size) same⟩
  have laws := SlashedKept.slashedKeptLaws (preset := preset) (fork := fork)
  refine started.step_of Sized refl trans
    (fun _ ok => processParentExecutionPayload_step_of Sized refl trans keep
      (fun ok => ⟨laws.processWithdrawalRequest SlashedKept.keep ok,
        (sameSizes_processWithdrawalRequest ok).1⟩)
      (fun ok => ⟨laws.processConsolidationRequest SlashedKept.keep ok,
        (sameSizes_processConsolidationRequest ok).1⟩) ok)
    (fun ok => ?_)
    (fun _ ok => processBlockExecution_step_of Sized refl trans keep
      (fun ok => ⟨laws.processWithdrawals SlashedKept.keep ok, (sameSizes_processWithdrawals ok).1⟩)
      ok)
    (fun ok => ?_) (fun _ ok => ?_)
  · obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
    exact keep (frame_processBlockHeader ok) rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
    exact keep (frame_processRandao ok) rfl
  · obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
    exact keep (frame_processEth1Data ok) (by rw [← rest])

private theorem block_backed {fork : Fork} {state after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (proposers : ∀ sl ∈ block.body.proposerSlashings.data.toList, ∀ old,
      state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey)
    (attesters : ∀ sl ∈ block.body.attesterSlashings.data.toList,
      ∀ i ∈ slashingIndices sl, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  obtain ⟨keptInput, sizeInput⟩ := slashedKept_operationsInput started
  obtain ⟨proposed, slashed, attested, proposersOk, attestersOk, attestations, tail⟩ :=
    processOperations_folds_of (fun s t => SlashedKept s t) SlashedKept.refl
      (fun one two => one.trans two) (SlashedKept.slashedKeptLaws.processDeposit SlashedKept.keep)
      SlashedKept.slashedKeptLaws.processVoluntaryExit
      SlashedKept.slashedKeptLaws.processBlsToExecutionChange
      (SlashedKept.slashedKeptLaws.processExecutionRequests SlashedKept.keep)
      (fun ok => by rw [processPayloadAttestation_eq ok]; exact SlashedKept.of_validators) operated
  -- The slashings of the block change flags only at the positions that they name.
  let Named (position : Nat) : Prop :=
    (∃ sl ∈ block.body.proposerSlashings.data.toList,
      sl.signedHeader1.message.proposerIndex.toNat = position) ∨
    ∃ sl ∈ block.body.attesterSlashings.data.toList, ∃ i ∈ slashingIndices sl, i.toNat = position
  have flags (position : Nat) (outside : ¬ Named position) :
      slashedFlagAt slashed position = slashedFlagAt input position :=
    (slashedFlagAt_foldlM id slashingIndices
      (fun _ _ _ ok position => slashedFlagAt_processAttesterSlashing ok position) attestersOk
      position fun sl member i named equal => outside (.inr ⟨sl, member, i, named, equal⟩)).trans
    (slashedFlagAt_foldlM id (fun sl => [sl.signedHeader1.message.proposerIndex])
      (fun _ _ _ ok position outside => slashedFlagAt_processProposerSlashing ok position
        fun equal => outside _ List.mem_cons_self equal.symm) proposersOk
      position fun sl member i named equal =>
        outside (.inl ⟨sl, member, List.mem_singleton.mp named ▸ equal⟩))
  have kept := ((BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok)
    proposersOk).trans (BlockFrame.foldlM (fun _ _ _ ok => frame_processAttesterSlashing ok)
      attestersOk)).pubkeysPrefix
  have size : slashed.validators.data.size = state.validators.data.size := by
    rw [(foldlM_ok_steps SameSizes SameSizes.refl SameSizes.trans
        (fun _ _ _ ok => sameSizes_processAttesterSlashing ok) attestersOk).1.1,
      (foldlM_ok_steps SameSizes SameSizes.refl SameSizes.trans
        (fun _ _ _ ok => sameSizes_processProposerSlashing ok) proposersOk).1.1, sizeInput]
  -- The evidence of the block names validators before it, whose keys the block keeps.
  have slashedBacked : SlashedBacked evidence slashed :=
    .of_flags (origin := state) Named kept
      ((frame_operationsInput started).pubkeysPrefix.trans kept)
      flags (fun _ _ small => size ▸ small)
      (fun position named old found => named.elim
        (fun ⟨sl, member, equal⟩ => proposers sl member old (equal ▸ found))
        (fun ⟨sl, member, i, inIndices, equal⟩ =>
          attesters sl member i inIndices old (equal ▸ found)))
      (keptInput evidence backed)
  -- Attestations keep the registry.
  have attestedKept : SlashedKept slashed attested := SlashedKept.foldlM
    (fun _ _ _ ok => SlashedKept.of_validators (by rw [(processAttestation_registry ok).1]))
    attestations
  have operatedBacked := (attestedKept.trans tail) evidence slashedBacked
  -- From Altair the sync aggregate follows, and it keeps the slashed flags.
  split at synced
  · exact SlashedKept.slashedKeptLaws.processSyncAggregate synced evidence operatedBacked
  · cases synced
    exact operatedBacked

/-- A validator of the state with the key is slashed. -/
def SlashedAt {fork : Fork} (state : BeaconState preset fork) (key : BLSPubkey) : Prop :=
  ∃ v ∈ state.validators.data.toList, v.pubkey = key ∧ v.slashed = true

/-- A slashed validator of the last state has a slashed key at the first state of the run.

Otherwise a block of the run carries a slashing that names its key.

The key is read in the registry before that block.

The run can start at any state. -/
theorem _root_.EthLib.Consensus.Run.slashed_evidence {x a : ForkedBeaconState preset}
    (run : Run config checks x a)
    (v : Validator) (member : v ∈ a.state.validators.data.toList) (slashed : v.slashed = true) :
    SlashedAt x.state v.pubkey ∨ run.SlashingEvidence v.pubkey := by
  have backed : SlashedBacked (fun k => SlashedAt x.state k ∨ run.SlashingEvidence k)
      a.state := by
    clear member slashed v
    induction run with
    | nil => exact fun current member flag => .inl ⟨current, member, rfl, flag⟩
    | snoc pre step ih =>
      rename_i middle last
      have inherited : SlashedBacked
          (fun k => SlashedAt x.state k ∨ (pre.snoc step).SlashingEvidence k) middle.state := by
        intro current member flag
        refine (ih current member flag).imp_right ?_
        rintro ⟨u, w, occurrence, contained, evidence⟩
        exact ⟨u, w, occurrence, .earlier contained step, evidence⟩
      cases step with
      | slot ok => exact SlashedKept.advanceSlotAcross ok _ inherited
      | block engine signed due ok =>
        apply block_backed (applySignedBlock_ok ok).2.1 _ inherited
        · intro sl member old found
          exact .inr ⟨_, _, .block engine signed due ok, .last pre _,
            Or.inl ⟨sl, member, old, found, rfl⟩⟩
        · intro sl member i inIndices old found
          exact .inr ⟨_, _, .block engine signed due ok, .last pre _,
            Or.inr ⟨sl, member, i, inIndices, old, found, rfl⟩⟩
  exact backed v member slashed

/-- A block of the run that applied an attester slashing checked both of its attestations.

Both checks accepted, and the data of the two attestations are slashable.

Take an index of the slashing and its validator in the registry before the block.

Each attestation then has an index that holds the key of that validator at the state of the check.
-/
theorem _root_.EthLib.Consensus.Run.attestationChecks_of_attesterSlashing
    {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {fork : Fork} {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, before⟩ = false}
    {applied : applySignedBlock config checks engine before signed true = .ok after}
    (member : run.Contains (.block engine signed due applied))
    {slashing : AttesterSlashing preset fork}
    (included : slashing ∈ signed.message.body.attesterSlashings.data.toList)
    {i : ValidatorIndex} (named : i ∈ slashingIndices slashing) {v : Validator}
    (found : before.validators.data[i.toNat]? = some v) :
    ∃ one two : AttestationCheck run v.pubkey,
      one.indexed.data = slashing.attestation1.data ∧
      two.indexed.data = slashing.attestation2.data ∧
      isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data =
        true := by
  obtain ⟨_, processed, _⟩ := applySignedBlock_ok applied
  obtain ⟨input, _, _, _, started, proposers, slashings, -⟩ := processBlock_folds processed
  -- The slashing sits at a position of the attester slashings of the block.
  obtain ⟨pre, post, checked, next, split, earlier, processedS⟩ :=
    foldlM_ok_of_mem included slashings
  have site (indexed : IndexedAttestation preset fork)
      (which : indexed = slashing.attestation1 ∨ indexed = slashing.attestation2) :
      AttestationSite config checks input signed.message.body before.latestBlockHeader.slot
        checked indexed :=
    .slashing split proposers earlier processedS which
  -- The validator at the index keeps its key from the state before the block to the check.
  obtain ⟨current, foundCurrent, currentKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix
      ((frame_operationsInput started).toFrame.trans
        (site _ (.inl rfl)).frame).pubkeysPrefix found
  -- The index is in both attestations, because the slashed indices are those in both.
  unfold slashingIndices at named
  obtain ⟨first, second⟩ := List.mem_filter.mp (mem_sortedSet.mp named)
  have inSecond := of_decide_eq_true second
  -- Both attestations are checked at the state where the slashing runs.
  obtain ⟨conflict, oneOk, twoOk⟩ := processAttesterSlashing_checks processedS
  exact ⟨⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩, checked,
      slashing.attestation1, site _ (.inl rfl),
      ⟨i, first, current, foundCurrent, currentKey⟩, oneOk⟩,
    ⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩, checked,
      slashing.attestation2, site _ (.inr rfl),
      ⟨i, inSecond, current, foundCurrent, currentKey⟩, twoOk⟩, rfl, rfl, conflict⟩

/-- A block of the run that applied a proposer slashing checked both of its headers.

The checks are for the key of the proposer in the registry before the block, and accepted.

The two headers conflict. -/
theorem _root_.EthLib.Consensus.Run.headerCheck_of_proposerSlashing
    {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {fork : Fork} {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, before⟩ = false}
    {applied : applySignedBlock config checks engine before signed true = .ok after}
    (member : run.Contains (.block engine signed due applied))
    {slashing : ProposerSlashing}
    (included : slashing ∈ signed.message.body.proposerSlashings.data.toList) {v : Validator}
    (found : before.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? =
      some v) :
    ∃ c : HeaderCheck run v.pubkey, c.slashing = slashing ∧ ProposerConflict slashing := by
  obtain ⟨_, processed, _⟩ := applySignedBlock_ok applied
  obtain ⟨input, _, _, _, started, proposers, -⟩ := processBlock_folds processed
  -- The slashing sits at a position of the proposer slashings of the block.
  obtain ⟨pre, post, checked, next, split, earlier, processedP⟩ :=
    foldlM_ok_of_mem included proposers
  have frame : Frame before checked :=
    (frame_operationsInput started).toFrame.trans
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) earlier).toFrame
  obtain ⟨current, foundCurrent, currentKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix frame.pubkeysPrefix found
  obtain ⟨slotEq, indexEq, differ, proposer, proposerOk, -, oneOk, twoOk⟩ :=
    processProposerSlashing_checks processedP
  -- The validator that the check reads is the one that the key reaches.
  have same : proposer = current := Option.some.inj
    ((getValidator_eq_ok_iff.mp proposerOk).symm.trans foundCurrent)
  have key : proposer.pubkey = v.pubkey := same ▸ currentKey
  rw [key] at oneOk twoOk
  exact ⟨⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩, pre, post,
    slashing, checked, next, split, earlier, processedP, ⟨current, foundCurrent, currentKey⟩,
    oneOk, twoOk⟩, rfl, slotEq, indexEq, differ⟩

end EthLib.Consensus.DirectSafety
