module

public import EthLib.Consensus.Proofs.DirectSafety.Attestations
public import EthLib.Consensus.Proofs.DirectSafety.Fields
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Slashed validators come from evidence on the selected history

A slashed flag in a reachable registry must originate in a slashing operation of the run.

The walk follows the state transition operation by operation; no abstract protocol is an input.

The steps of an epoch use the generic traversal of the epoch laws.
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

namespace SlashedKept

variable {fork : Fork} {state after : BeaconState preset fork}

private theorem setValidatorAt {position : Nat} {v old : Validator}
    (found : getValidatorAt state position = .ok old)
    (key : v.pubkey = old.pubkey) (flag : v.slashed = old.slashed)
    (set : state.setValidatorAt position v = .ok after) : SlashedKept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  intro evidence backed current member slashed
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.toList_set] at member
  rcases List.mem_or_eq_of_mem_set member with member | equal
  · exact backed current member slashed
  · subst current
    rw [key]
    apply backed old
    · rw [← oldEq]
      simp
    · rwa [flag] at slashed

private theorem setValidator {index : ValidatorIndex} {v old : Validator}
    (found : getValidator state index = .ok old)
    (key : v.pubkey = old.pubkey) (flag : v.slashed = old.slashed)
    (set : state.setValidator index v = .ok after) : SlashedKept state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) key flag
    (by rwa [← setValidator_eq_setValidatorAt])

private theorem increaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (increaseBalance_validators ok))

private theorem decreaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (decreaseBalance_validators ok))

private theorem initiateValidatorExit {index : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config state index = .ok after) :
    SlashedKept state after := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have same := (exitQueue_validators queue).1
    exact (of_validators (congrArg (·.data) same)).trans
      (setValidator (old := v) (v := { v with exitEpoch := epoch, withdrawableEpoch := withdrawal })
        (by rw [getValidator_of_validators_eq same]; exact found)
        rfl rfl set)

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
  setValidatorAt := fun set found key flag _ _ => setValidatorAt found key flag set
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

private theorem genesis {hash : Hash32} {time : UInt64} {deposits : Array Deposit}
    (ok : initializeBeaconStateFromEth1 config checks hash time deposits = .ok after) :
    SlashedBacked (fun _ => False) after := by
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    rfl⟩ := initializeBeaconStateFromEth1_ok ok
  have first := foldlM (fun _ _ _ ok => slashedKeptLaws.genesisDeposit keep ok) depositedOk
  have second := foldlM (fun _ _ _ ok => slashedKeptLaws.activateAtGenesis ok) activatedOk
  exact (first.trans second) (fun _ => False) (by simp [SlashedBacked, emptyGenesisState])

private theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    SlashedKept state after :=
  of_validators (by rw [(processJustificationAndFinalization_keeps ok).2.2.2.2.2.1])

private theorem processEpoch (ok : Consensus.processEpoch config checks state = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processEpoch at ok
  split at ok
  · obtain ⟨pending, paid, rooted, pendingOk, paidOk, middle, tail⟩ :=
      slashedKeptLaws.processEpochAltair_paymentSplit ok
    obtain ⟨justified, justifiedOk, head⟩ := slashedKeptLaws.epochBeforePayments_split pendingOk
    have paidStep : SlashedKept pending paid := by
      split at paidOk
      · rw [processBuilderPendingPayments_eq (liftAccessor_ok.mp paidOk)]
        exact of_validators
      · cases paidOk; exact refl _
    exact (processJustificationAndFinalization justifiedOk).trans <| head.trans <|
      paidStep.trans <| middle.trans <| (of_validators (state := rooted)).trans tail
  · simp only [bind_ok_iff] at ok
    obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
      slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
      rootedOk, rotated⟩ := ok
    exact (processJustificationAndFinalization justifiedOk).trans <|
      (slashedKeptLaws.processRewardsAndPenalties rewardedOk).trans <|
      (slashedKeptLaws.processRegistryUpdates registeredOk).trans <|
      (slashedKeptLaws.processSlashings slashedOk).trans <|
      (slashedKeptLaws.processEth1DataReset resetOk).trans <|
      (slashedKeptLaws.processEffectiveBalanceUpdates balancedOk).trans <|
      (slashedKeptLaws.processSlashingsReset clearedOk).trans <|
      (slashedKeptLaws.processRandaoMixesReset mixedOk).trans <|
      (slashedKeptLaws.processHistoricalRootsUpdate rootedOk).trans
        (slashedKeptLaws.processParticipationRecordUpdates rotated)


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

private theorem upgradeToElectra {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra}
    (ok : Consensus.upgradeToElectra config pre = .ok post) : SlashedKept pre post := by
  simp only [Consensus.upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := ok
  exact (of_validators (state := pre)).trans <|
    (foldlM (fun _ _ _ ok => slashedKeptLaws.queuePreActivation keep ok) queued).trans
      (foldlM (fun _ _ _ ok => slashedKeptLaws.queueCompoundingExcess keep ok) compounded)

private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    SlashedKept pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToAltair_spec upgraded).1
  case altair | bellatrix | shapella =>
    simp only [Consensus.upgradeNext, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact of_validators
  case dencun =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact upgradeToElectra upgraded
  case pectra =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToFulu_spec upgraded).1
  case fusaka =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToGloas_spec upgraded).1
  case glamsterdam =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact of_validators (upgradeHezeFields_lists _).1
  all_goals simp only [Consensus.upgradeNext] at ok; cases ok

private theorem advanceSlotAcross {pre post : ForkedBeaconState preset}
    (ok : Consensus.advanceSlotAcross config checks pre = .ok post) :
    SlashedKept pre.state post.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  have rest := processUpgrades_induction
    (property := fun post => SlashedKept advanced post.state)
    (fun before ok => before.trans (upgradeNext ok)) (refl advanced) upgrades
  exact (advanceSlot slotOk).trans rest

end SlashedKept

private theorem key_of_same_size {fork : Fork} {state after : BeaconState preset fork}
    (kept : validatorKeys state <+: validatorKeys after)
    (size : after.validators.data.size = state.validators.data.size)
    {i : Nat} {v : Validator} (found : after.validators.data[i]? = some v) :
    ∃ old, state.validators.data[i]? = some old ∧ old.pubkey = v.pubkey := by
  -- The registry has the same size, so the position was filled before, with the same key.
  have before : i < state.validators.data.size :=
    size ▸ (Array.getElem?_eq_some_iff.mp found).1
  have atOld : state.validators.data[i]? = some state.validators.data[i] := by simp [before]
  obtain ⟨current, foundCurrent, same⟩ := validators_getElem?_of_validatorKeys_prefix kept atOld
  obtain rfl : current = v := Option.some.inj (foundCurrent.symm.trans found)
  exact ⟨_, atOld, same.symm⟩

private theorem slashValidator_backed {fork : Fork} {state after : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state index whistleblower = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ old, state.validators.data[index.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  obtain ⟨exited, validator, withdrawable, marked, _, _, slashings, lowered, _, _, raised, last,
    exitedOk, found, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok ok
  have oldBacked := SlashedKept.initiateValidatorExit exitedOk evidence backed
  -- Only the selected validator can acquire a flag at this write.
  have markedBacked : SlashedBacked evidence marked := by
    obtain ⟨inside, rfl⟩ := setValidator_ok markedOk
    intro v member flag
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.toList_set] at member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact oldBacked v member flag
    · obtain ⟨old, atOld, same⟩ := key_of_same_size
        (frame_initiateValidatorExit exitedOk).pubkeysPrefix
        (sameSizes_initiateValidatorExit exitedOk).1 (getValidator_eq_ok_iff.mp found)
      exact same ▸ selected old atOld
  have rest : SlashedKept marked last :=
    (SlashedKept.of_validators (after := { marked with slashings })).trans <|
    (SlashedKept.decreaseBalance loweredOk).trans <|
    (SlashedKept.increaseBalance raisedOk).trans (SlashedKept.increaseBalance lastOk)
  have lastBacked := rest evidence markedBacked
  rw [done]
  split <;> exact lastBacked

private theorem proposerSlashing_backed {fork : Fork} {state after : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ old,
      state.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey) : SlashedBacked evidence after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator_backed slashed evidence backed selected

private theorem attesterSlashing_backed {fork : Fork} {state after : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ i ∈ slashingIndices slashing, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  have traverse (indices : List ValidatorIndex)
      (allowed : ∀ i ∈ indices, ∀ old,
        state.validators.data[i.toNat]? = some old → evidence old.pubkey)
      {start finish : BeaconState preset fork × Bool}
      (identity : validatorKeys state <+: validatorKeys start.1)
      (size : start.1.validators.data.size = state.validators.data.size)
      (backed : SlashedBacked evidence start.1)
      (ok : indices.foldlM (slashIfSlashable config) start = .ok finish) :
      SlashedBacked evidence finish.1 := by
    induction indices generalizing start with
    | nil => cases ok; exact backed
    | cons index rest ih =>
      obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
      obtain ⟨s, anySlashed⟩ := start
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
      obtain ⟨_, _, first⟩ := first
      split at first
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at first
        obtain ⟨next, slashed, rfl⟩ := first
        refine ih (fun i member => allowed i (by simp [member]))
          (identity.trans (frame_slashValidator slashed).pubkeysPrefix)
          ((sameSizes_slashValidator slashed).1.trans size) ?_ tail
        apply slashValidator_backed slashed evidence backed
        intro old found
        obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
        exact same ▸ allowed index (by simp) original originalAt
      · cases first
        exact ih (fun i member => allowed i (by simp [member])) identity size backed tail
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact traverse _ selected (List.prefix_refl _) rfl backed folded

private theorem fold_slashings_backed {fork : Fork} {α : Type}
    {step : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (indices : α → List ValidatorIndex)
    (identityStep : ∀ s x t, step s x = .ok t → validatorKeys s <+: validatorKeys t)
    (sizeStep : ∀ s x t, step s x = .ok t → SameSizes s t)
    (backedStep : ∀ s x t, step s x = .ok t → ∀ evidence,
      SlashedBacked evidence s →
      (∀ i ∈ indices x, ∀ old, s.validators.data[i.toNat]? = some old → evidence old.pubkey) →
      SlashedBacked evidence t)
    {state start finish : BeaconState preset fork} (items : List α)
    (identity : validatorKeys state <+: validatorKeys start)
    (size : start.validators.data.size = state.validators.data.size)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence start)
    (selected : ∀ x ∈ items, ∀ i ∈ indices x, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey)
    (ok : items.foldlM step start = .ok finish) : SlashedBacked evidence finish := by
  induction items generalizing start with
  | nil => cases ok; exact backed
  | cons item rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
    refine ih (identity.trans (identityStep _ _ _ first))
      ((sizeStep _ _ _ first).1.trans size) ?_
      (fun x member => selected x (by simp [member])) tail
    apply backedStep _ _ _ first evidence backed
    intro i member old found
    -- Earlier slashings preserve the index and key used by the block's original evidence.
    obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
    exact same ▸ selected item (by simp) i member original originalAt

private theorem operations_backed {fork : Fork} {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (proposers : ∀ sl ∈ body.proposerSlashings.data.toList, ∀ old,
      state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey)
    (attesters : ∀ sl ∈ body.attesterSlashings.data.toList, ∀ i ∈ slashingIndices sl, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  -- The operations after the attestations keep the slashed flags.
  obtain ⟨proposed, slashed, attested, proposersOk, attestersOk, attestations, tail⟩ :=
    processOperations_folds_of (fun s t => SlashedKept s t) SlashedKept.refl
      (fun one two => one.trans two) (SlashedKept.slashedKeptLaws.processDeposit SlashedKept.keep)
      SlashedKept.slashedKeptLaws.processVoluntaryExit
      SlashedKept.slashedKeptLaws.processBlsToExecutionChange
      (SlashedKept.slashedKeptLaws.processExecutionRequests SlashedKept.keep)
      (fun ok => by rw [processPayloadAttestation_eq ok]; exact SlashedKept.of_validators) ok
  have proposedBacked : SlashedBacked evidence proposed := by
    refine fold_slashings_backed (fun sl => [sl.signedHeader1.message.proposerIndex])
      (fun _ _ _ ok => (frame_processProposerSlashing ok).pubkeysPrefix)
      (fun _ _ _ ok => sameSizes_processProposerSlashing ok) ?_ _ (List.prefix_refl _) rfl
      evidence backed ?_ proposersOk
    · intro s sl t ok evidence backed selected
      exact proposerSlashing_backed ok evidence backed (selected _ (by simp))
    · intro sl member i inIndices
      simp only [List.mem_singleton] at inIndices
      subst i
      exact proposers sl member
  have proposedSize : SameSizes state proposed :=
    (foldlM_ok_steps SameSizes SameSizes.refl SameSizes.trans
      (fun _ _ _ ok => sameSizes_processProposerSlashing ok) proposersOk).1
  have slashedBacked := fold_slashings_backed slashingIndices
    (fun _ _ _ ok => (frame_processAttesterSlashing ok).pubkeysPrefix)
    (fun _ _ _ ok => sameSizes_processAttesterSlashing ok)
    (fun _ _ _ ok => attesterSlashing_backed ok) _
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk).pubkeysPrefix
    proposedSize.1 evidence proposedBacked attesters attestersOk
  -- Attestations keep the registry.
  have attestedKept : SlashedKept slashed attested := SlashedKept.foldlM
    (fun _ _ _ ok => SlashedKept.of_validators (by rw [(processAttestation_registry ok).1]))
    attestations
  exact (attestedKept.trans tail) evidence slashedBacked

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
  -- The evidence of the block names validators before it, and they keep their keys to its input.
  have kept := (frame_operationsInput started).pubkeysPrefix
  obtain ⟨slashedKept, size⟩ := slashedKept_operationsInput started
  have operatedBacked : SlashedBacked evidence last := by
    apply operations_backed operated evidence (slashedKept evidence backed)
    · intro sl member old found
      obtain ⟨original, originalAt, same⟩ := key_of_same_size kept size found
      exact same ▸ proposers sl member original originalAt
    · intro sl member i inIndices old found
      obtain ⟨original, originalAt, same⟩ := key_of_same_size kept size found
      exact same ▸ attesters sl member i inIndices original originalAt
  -- From Altair the sync aggregate follows, and it keeps the slashed flags.
  split at synced
  · exact SlashedKept.slashedKeptLaws.processSyncAggregate synced evidence operatedBacked
  · cases synced
    exact operatedBacked

/-- A slashed validator of the last state has a slashing in a block of the run that names its key.

The key is read in the registry before that block.

The run starts at a genesis built from deposits. -/
theorem _root_.EthLib.Consensus.Run.slashed_evidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (v : Validator) (member : v ∈ a.state.validators.data.toList) (slashed : v.slashed = true) :
    run.SlashingEvidence v.pubkey := by
  have backed : SlashedBacked run.SlashingEvidence a.state := by
    clear member slashed v
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      intro current member flag
      exact False.elim (SlashedKept.genesis ok current member flag)
    | snoc pre step ih =>
      rename_i middle last
      have inherited : SlashedBacked (pre.snoc step).SlashingEvidence middle.state := by
        intro current member flag
        obtain ⟨x, y, occurrence, contained, evidence⟩ := ih current member flag
        exact ⟨x, y, occurrence, .earlier contained step, evidence⟩
      cases step with
      | slot ok => exact SlashedKept.advanceSlotAcross ok _ inherited
      | block engine signed due ok =>
        apply block_backed (applySignedBlock_ok ok).2.1 _ inherited
        · intro sl member old found
          exact ⟨_, _, .block engine signed due ok, .last pre _,
            Or.inl ⟨sl, member, old, found, rfl⟩⟩
        · intro sl member i inIndices old found
          exact ⟨_, _, .block engine signed due ok, .last pre _,
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
