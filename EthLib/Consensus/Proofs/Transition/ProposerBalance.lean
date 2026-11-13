module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
import EthLib.Consensus.Proofs.Transition.BalanceCappedBlock
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# Proofs: what the operations and the sync aggregate of a block pay its proposer

The slashings and the attestations of a block never lower the balance of a validator they spare.

The later operations keep that balance exactly, unless they pay it a deposit or switch it.

Only a deposit to its key, before Electra, raises it at once.

Only a request to switch it to compounding credentials, from Electra, lowers it at once.

From Altair the sync aggregate pays the proposer one share for each member that signs.

That holds when the proposer has no seat in the committee.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Balances that do not fall, and balances that stay -/

/-- A state keeps each of its balances. -/
private theorem BalanceRises.refl (index : Nat) (state : BeaconState preset fork) :
    BalanceRises index state state :=
  fun earlier found => ⟨earlier, found, UInt64.le_refl _⟩

/-- Two steps that keep a balance from falling keep it from falling. -/
private theorem BalanceRises.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : BalanceRises index first second) (two : BalanceRises index second third) :
    BalanceRises index first third := by
  intro earlier found
  obtain ⟨middle, atMiddle, low⟩ := one earlier found
  obtain ⟨later, atLater, lower⟩ := two middle atMiddle
  exact ⟨later, atLater, UInt64.le_trans low lower⟩

/-- A step that keeps the balances keeps the balance at each position from falling. -/
private theorem BalanceRises.of_balances {index : Nat} (same : after.balances = state.balances) :
    BalanceRises index state after :=
  fun earlier found => ⟨earlier, by rw [same]; exact found, UInt64.le_refl _⟩

/-- A fold of steps that each keep a balance from falling keeps it. -/
private theorem BalanceRises.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ s x t, step s x = .ok t → BalanceRises index s t) {items : List α}
    (computed : items.foldlM step state = .ok after) : BalanceRises index state after :=
  (foldlM_ok_steps (BalanceRises index) (BalanceRises.refl index) BalanceRises.trans each
    computed).1

/-- A state keeps each of its balances. -/
private theorem BalanceStays.refl (index : Nat) (state : BeaconState preset fork) :
    BalanceStays index state state :=
  fun _ found => found

/-- Two steps that keep a balance keep it. -/
private theorem BalanceStays.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : BalanceStays index first second) (two : BalanceStays index second third) :
    BalanceStays index first third :=
  fun earlier found => two earlier (one earlier found)

/-- A step that keeps the balances keeps the balance at each position. -/
private theorem BalanceStays.of_balances {index : Nat} (same : after.balances = state.balances) :
    BalanceStays index state after :=
  fun _ found => by rw [same]; exact found

/-- An exit keeps the balances. -/
private theorem balances_initiateValidatorExit {position : ValidatorIndex}
    (computed : initiateValidatorExit config state position = .ok after) :
    after.balances = state.balances := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    obtain ⟨_, rfl⟩ := setValidator_ok set
    rfl

/-! ## The later operations -/

/-- A deposit of a block to another key keeps the balance at the position of a validator.

It neither lowers that balance nor raises it. -/
private theorem stays_processDeposit {before : fork < .hegota} {deposit : Deposit} {index : Nat}
    {validator : Validator}
    (computed : processDeposit config checks before state deposit = .ok after)
    (found : state.validators.data[index]? = some validator)
    (other : deposit.data.pubkey ≠ validator.pubkey) : BalanceStays index state after := by
  intro earlier atIndex
  obtain ⟨low, atLow, lowLe⟩ := down_processDeposit computed found other earlier atIndex
  obtain ⟨high, atHigh, highLe⟩ := balanceRises_processDeposit computed
    (Array.getElem?_eq_some_iff.mp found).1 earlier atIndex
  rw [atLow, Option.some.injEq] at atHigh
  subst atHigh
  rw [atLow, UInt64.le_antisymm lowLe highLe]

/-- From Electra, a deposit of a block keeps the balance at each position of the registry.

It only queues a pending deposit, after a new validator with no balance at most. -/
private theorem stays_processDeposit_of_electra (electra : .pectra ≤ fork)
    {before : fork < .hegota} {deposit : Deposit} {index : Nat}
    (computed : processDeposit config checks before state deposit = .ok after)
    (inside : index < state.validators.data.size) : BalanceStays index state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine (BalanceStays.of_balances
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans ?_
  unfold applyDeposit at applied
  simp only [electra, ↓reduceDIte] at applied
  unfold applyDepositElectra at applied
  split at applied
  · simp only [bind_ok_iff] at applied
    obtain ⟨_, _, applied⟩ := applied
    split at applied
    · simp only [bind_ok_iff, liftAccessor_ok] at applied
      obtain ⟨_, added, pushed⟩ := applied
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact BalanceStays.trans (fun _ found => addValidatorToRegistry_balance added inside found)
        (BalanceStays.of_balances rfl)
    · cases applied
      exact BalanceStays.refl _ _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
    exact BalanceStays.of_balances rfl

/-- A partial withdrawal request keeps the balances. -/
private theorem stays_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {position : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra position validator amount owed =
      .ok after) (index : Nat) :
    BalanceStays index state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact BalanceStays.of_balances (computeExitEpochAndUpdateChurn_earliest churned).2.2
  · cases computed
    exact BalanceStays.refl _ _

/-- A withdrawal request keeps the balances. -/
private theorem stays_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) (index : Nat) :
    BalanceStays index state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BalanceStays.refl _ _)
    | exact BalanceStays.of_balances
        (balances_initiateValidatorExit (liftAccessor_ok.mp computed))
    | exact stays_requestPartialWithdrawal computed index

/-- A step keeps the balance at a position, and keeps the keys as a prefix. -/
private def Stay (index : Nat) (state after : BeaconState preset fork) : Prop :=
  BalanceStays index state after ∧ validatorKeys state <+: validatorKeys after

/-- A state keeps its own balance and keys. -/
private theorem Stay.refl (index : Nat) (state : BeaconState preset fork) :
    Stay index state state :=
  ⟨BalanceStays.refl index state, List.prefix_refl _⟩

/-- Two steps that keep a balance and the keys keep them. -/
private theorem Stay.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : Stay index first second) (two : Stay index second third) : Stay index first third :=
  ⟨one.1.trans two.1, one.2.trans two.2⟩

/-- A fold keeps a balance and the keys when each step does, given the steps so far. -/
private theorem Stay.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    {start : BeaconState preset fork} {items : List α}
    (each : ∀ u x v, x ∈ items → Stay index start u → step u x = .ok v → Stay index u v)
    {first last : BeaconState preset fork} (held : Stay index start first)
    (computed : items.foldlM step first = .ok last) : Stay index start last :=
  foldlM_ok_invariant_of_mem (Stay index start)
    (fun u x v member held ok => held.trans (each u x v member held ok)) held computed

/-- The requests of the execution layer keep the balance of a validator that sends no switch. -/
private theorem stay_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam} {index : Nat} {validator : Validator}
    {start : BeaconState preset fork}
    (computed : processExecutionRequests config state body electra = .ok after)
    (held : Stay index start state) (found : start.validators.data[index]? = some validator)
    (unswitched : ∀ request ∈ (body.executionRequests electra).consolidations.data,
      request.sourcePubkey ≠ validator.pubkey) :
    Stay index start after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  have deposited := Stay.foldlM (fun _ _ _ _ _ ok => ⟨BalanceStays.of_balances
    (processDepositRequest_ok ok).2.2, (frame_processDepositRequest ok).pubkeysPrefix⟩)
    held depositsOk
  have withdrawn := Stay.foldlM (fun _ _ _ _ _ ok => ⟨stays_processWithdrawalRequest ok index,
    (frame_processWithdrawalRequest ok).pubkeysPrefix⟩) deposited withdrawalsOk
  refine Stay.foldlM (fun u request v member held ok => ?_) withdrawn consolidationsOk
  obtain ⟨now, atNow, same⟩ := validators_getElem?_of_validatorKeys_prefix held.2 found
  refine ⟨balanceStays_processConsolidationRequest ok atNow ?_,
    (frame_processConsolidationRequest ok).pubkeysPrefix⟩
  rw [same]
  exact unswitched request (Array.mem_toList_iff.mp member)

/-! ## The operations -/

/-- The balance of a validator through the operations of a block.

The proposer slashings, the attester slashings and the attestations each keep it from falling.

The operations after them keep it.

Before Electra, no deposit of the block may carry its key.

From Electra to Fulu, no consolidation request may come from its key either.

The slashings must spare it. -/
theorem processOperations_balance {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unslashedByProposers : ∀ slashing ∈ body.proposerSlashings.data,
      slashing.signedHeader1.message.proposerIndex.toNat ≠ index)
    (unslashedByAttesters : ∀ slashing ∈ body.attesterSlashings.data,
      ∀ slashed ∈ slashingIndices slashing, slashed.toNat ≠ index)
    (undeposited : ∀ before : fork < .pectra,
      ∀ deposit ∈ (body.deposits (Nat.lt_trans before (by decide))).data,
        deposit.data.pubkey ≠ validator.pubkey)
    (unswitched : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
      ∀ request ∈ (body.executionRequests electra).consolidations.data,
        request.sourcePubkey ≠ validator.pubkey) :
    ∃ slashed caught attested,
      body.proposerSlashings.data.foldlM (processProposerSlashing config checks) state =
        .ok slashed ∧
      body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) slashed =
        .ok caught ∧
      body.attestations.data.foldlM (processAttestation config checks · parentSlot ·) caught =
        .ok attested ∧
      BalanceRises index state slashed ∧ BalanceRises index slashed caught ∧
      BalanceRises index caught attested ∧ BalanceStays index attested after := by
  have exits {u v : BeaconState preset fork} {signed : List SignedVoluntaryExit}
      {start : BeaconState preset fork} (held : Stay index start u)
      (ok : signed.foldlM (processVoluntaryExit config checks) u = .ok v) :
      Stay index start v :=
    Stay.foldlM (fun _ _ _ _ _ ok => ⟨BalanceStays.of_balances
      (balances_initiateValidatorExit (processVoluntaryExit_initiates ok)),
      (frame_processVoluntaryExit ok).pubkeysPrefix⟩) held ok
  have changes {u v : BeaconState preset fork} {signed : List SignedBLSToExecutionChange}
      {start : BeaconState preset fork} (held : Stay index start u)
      (ok : signed.foldlM (processBlsToExecutionChange config checks) u = .ok v) :
      Stay index start v := by
    refine Stay.foldlM (fun _ _ _ _ _ ok =>
      ⟨?_, (frame_processBlsToExecutionChange ok).pubkeysPrefix⟩) held ok
    obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact BalanceStays.of_balances rfl
  -- The three folds come first, and keep the keys.
  have folds {slashed caught attested : BeaconState preset fork}
      (proposersOk : body.proposerSlashings.data.toList.foldlM
        (processProposerSlashing config checks) state = .ok slashed)
      (attestersOk : body.attesterSlashings.data.toList.foldlM
        (processAttesterSlashing config checks) slashed = .ok caught)
      (attestedOk : body.attestations.data.toList.foldlM
        (processAttestation config checks · parentSlot ·) caught = .ok attested) :
      BalanceRises index state slashed ∧ BalanceRises index slashed caught ∧
        BalanceRises index caught attested ∧ validatorKeys state <+: validatorKeys attested := by
    refine ⟨foldlM_ok_invariant_of_mem (BalanceRises index state)
        (fun u slashing v member held ok => held.trans (balanceRises_processProposerSlashing ok
          (unslashedByProposers slashing (Array.mem_toList_iff.mp member))))
        (BalanceRises.refl index state) proposersOk,
      foldlM_ok_invariant_of_mem (BalanceRises index slashed)
        (fun u slashing v member held ok => held.trans (balanceRises_processAttesterSlashing ok
          (unslashedByAttesters slashing (Array.mem_toList_iff.mp member))))
        (BalanceRises.refl index slashed) attestersOk,
      BalanceRises.foldlM (fun _ _ _ ok => balanceRises_processAttestation ok index) attestedOk, ?_⟩
    have frame := (foldlM_ok_steps Frame Frame.refl Frame.trans
      (fun _ _ _ ok => (frame_processProposerSlashing ok).toFrame) proposersOk).1.trans <|
      (foldlM_ok_steps Frame Frame.refl Frame.trans
        (fun _ _ _ ok => (frame_processAttesterSlashing ok).toFrame) attestersOk).1.trans
      (foldlM_ok_steps Frame Frame.refl Frame.trans
        (fun _ _ _ ok => frame_processAttestation ok) attestedOk).1
    exact frame.pubkeysPrefix
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    unfold processOperationsGloas at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed, proposersOk, caught, attestersOk,
      attested, attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    refine ⟨slashed, caught, attested, proposersOk, attestersOk, attestedOk, ?_⟩
    rw [← Array.foldlM_toList] at proposersOk attestersOk attestedOk exitsOk changesOk paid
    obtain ⟨one, two, three, -⟩ := folds proposersOk attestersOk attestedOk
    refine ⟨one, two, three, ?_⟩
    refine ((changes (exits (Stay.refl index attested) exitsOk) changesOk).trans ?_).1
    refine Stay.foldlM (fun _ _ _ _ _ ok => ?_) (Stay.refl index _) paid
    rw [processPayloadAttestation_eq ok]
    exact Stay.refl _ _
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, slashed, proposersOk, caught, attestersOk, attested, attestedOk, _,
    depositedOk, exited, exitsOk, changed, changesOk, requestsOk⟩ := computed
  refine ⟨slashed, caught, attested, proposersOk, attestersOk, attestedOk, ?_⟩
  rw [← Array.foldlM_toList] at proposersOk attestersOk attestedOk depositedOk exitsOk
  obtain ⟨one, two, three, keys⟩ := folds proposersOk attestersOk attestedOk
  refine ⟨one, two, three, ?_⟩
  -- Each later state holds the key of the validator at its position.
  obtain ⟨now, atNow, same⟩ := validators_getElem?_of_validatorKeys_prefix keys found
  have deposited := Stay.foldlM (fun u deposit v member held ok => by
    obtain ⟨current, atCurrent, kept⟩ := validators_getElem?_of_validatorKeys_prefix held.2 atNow
    refine ⟨?_, (frame_processDeposit ok).pubkeysPrefix⟩
    by_cases electra : Fork.pectra ≤ fork
    · exact stays_processDeposit_of_electra electra ok
        (Array.getElem?_eq_some_iff.mp atCurrent).1
    refine stays_processDeposit ok atCurrent ?_
    rw [kept, same]
    exact undeposited (Nat.lt_of_not_le electra) deposit (Array.mem_toList_iff.mp member))
    (Stay.refl index attested)
    depositedOk
  have changed : Stay index attested changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact changes (exits deposited exitsOk) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ exits deposited exitsOk
  split at requestsOk
  · refine (stay_processExecutionRequests requestsOk changed atNow fun request member => ?_).1
    rw [same]
    exact unswitched _ request member
  · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
    exact requestsOk ▸ changed.1

/-! ## The sync aggregate -/

/-- Paired with bits of the same length, the pairs with a set bit are as many as the set bits. -/
private theorem countP_zip_snd {α : Type} :
    ∀ (items : List α) (bits : List Bool), items.length = bits.length →
      (items.zip bits).countP (·.2) = bits.countP id
  | [], [], _ => rfl
  | _ :: items, _ :: bits, same => by
    simp only [List.zip_cons_cons, List.countP_cons,
      countP_zip_snd items bits (by simpa using same)]
    rfl
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

/-- The sync rewards at the position of a proposer that holds no seat.

Each member that signs adds the proposer share, and no other step touches the position. -/
private theorem syncRewards_proposer {reward proposerReward index : Nat}
    {chosen : ValidatorIndex} :
    ∀ (members : List (ValidatorIndex × Bool)) (balance : Nat),
      (∀ member ∈ members, member.1.toNat ≠ index) →
      (∀ member ∈ members, member.2 = true → chosen.toNat = index) →
      members.foldl (fun balance member =>
        if member.2 then balance + (if member.1.toNat = index then reward else 0) +
          (if chosen.toNat = index then proposerReward else 0)
        else if member.1.toNat = index then balance - reward else balance) balance =
        balance + proposerReward * members.countP (·.2)
  | [], _, _, _ => by simp
  | member :: members, balance, apart, paid => by
    rw [List.foldl_cons, syncRewards_proposer members _
      (fun other inside => apart other (List.mem_cons_of_mem _ inside))
      (fun other inside => paid other (List.mem_cons_of_mem _ inside)), List.countP_cons]
    have head := apart member List.mem_cons_self
    by_cases signed : member.2 = true
    · simp only [signed, ↓reduceIte, head, paid member List.mem_cons_self signed]
      rw [Nat.mul_add]
      omega
    · simp only [signed, Bool.false_eq_true, ↓reduceIte, head, Nat.add_zero]

/-- The sync aggregate pays a proposer without a seat its share once per signature.

That share is the participant reward times the proposer weight, over the denominator less it.

It rounds down. -/
theorem processSyncAggregate_proposer {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset} {proposer : ValidatorIndex} {validator : Validator}
    {balance : Gwei}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after)
    (read : getBeaconProposerIndex state = .ok proposer)
    (found : state.validators.data[proposer.toNat]? = some validator)
    (unseated : validator.pubkey ∉ (state.currentSyncCommittee altair).value.pubkeys.toList)
    (held : state.balances.data[proposer.toNat]? = some balance) :
    ∃ reward proposerReward final : Gwei, syncParticipantReward state = .ok reward ∧
      proposerReward.toNat =
        reward.toNat * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) ∧
      after.balances.data[proposer.toNat]? = some final ∧
      final.toNat = balance.toNat +
        proposerReward.toNat * aggregate.syncCommitteeBits.bits.toArray.countP id := by
  obtain ⟨reward, proposerReward, members, chosen, rewardOk, share, membersOk, chosenOk,
    balances⟩ := processSyncAggregate_balance computed
  -- No member is the proposer, since no key of the committee is its key.
  have seatless : ∀ bit : Bool, ∀ member ∈ (members.zip
      aggregate.syncCommitteeBits.bits.toArray).toList, member.2 = bit →
      member.1.toNat ≠ proposer.toNat := by
    intro bit
    refine signers_elsewhere membersOk found fun member inside _ same => unseated ?_
    rw [Array.toList_zip] at inside
    rw [← same, ← Vector.toList_toArray]
    exact List.of_mem_zip inside |>.1
  have length : members.size = preset.SYNC_COMMITTEE_SIZE.toNat := by
    have onList : (state.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
        (validatorIndexOfPubkey state) = .ok members.toList := by
      rw [← Array.toList_mapM, membersOk]
      rfl
    have := mapM_ok_length onList
    simpa using this
  obtain ⟨final, atFinal, value⟩ := balances _ balance held
  refine ⟨reward, proposerReward, final, rewardOk, share, atFinal, ?_⟩
  rw [value, syncRewards_proposer _ _ (fun member inside => seatless member.2 member inside rfl)
    (fun member inside signed => ?_)]
  · rw [Array.toList_zip, countP_zip_snd _ _ (by simp [length]), Array.countP_toList]
  · rw [read] at chosenOk
    rw [Except.ok.inj (chosenOk ⟨member, inside, signed⟩)]

end EthLib.Consensus
