module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.BuilderRequests
public import EthLib.Consensus.Proofs.Transition.Withdrawals
public import EthLib.Consensus.Transition.Operations

/-!
# Proofs: the operations of a block

An attestation is included in its window, with the justified source of its target epoch.

It then joins the pending attestations of its target epoch, and nothing else changes.

A deposit lies in the deposit tree, and moves the next deposit index on by one.

A deposit to a known key adds its amount to the sum of the balances.

A valid deposit to a new key adds one validator and its balance.

An invalid deposit to a new key changes nothing.

A voluntary exit is signed by an active validator, which then has an exit epoch.

The operations of a block hold every outstanding deposit, up to the most per block.

They keep one balance for each validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The sum of the balances, on natural numbers. -/
def balanceSum (state : BeaconState preset fork) : Nat :=
  (state.balances.data.toList.map (·.toNat)).sum

/-- The registry and the balances have one entry for each validator. -/
def BalancesMatch (state : BeaconState preset fork) : Prop :=
  state.balances.data.size = state.validators.data.size

theorem balancesMatch_of_sameSizes (sizes : SameSizes state after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  unfold BalancesMatch at holds ⊢
  rw [sizes.1, sizes.2, holds]

/-- Raising a balance adds the amount to the sum of the balances. -/
theorem balanceSum_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    balanceSum after = balanceSum state + delta.toNat := by
  simp only [increaseBalance, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨balance, found, raised, ⟨_, summed⟩, rfl⟩ := computed
  unfold getBalance at found
  split at found
  · rename_i read
    cases found
    obtain ⟨inside, rfl⟩ := Array.getElem?_eq_some_iff.mp read
    unfold balanceSum BeaconState.setBalance
    simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, inside, ↓reduceDIte,
      Array.toList_set, List.map_set]
    have := sum_set_add (l := state.balances.data.toList.map (·.toNat)) (i := index.toNat)
      (by simpa using inside) raised.toNat
    simp only [List.getElem_map, Array.getElem_toList] at this
    omega
  · cases found

/-! ## Attestations -/

/-- Recording a pending attestation appends it to the list of its epoch, and changes nothing else.
-/
theorem recordPendingAttestation_ok {before : fork < .altair} {current : Bool}
    {pending : PendingAttestation preset}
    (computed : recordPendingAttestation state before current pending = .ok after) :
    if current then
      (after.currentEpochAttestations before).data =
          (state.currentEpochAttestations before).data.push pending ∧
        { after with currentEpochAttestations := state.currentEpochAttestations } = state
    else
      (after.previousEpochAttestations before).data =
          (state.previousEpochAttestations before).data.push pending ∧
        { after with previousEpochAttestations := state.previousEpochAttestations } = state := by
  cases current <;>
    simp only [recordPendingAttestation, Bool.false_eq_true, ↓reduceIte] at computed ⊢ <;>
    split at computed <;> cases computed <;> simp

theorem sameSizes_recordPendingAttestation {before : fork < .altair} {current : Bool}
    {pending : PendingAttestation preset}
    (computed : recordPendingAttestation state before current pending = .ok after) :
    SameSizes state after := by
  cases current <;>
    simp only [recordPendingAttestation, Bool.false_eq_true, ↓reduceIte] at computed <;>
    split at computed <;> cases computed <;> exact SameSizes.refl _

/-- An attestation is valid only before Altair.

Its target is the current or the previous epoch, and the epoch of its slot.

It is included at least the least inclusion delay after its slot, and at most one epoch after.

It names a committee of its slot, with one bit for each member.

Its source is the justified checkpoint that the state holds for its target epoch. -/
theorem processAttestation_checks {attestation : Attestation preset fork}
    (computed : processAttestation config checks state attestation = .ok after) :
    fork < .altair ∧
      (attestation.data.target.epoch = getPreviousEpoch state ∨
        attestation.data.target.epoch = getCurrentEpoch state) ∧
      attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot ∧
      attestation.data.slot.toNat + preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤
        state.slot.toNat ∧
      state.slot.toNat ≤ attestation.data.slot.toNat + preset.SLOTS_PER_EPOCH.toNat ∧
      attestation.data.index < getCommitteeCountPerSlot state attestation.data.target.epoch ∧
      (∃ committee, getBeaconCommittee state attestation.data.slot attestation.data.index =
          .ok committee ∧ attestation.aggregationBits.bits.size = committee.size) ∧
      attestation.data.source =
        if attestation.data.target.epoch = getCurrentEpoch state then
          state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint := by
  unfold processAttestation at computed
  split at computed
  · cases computed
  rename_i altair
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at computed
  obtain ⟨_, recent, _, slotEpoch, earliest, ⟨_, earliestSum⟩, _, early, latest,
    ⟨_, latestSum⟩, _, late, _, index, committee, found, _, bits, _, _, _, source, _⟩ :=
    computed
  refine ⟨Nat.lt_of_not_le altair, recent, slotEpoch, ?_, ?_, index, ⟨committee, found, bits⟩, ?_⟩
  · rw [← earliestSum]
    exact UInt64.le_iff_toNat_le.mp early
  · rw [← latestSum]
    exact UInt64.le_iff_toNat_le.mp late
  · simpa [beq_iff_eq] using source

/-- A valid attestation joins the pending attestations of its target epoch.

The pending attestation holds its bits and data, its inclusion delay and the current proposer.

The signature of the attestation is valid on the state that holds it. -/
theorem processAttestation_records {attestation : Attestation preset fork}
    (computed : processAttestation config checks state attestation = .ok after) :
    ∃ (before : fork < .altair) (pending : PendingAttestation preset),
      pending.aggregationBits.bits = attestation.aggregationBits.bits ∧
      pending.data = attestation.data ∧
      pending.inclusionDelay = state.slot - attestation.data.slot ∧
      getBeaconProposerIndex state = .ok pending.proposerIndex ∧
      recordPendingAttestation state before
          (attestation.data.target.epoch == getCurrentEpoch state) pending = .ok after ∧
      ∃ indexed, getIndexedAttestation after attestation = .ok indexed ∧
        isValidIndexedAttestation config checks after indexed = .ok true := by
  unfold processAttestation at computed
  split at computed
  · cases computed
  rename_i altair
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposer, proposerOk, _, _,
    updated, recorded, indexed, indexedOk, valid, validOk, _, validTrue, rfl⟩ := computed
  subst validTrue
  exact ⟨Nat.lt_of_not_le altair, _, rfl, rfl, rfl, proposerOk, recorded, indexed, indexedOk,
    validOk⟩

theorem sameSizes_processAttestation {attestation : Attestation preset fork}
    (computed : processAttestation config checks state attestation = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, _, _, _, _, recorded, _⟩ := processAttestation_records computed
  exact sameSizes_recordPendingAttestation recorded

/-! ## Deposits -/

/-- Before Electra, a deposit to a key that a validator has adds the amount to its balance.

The sum of the balances grows by the amount, and the registry stays. -/
theorem applyDeposit_known {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature} {index : Nat}
    (known : state.validators.data.findIdx? (·.pubkey == pubkey) = some index)
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    balanceSum after = balanceSum state + amount.toNat ∧ after.validators = state.validators := by
  unfold applyDeposit at computed
  split at computed
  · cases computed
  simp only [known, liftAccessor_ok] at computed
  exact ⟨balanceSum_increaseBalance computed, increaseBalance_validators computed⟩

/-- Before Altair, a deposit to a new key with a valid signature adds a validator and its balance.
-/
theorem applyDeposit_new_valid {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (new : state.validators.data.findIdx? (·.pubkey == pubkey) = none)
    (valid : isValidDepositSignature config checks pubkey withdrawalCredentials amount signature =
      .ok true)
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    fork < .altair ∧
      after.validators.data = state.validators.data.push
        (getValidatorFromDeposit preset pubkey withdrawalCredentials amount) ∧
      after.balances.data = state.balances.data.push amount := by
  unfold applyDeposit at computed
  split at computed
  · cases computed
  simp only [new, valid, bind, Except.bind, ↓reduceIte] at computed
  unfold addValidatorToRegistry at computed
  split at computed
  · cases computed
  rename_i altair
  split at computed
  · cases computed
    exact ⟨Nat.lt_of_not_le altair, rfl, rfl⟩
  · cases computed

/-- Before Electra, a deposit to a new key with an invalid signature changes nothing. -/
theorem applyDeposit_new_invalid {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature} (before : fork < .pectra)
    (new : state.validators.data.findIdx? (·.pubkey == pubkey) = none)
    (invalid : isValidDepositSignature config checks pubkey withdrawalCredentials amount signature =
      .ok false) :
    applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok state := by
  have notElectra : ¬Fork.pectra ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp [applyDeposit, notElectra, new, invalid, bind, Except.bind, pure, Except.pure]

/-- A deposit keeps one balance for each validator. -/
theorem balancesMatch_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  cases found : state.validators.data.findIdx? (·.pubkey == pubkey) with
  | some index =>
    unfold applyDeposit at computed
    split at computed
    · cases computed
    simp only [found, liftAccessor_ok] at computed
    exact balancesMatch_of_sameSizes (sameSizes_increaseBalance computed) holds
  | none =>
    cases signed : isValidDepositSignature config checks pubkey withdrawalCredentials amount
        signature with
    | error e =>
      unfold applyDeposit at computed
      split at computed
      · cases computed
      simp [found, signed, bind, Except.bind] at computed
    | ok valid =>
      cases valid with
      | true =>
        obtain ⟨_, validators, balances⟩ := applyDeposit_new_valid found signed computed
        unfold BalancesMatch at holds ⊢
        rw [validators, balances, Array.size_push, Array.size_push, holds]
      | false =>
        unfold applyDeposit at computed
        split at computed
        · cases computed
        simp only [found, signed, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, pure,
          Except.pure, Except.ok.injEq] at computed
        exact computed ▸ holds

/-- A deposit keeps the deposit data and the next deposit index. -/
theorem applyDeposit_eth1 {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    after.eth1DepositIndex = state.eth1DepositIndex ∧ after.eth1Data = state.eth1Data := by
  unfold applyDeposit at computed
  split at computed
  · cases computed
  split at computed
  · simp only [bind, Except.bind] at computed
    split at computed
    · cases computed
    split at computed
    · unfold addValidatorToRegistry at computed
      split at computed
      · cases computed
      split at computed
      · cases computed
        exact ⟨rfl, rfl⟩
      · cases computed
    · cases computed
      exact ⟨rfl, rfl⟩
  · simp only [liftAccessor_ok, increaseBalance, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩

/-- A valid deposit lies in the deposit tree, at the next deposit index.

The next deposit index then grows by one, and the deposit applies. -/
theorem processDeposit_ok {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    (∃ leaf, hashTreeRoot deposit.data = .ok leaf ∧
      isValidMerkleBranch leaf deposit.proof.toList (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
        (state.eth1DepositIndex before).toNat (state.eth1Data before).depositRoot = true) ∧
      (after.eth1DepositIndex before).toNat = (state.eth1DepositIndex before).toNat + 1 ∧
      ∃ next, (state.eth1DepositIndex before).toNat + 1 = next.toNat ∧
        applyDeposit config checks { state with eth1DepositIndex := fun _ => next }
          deposit.data.pubkey deposit.data.withdrawalCredentials deposit.data.amount
          deposit.data.signature = .ok after := by
  simp only [processDeposit, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, liftArith,
    mapError_ok_iff, addChecked_ok_iff] at computed
  obtain ⟨leaf, leafOk, _, valid, next, ⟨_, summed⟩, applied⟩ := computed
  have kept := (applyDeposit_eth1 applied).1
  refine ⟨⟨leaf, leafOk, valid⟩, ?_, next, by simpa using summed.symm, applied⟩
  rw [kept]
  simpa using summed

theorem balancesMatch_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok computed
  exact balancesMatch_applyDeposit applied holds

/-! ## Voluntary exits -/

/-- A valid voluntary exit is before Deneb, from an active validator that has not started to exit.

The exit is not for a later epoch, and the validator has been active for long enough.

The validator signs the exit, under the fork version of the epoch of the exit. -/
theorem processVoluntaryExit_checks {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    fork < .dencun ∧ ∃ validator, getValidator state signed.message.validatorIndex = .ok validator ∧
      isActiveValidator validator (getCurrentEpoch state) = true ∧
      validator.exitEpoch = FAR_FUTURE_EPOCH ∧
      signed.message.epoch ≤ getCurrentEpoch state ∧
      validator.activationEpoch.toNat + config.SHARD_COMMITTEE_PERIOD.toNat ≤
        (getCurrentEpoch state).toNat ∧
      ∃ domain signingRoot,
        getDomain config state DOMAIN_VOLUNTARY_EXIT (some signed.message.epoch) = .ok domain ∧
        computeSigningRoot signed.message domain = .ok signingRoot ∧
        checks.verify (packBytes validator.pubkey) (packBytes signingRoot)
          (packBytes signed.signature) = true := by
  unfold processVoluntaryExit at computed
  split at computed
  · cases computed
  rename_i deneb
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at computed
  obtain ⟨validator, found, _, active, _, notExiting, _, notLater, eligible, ⟨_, summed⟩, _,
    longEnough, domain, domainOk, signingRoot, rootOk, _, verified, _⟩ := computed
  refine ⟨Nat.lt_of_not_le deneb, validator, found, active, notExiting, notLater, ?_, domain,
    signingRoot, domainOk, rootOk, verified⟩
  rw [← summed]
  exact UInt64.le_iff_toNat_le.mp longEnough

/-- After a valid voluntary exit, its validator may withdraw a fixed delay after its exit epoch.

With a nonzero delay, the exit epoch is then not the far future epoch. -/
theorem processVoluntaryExit_exited {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    ∃ exited, getValidator after signed.message.validatorIndex = .ok exited ∧
      exited.withdrawableEpoch.toNat =
        exited.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ∧
      (config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY ≠ 0 → exited.exitEpoch ≠ FAR_FUTURE_EPOCH) := by
  obtain ⟨_, validator, found, _, notExiting, _⟩ := processVoluntaryExit_checks computed
  unfold processVoluntaryExit at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, found', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  obtain ⟨exitedValidator, read, sum⟩ :=
    initiateValidatorExit_withdrawableEpoch found notExiting exited
  refine ⟨exitedValidator, read, sum, fun nonzero far => ?_⟩
  have bounded := exitedValidator.withdrawableEpoch.toNat_lt
  have positive : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    rcases Nat.eq_zero_or_pos config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat with zero | pos
    · exact absurd (UInt64.toNat_inj.mp (by simpa using zero)) nonzero
    · exact pos
  rw [far] at sum
  simp [FAR_FUTURE_EPOCH] at sum
  omega

theorem sameSizes_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    SameSizes state after := by
  unfold processVoluntaryExit at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact sameSizes_initiateValidatorExit exited

/-! ## All the operations of a block -/

/-- The operations of a valid block run before Electra.

The block holds every outstanding deposit, up to the most per block. -/
theorem processOperations_deposits {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body = .ok after) :
    fork < .pectra ∧ ∀ before : fork < .hegota,
      (state.eth1DepositIndex before).toNat ≤ (state.eth1Data before).depositCount.toNat ∧
      (body.deposits before).data.size =
        min preset.MAX_DEPOSITS.toNat
          ((state.eth1Data before).depositCount.toNat - (state.eth1DepositIndex before).toNat) := by
  unfold processOperations at computed
  split at computed
  · cases computed
  rename_i capella
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    subChecked_ok_iff] at computed
  obtain ⟨outstanding, ⟨noUnderflow, difference⟩, _, count, _⟩ := computed
  refine ⟨Nat.lt_of_not_le capella, fun _ => ⟨UInt64.le_iff_toNat_le.mp noUnderflow, ?_⟩⟩
  rw [count, UInt64.min_def]
  split
  · rename_i le
    have := UInt64.le_iff_toNat_le.mp le
    omega
  · rename_i gt
    have := mt UInt64.le_iff_toNat_le.mpr gt
    omega

/-- The operations of a block keep one balance for each validator. -/
theorem balancesMatch_processOperations {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have keep {α : Type} (step : BeaconState preset fork → α → Except TransitionError _)
      (sizes : ∀ s x s', step s x = .ok s' → SameSizes s s') :=
    fun s x s' (h : BalancesMatch s) ok => balancesMatch_of_sameSizes (sizes s x s' ok) h
  have one := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processProposerSlashing ok) holds proposersOk
  have two := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processAttesterSlashing ok) one attestersOk
  have three := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processAttestation ok) two attestedOk
  have four := foldlM_ok_invariant BalancesMatch
    (fun _ _ _ h ok => balancesMatch_processDeposit ok h) three depositedOk
  have five := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processVoluntaryExit ok) four exitsOk
  split at changesOk
  · exact foldlM_ok_invariant BalancesMatch
      (keep _ fun _ _ _ ok => sameSizes_processBlsToExecutionChange ok) five changesOk
  · cases changesOk
    exact five

end EthLib.Consensus
