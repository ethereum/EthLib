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

From Electra a deposit request joins the end of the pending deposits.

A voluntary exit is signed by an active validator, which then has an exit epoch.

The operations of a block hold every outstanding deposit, up to the most per block.

They keep one balance for each validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {parentSlot : Slot}

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
  simp only [increaseBalance, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff]
    at computed
  obtain ⟨balance, found, raised, ⟨_, summed⟩, set⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  unfold getBalance at found
  split at found
  · rename_i read
    cases found
    obtain ⟨inside, rfl⟩ := Array.getElem?_eq_some_iff.mp read
    unfold balanceSum BeaconState.putBalance
    simp only [Array.toList_set, List.map_set]
    have := sum_set_add (l := state.balances.data.toList.map (·.toNat)) (i := index.toNat)
      (by simpa using inside) raised.toNat
    simp only [List.getElem_map, Array.getElem_toList] at this
    omega
  · cases found

/-- Lowering a balance by at most itself takes the amount from the sum of the balances. -/
theorem balanceSum_decreaseBalance {index : ValidatorIndex} {delta balance : Gwei}
    (found : getBalance state index = .ok balance) (le : delta ≤ balance)
    (computed : decreaseBalance state index delta = .ok after) :
    balanceSum after + delta.toNat = balanceSum state := by
  simp only [decreaseBalance, found, bind, Except.bind] at computed
  obtain ⟨_, rfl⟩ := setBalance_ok computed
  unfold getBalance at found
  split at found
  · rename_i read
    cases found
    obtain ⟨inside, rfl⟩ := Array.getElem?_eq_some_iff.mp read
    unfold balanceSum BeaconState.putBalance
    simp only [Array.toList_set, List.map_set]
    have := sum_set_add (l := state.balances.data.toList.map (·.toNat)) (i := index.toNat)
      (by simpa using inside) (saturatingSub state.balances.data[index.toNat] delta).toNat
    simp only [List.getElem_map, Array.getElem_toList] at this
    have sub : (saturatingSub state.balances.data[index.toNat] delta).toNat + delta.toNat =
        state.balances.data[index.toNat].toNat := by
      rw [toNat_saturatingSub]
      have := UInt64.le_iff_toNat_le.mp le
      omega
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

/-- Before Altair, what a valid attestation satisfies.

Its target is the current or the previous epoch, and the epoch of its slot.

It is included at least the least inclusion delay after its slot, and at most one epoch after.

It names a committee of its slot, with one bit for each member.

Its source is the justified checkpoint that the state holds for its target epoch. -/
theorem processAttestation_checks {attestation : Attestation preset fork}
    (before : fork < .altair)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
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
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at computed
  obtain ⟨_, recent, _, slotEpoch, earliest, ⟨_, earliestSum⟩, _, early, latest,
    ⟨_, latestSum⟩, _, late, _, index, committee, found, _, bits, _, _, _, source, _⟩ :=
    computed
  refine ⟨recent, slotEpoch, ?_, ?_, index, ⟨committee, found, bits⟩, ?_⟩
  · rw [← earliestSum]
    exact UInt64.le_iff_toNat_le.mp early
  · rw [← latestSum]
    exact UInt64.le_iff_toNat_le.mp late
  · simpa [beq_iff_eq] using source

/-- Before Altair, a valid attestation joins the pending attestations of its target epoch.

The pending attestation holds its bits and data, its inclusion delay and the current proposer.

The signature of the attestation is valid on the state that holds it. -/
theorem processAttestation_records {attestation : Attestation preset fork}
    (before : fork < .altair)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ pending : PendingAttestation preset,
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
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposer, proposerOk, _, _,
    updated, recorded, indexed, indexedOk, valid, validOk, _, validTrue, rfl⟩ := computed
  subst validTrue
  exact ⟨_, rfl, rfl, rfl, proposerOk, recorded, indexed, indexedOk, validOk⟩

/-- From Altair, writing the flags of an epoch keeps the sizes of the registry and the balances.
-/
theorem sameSizes_setEpochParticipation (current : Bool)
    (participation : EpochParticipation preset fork) :
    SameSizes state (setEpochParticipation state current participation) := by
  unfold setEpochParticipation
  split <;> exact SameSizes.refl _

/-- Before Deneb, the inclusion deadline passes exactly when two facts hold.

The slot one epoch after the given slot fits in 64 bits.

The slot of the state is at most that slot. -/
theorem checkInclusionDeadline_ok_iff {slot : Slot} (before : fork < .dencun) :
    checkInclusionDeadline state slot = .ok () ↔
      slot.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 ∧
        state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_EPOCH.toNat := by
  simp only [checkInclusionDeadline, before, ↓reduceIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff]
  constructor
  · rintro ⟨latest, ⟨fits, sum⟩, le⟩
    exact ⟨fits, sum ▸ UInt64.le_iff_toNat_le.mp le⟩
  · rintro ⟨fits, le⟩
    have sum : (slot + preset.SLOTS_PER_EPOCH).toNat = slot.toNat + preset.SLOTS_PER_EPOCH.toNat :=
      toNat_add_of_lt fits
    exact ⟨_, ⟨fits, sum⟩, UInt64.le_iff_toNat_le.mpr (sum ▸ le)⟩

/-- From Deneb, the inclusion deadline always passes, whatever the slots. -/
theorem checkInclusionDeadline_of_dencun {slot : Slot} (dencun : .dencun ≤ fork) :
    checkInclusionDeadline state slot = .ok () := by
  have notBefore : ¬fork < .dencun := Nat.not_lt.mpr dencun
  simp only [checkInclusionDeadline, notBefore, ↓reduceIte]
  rfl

/-- From Gloas, weighing the payment of a block changes only the pending payments of builders. -/
theorem recordPaymentWeight_eq {gloas : .glamsterdam ≤ fork} {data : AttestationData}
    {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after) :
    after = { state with builderPendingPayments := after.builderPendingPayments } := by
  unfold recordPaymentWeight at computed
  dsimp only at computed
  split at computed
  rotate_left
  · cases computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- From Gloas, weighing a payment leaves every payment at another position as it was. -/
theorem recordPaymentWeight_other {gloas : .glamsterdam ≤ fork} {data : AttestationData}
    {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex} {position : Nat}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after)
    (other : position ≠ attestationPaymentPosition preset current data.slot) :
    (after.builderPendingPayments gloas)[position]? =
      (state.builderPendingPayments gloas)[position]? := by
  unfold recordPaymentWeight at computed
  dsimp only at computed
  split at computed
  rotate_left
  · cases computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  simp [Ne.symm other]

/-- From Gloas, a payment gains no weight unless the vote is for the block of its own slot.

It also gains none when the payment is of no amount.

The state is then unchanged. -/
theorem recordPaymentWeight_of_noWeight {gloas : .glamsterdam ≤ fork} {data : AttestationData}
    {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after)
    (noWeight : isAttestationSameSlot state data = .ok false ∨
      ∀ payment, (state.builderPendingPayments gloas)[
        attestationPaymentPosition preset current data.slot]? = some payment →
          payment.withdrawal.amount = 0) :
    after = state := by
  unfold recordPaymentWeight at computed
  dsimp only at computed
  split at computed
  rotate_left
  · cases computed
  rename_i inside
  simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨sameSlot, sameOk, weight, weightOk, rfl⟩ := computed
  have found : (state.builderPendingPayments gloas)[
      attestationPaymentPosition preset current data.slot]? =
      some (state.builderPendingPayments gloas)[
        attestationPaymentPosition preset current data.slot] :=
    Vector.getElem?_eq_getElem inside
  have notWeighed : ¬(sameSlot = true ∧ 0 <
      (state.builderPendingPayments gloas)[
        attestationPaymentPosition preset current data.slot].withdrawal.amount) := by
    rintro ⟨same, positive⟩
    rcases noWeight with notSame | zero
    · rw [notSame, same] at sameOk
      cases sameOk
    · rw [zero _ found] at positive
      exact absurd positive (by decide)
  simp only [notWeighed, ↓reduceIte, Except.ok.injEq] at weightOk
  subst weightOk
  have kept : (fun _ => (state.builderPendingPayments gloas).set
      (attestationPaymentPosition preset current data.slot)
        { (state.builderPendingPayments gloas)[
          attestationPaymentPosition preset current data.slot] with
          weight := (state.builderPendingPayments gloas)[
            attestationPaymentPosition preset current data.slot].weight } inside) =
      state.builderPendingPayments := by
    funext gloas'
    have same : gloas' = gloas := rfl
    subst same
    ext index bound
    by_cases same : index = attestationPaymentPosition preset current data.slot
    · subst same
      simp
    · exact Vector.getElem_set_ne _ _ (Ne.symm same)
  simp only [kept]

/-- From Altair, an attestation keeps the sizes of the registry and the balances. -/
theorem sameSizes_processAttestationAltair {attestation : Attestation preset fork}
    {altair : .altair ≤ fork}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after) :
    SameSizes state after := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, raised, final⟩ := computed
  refine (sameSizes_setEpochParticipation _ _).trans ((sameSizes_increaseBalance raised).trans ?_)
  split at final
  · refine ⟨?_, ?_⟩ <;> rw [recordPaymentWeight_eq final]
  · cases final
    exact SameSizes.refl _

theorem sameSizes_processAttestation {attestation : Attestation preset fork}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    SameSizes state after := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte] at computed
    exact sameSizes_processAttestationAltair computed
  · obtain ⟨_, _, _, _, _, recorded, _⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) computed
    exact sameSizes_recordPendingAttestation recorded

/-! ## Deposits -/

/-- A deposit credited to a key that a validator has adds the amount to its balance.

The sum of the balances grows by the amount, and the registry stays. -/
theorem applyPendingDeposit_known {deposit : PendingDeposit} {index : Nat}
    (known : state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some index)
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    balanceSum after = balanceSum state + deposit.amount.toNat ∧
      after.validators = state.validators := by
  simp only [applyPendingDeposit, known, liftAccessor_ok] at computed
  exact ⟨balanceSum_increaseBalance computed, increaseBalance_validators computed⟩

/-- Before Electra, a deposit to a key that a validator has adds the amount to its balance.

The sum of the balances grows by the amount, and the registry stays. -/
theorem applyDeposit_known {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature} {index : Nat} (before : fork < .pectra)
    (known : state.validators.data.findIdx? (·.pubkey == pubkey) = some index)
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    balanceSum after = balanceSum state + amount.toNat ∧ after.validators = state.validators := by
  have notElectra : ¬Fork.pectra ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp only [applyDeposit, notElectra, ↓reduceDIte] at computed
  exact applyPendingDeposit_known known computed

/-- A set or an append adds one entry exactly when the index is the size of the list. -/
theorem setOrAppendList_size {switch : Base.Fork} {α : Type} {limit : Nat}
    {list list' : ForkList switch fork α limit} {index : UInt64} {value : α}
    (computed : setOrAppendList list index value = .ok list') :
    list'.data.size = if index.toNat = list.data.size then list.data.size + 1
      else list.data.size := by
  unfold setOrAppendList at computed
  split at computed
  · rename_i atEnd
    unfold appendWithinLimit at computed
    split at computed
    · cases computed
      simp [atEnd]
    · cases computed
  · rename_i notEnd
    split at computed
    · cases computed
      simp [notEnd]
    · cases computed

/-- A set or an append puts the value at the index, and keeps every other entry. -/
theorem setOrAppendList_getElem? {switch : Base.Fork} {α : Type} {limit : Nat}
    {list list' : ForkList switch fork α limit} {index : UInt64} {value : α}
    (computed : setOrAppendList list index value = .ok list') (i : Nat) :
    list'.data[i]? = if i = index.toNat then some value else list.data[i]? := by
  unfold setOrAppendList at computed
  split at computed
  · rename_i atEnd
    unfold appendWithinLimit at computed
    split at computed
    · cases computed
      simp only [Array.getElem?_push, atEnd]
    · cases computed
  · split at computed
    · cases computed
      simp only [Array.getElem?_set, eq_comm]
    · cases computed

/-- From Altair, a new validator keeps the deposit data and the next deposit index. -/
theorem addValidatorToRegistryAltair_eth1 {altair : .altair ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistryAltair state altair pubkey withdrawalCredentials amount =
      .ok after) :
    after.eth1DepositIndex = state.eth1DepositIndex ∧ after.eth1Data = state.eth1Data := by
  unfold addValidatorToRegistryAltair at computed
  simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
  exact ⟨rfl, rfl⟩

/-- From Altair, a new validator keeps one balance for each validator. -/
theorem balancesMatch_addValidatorToRegistryAltair {altair : .altair ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistryAltair state altair pubkey withdrawalCredentials amount =
      .ok after) (holds : BalancesMatch state) : BalancesMatch after := by
  unfold addValidatorToRegistryAltair at computed
  simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨validators, validatorsOk, balances, balancesOk, _, _, _, _, _, _, rfl⟩ := computed
  unfold BalancesMatch at holds ⊢
  rw [setOrAppendList_size validatorsOk, setOrAppendList_size balancesOk, holds]

/-- A new validator keeps one balance for each validator. -/
theorem balancesMatch_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · exact balancesMatch_addValidatorToRegistryAltair computed holds
  · split at computed
    · cases computed
      unfold BalancesMatch at holds ⊢
      simp only [Array.size_push, holds]
    · cases computed

/-- A new validator keeps the deposit data and the next deposit index. -/
theorem addValidatorToRegistry_eth1 {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    after.eth1DepositIndex = state.eth1DepositIndex ∧ after.eth1Data = state.eth1Data := by
  unfold addValidatorToRegistry at computed
  split at computed
  · exact addValidatorToRegistryAltair_eth1 computed
  · split at computed
    · cases computed
      exact ⟨rfl, rfl⟩
    · cases computed

/-- Before Altair, a deposit to a new key with a valid signature adds a validator and its balance.
-/
theorem applyDeposit_new_valid {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature} (before : fork < .altair)
    (new : state.validators.data.findIdx? (·.pubkey == pubkey) = none)
    (valid : isValidDepositSignature config checks pubkey withdrawalCredentials amount signature =
      .ok true)
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    after.validators.data = state.validators.data.push
        (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount) ∧
      after.balances.data = state.balances.data.push amount := by
  have notElectra : ¬Fork.pectra ≤ fork := fun le =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans before (by decide)) le)
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  have notHeze : ¬Fork.hegota ≤ fork := fun le =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans before (by decide)) le)
  simp only [applyDeposit, notElectra, ↓reduceDIte, applyPendingDeposit, new, valid, bind,
    Except.bind, ↓reduceIte, addValidatorToRegistry, notAltair, notHeze, false_and] at computed
  split at computed
  · cases computed
    exact ⟨rfl, rfl⟩
  · cases computed

/-- Before Electra, a deposit to a new key with an invalid signature changes nothing. -/
theorem applyDeposit_new_invalid {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature} (before : fork < .pectra)
    (new : state.validators.data.findIdx? (·.pubkey == pubkey) = none)
    (invalid : isValidDepositSignature config checks pubkey withdrawalCredentials amount signature =
      .ok false) :
    applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok state := by
  have notElectra : ¬Fork.pectra ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp [applyDeposit, applyPendingDeposit, notElectra, new, invalid, bind, Except.bind, pure,
    Except.pure]

/-- A credited deposit keeps one balance for each validator, and the deposit data. -/
theorem applyPendingDeposit_kept {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    (BalancesMatch state → BalancesMatch after) ∧
      after.eth1DepositIndex = state.eth1DepositIndex ∧ after.eth1Data = state.eth1Data := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact ⟨id, rfl, rfl⟩
    simp only [bind, Except.bind] at computed
    split at computed
    · cases computed
    split at computed
    · exact ⟨balancesMatch_addValidatorToRegistry computed, addValidatorToRegistry_eth1 computed⟩
    · cases computed
      exact ⟨id, rfl, rfl⟩
  · rw [liftAccessor_ok] at computed
    refine ⟨balancesMatch_of_sameSizes (sameSizes_increaseBalance computed), ?_⟩
    obtain ⟨_, set⟩ := increaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact ⟨rfl, rfl⟩

/-- A new validator is the only change to the registry.

Each validator after is the validator at the same index before, or the validator of the deposit.
-/
theorem addValidatorToRegistry_validator {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    {i : Nat} {validator : Validator} (found : after.validators.data[i]? = some validator) :
    state.validators.data[i]? = some validator ∨
      validator = getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rw [setOrAppendList_getElem? validatorsOk] at found
    split at found
    · exact .inr (Option.some.inj found).symm
    · exact .inl found
  · split at computed
    · cases computed
      rw [Array.getElem?_push] at found
      split at found
      · exact .inr (Option.some.inj found).symm
      · exact .inl found
    · cases computed

/-- From Heze, a deposit to a new key with BLS withdrawal credentials changes nothing. -/
theorem applyPendingDeposit_of_blsCredentials {deposit : PendingDeposit} (heze : .hegota ≤ fork)
    (new : state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = none)
    (bls : deposit.withdrawalCredentials[0] = BLS_WITHDRAWAL_PREFIX[0]) :
    applyPendingDeposit config checks state deposit = .ok state := by
  simp only [applyPendingDeposit, new, heze, bls, and_self, ↓reduceIte, pure, Except.pure]

/-- From Heze, a credited deposit creates no validator with BLS withdrawal credentials.

Each validator after with BLS credentials is the validator at the same index before. -/
theorem applyPendingDeposit_blsValidator {deposit : PendingDeposit} (heze : .hegota ≤ fork)
    (computed : applyPendingDeposit config checks state deposit = .ok after) {i : Nat}
    {validator : Validator} (found : after.validators.data[i]? = some validator)
    (bls : validator.withdrawalCredentials[0] = BLS_WITHDRAWAL_PREFIX[0]) :
    state.validators.data[i]? = some validator := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact found
    rename_i notBls
    simp only [bind, Except.bind] at computed
    split at computed
    · cases computed
    split at computed
    · refine (addValidatorToRegistry_validator computed found).resolve_right fun added => ?_
      subst added
      exact notBls ⟨heze, bls⟩
    · cases computed
      exact found
  · rw [liftAccessor_ok] at computed
    obtain ⟨_, set⟩ := increaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact found

/-- From Electra, a deposit keeps one balance for each validator, and the deposit data. -/
theorem applyDepositElectra_kept {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials amount
      signature = .ok after) :
    (BalancesMatch state → BalancesMatch after) ∧
      after.eth1DepositIndex = state.eth1DepositIndex ∧ after.eth1Data = state.eth1Data := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind, Except.bind] at computed
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i added
      have matched := balancesMatch_addValidatorToRegistry added
      have kept := addValidatorToRegistry_eth1 added
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact ⟨matched, kept⟩
    · cases computed
      exact ⟨id, rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact ⟨id, rfl, rfl⟩

/-- A deposit keeps one balance for each validator. -/
theorem balancesMatch_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  unfold applyDeposit at computed
  split at computed
  · exact (applyDepositElectra_kept computed).1 holds
  · exact (applyPendingDeposit_kept computed).1 holds

/-- A deposit keeps the deposit data and the next deposit index. -/
theorem applyDeposit_eth1 {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    after.eth1DepositIndex = state.eth1DepositIndex ∧ after.eth1Data = state.eth1Data := by
  unfold applyDeposit at computed
  split at computed
  · exact (applyDepositElectra_kept computed).2
  · exact (applyPendingDeposit_kept computed).2

/-- Recording the start of the deposit requests changes no other field of the state. -/
theorem recordDepositRequestsStart_eq {index : UInt64} :
    ∃ start, recordDepositRequestsStart state index =
      { state with depositRequestsStartIndex := start } := by
  unfold recordDepositRequestsStart
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨state.depositRequestsStartIndex, rfl⟩
  · exact ⟨state.depositRequestsStartIndex, rfl⟩

/-- From Electra, a deposit request joins the end of the pending deposits, at the current slot.

The registry and the balances stay. -/
theorem processDepositRequest_ok {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    (after.pendingDeposits electra).data = (state.pendingDeposits electra).data.push
        ⟨request.pubkey, request.withdrawalCredentials, request.amount, request.signature,
          state.slot⟩ ∧
      after.validators = state.validators ∧ after.balances = state.balances := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨pending, appended, rfl⟩ := computed
  exact ⟨appendWithinLimit_data appended, rfl, rfl⟩

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

/-- Before Deneb, the domain of a voluntary exit is that of the fork at the epoch of the exit. -/
theorem voluntaryExitDomain_of_lt {epoch : Epoch} (before : fork < .dencun) :
    voluntaryExitDomain config state epoch =
      liftAccessor (getDomain config state DOMAIN_VOLUNTARY_EXIT (some epoch)) := by
  have notDeneb : ¬Fork.dencun ≤ fork := Nat.not_le.mpr before
  simp only [voluntaryExitDomain, notDeneb, ↓reduceIte]

/-- From Deneb, the domain of a voluntary exit is that of the fork version of Capella.

It depends on neither the epoch of the exit nor the fork of the state. -/
theorem voluntaryExitDomain_of_dencun {epoch : Epoch} (dencun : .dencun ≤ fork) :
    voluntaryExitDomain config state epoch =
      liftSsz (computeDomain config DOMAIN_VOLUNTARY_EXIT config.CAPELLA_FORK_VERSION
        state.genesisValidatorsRoot) := by
  simp only [voluntaryExitDomain, dencun, ↓reduceIte]

/-- A valid voluntary exit is from an active validator that has not started to exit.

The exit is not for a later epoch, and the validator has been active for long enough.

From Electra the validator has no pending partial withdrawal.

The validator signs the exit, under the domain of a voluntary exit. -/
theorem processVoluntaryExit_checks {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    ∃ validator, getValidator state signed.message.validatorIndex = .ok validator ∧
      isActiveValidator validator (getCurrentEpoch state) = true ∧
      validator.exitEpoch = FAR_FUTURE_EPOCH ∧
      signed.message.epoch ≤ getCurrentEpoch state ∧
      validator.activationEpoch.toNat + config.SHARD_COMMITTEE_PERIOD.toNat ≤
        (getCurrentEpoch state).toNat ∧
      checkNoPendingWithdrawal state signed.message.validatorIndex = .ok () ∧
      ∃ domain signingRoot,
        voluntaryExitDomain config state signed.message.epoch = .ok domain ∧
        computeSigningRoot signed.message domain = .ok signingRoot ∧
        checks.verify (packBytes validator.pubkey) (packBytes signingRoot)
          (packBytes signed.signature) = true := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at computed
  obtain ⟨validator, found, _, active, _, notExiting, _, notLater, eligible, ⟨_, summed⟩, _,
    longEnough, ⟨⟩, noPending, domain, domainOk, signingRoot, rootOk, _, verified, _⟩ := computed
  refine ⟨validator, found, active, notExiting, notLater, ?_, noPending, domain,
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
  obtain ⟨validator, found, _, notExiting, _⟩ := processVoluntaryExit_checks computed
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, found', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
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
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact sameSizes_initiateValidatorExit exited

/-! ## All the operations of a block -/

/-- Before Electra, a valid block holds every outstanding deposit, up to the most per block. -/
theorem processOperations_deposits (beforeElectra : fork < .pectra)
    {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∀ before : fork < .hegota,
      (state.eth1DepositIndex before).toNat ≤ (state.eth1Data before).depositCount.toNat ∧
      (body.deposits before).data.size =
        min preset.MAX_DEPOSITS.toNat
          ((state.eth1Data before).depositCount.toNat - (state.eth1DepositIndex before).toNat) := by
  intro _
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le.mpr beforeElectra
  have notFulu : ¬Fork.fusaka ≤ fork := fun le => notElectra (Nat.le_trans (by decide) le)
  unfold processOperations at computed
  split at computed
  · exact absurd ‹_› fun gloas => notElectra (Nat.le_trans (by decide) gloas)
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨expected, expectedOk, _, count, _⟩ := computed
  simp only [expectedDepositCount, notFulu, notElectra, ↓reduceIte, ↓reduceDIte, bind_ok_iff,
    liftAccessor_ok, liftArith, mapError_ok_iff, subChecked_ok_iff, pure, Except.pure,
    Except.ok.injEq] at expectedOk
  obtain ⟨outstanding, ⟨noUnderflow, difference⟩, rfl⟩ := expectedOk
  refine ⟨UInt64.le_iff_toNat_le.mp noUnderflow, ?_⟩
  rw [count, UInt64.min_def]
  split
  · rename_i le
    have := UInt64.le_iff_toNat_le.mp le
    omega
  · rename_i gt
    have := mt UInt64.le_iff_toNat_le.mpr gt
    omega

/-- From Fulu, the expected number of deposits is zero. -/
theorem expectedDepositCount_of_fusaka (fulu : .fusaka ≤ fork) {before : fork < .hegota} :
    expectedDepositCount state before = .ok 0 := by
  simp only [expectedDepositCount, fulu, ↓reduceIte]
  rfl

/-- From Gloas, a valid block holds no more operations of each kind than the most per block. -/
theorem processOperationsGloas_counts {body : BeaconBlockBody preset fork}
    {gloas : .glamsterdam ≤ fork}
    (computed : processOperationsGloas config checks state body gloas parentSlot = .ok after) :
    body.proposerSlashings.data.size ≤ preset.MAX_PROPOSER_SLASHINGS.toNat ∧
      body.attesterSlashings.data.size ≤ preset.MAX_ATTESTER_SLASHINGS_ELECTRA.toNat ∧
      body.attestations.data.size ≤ preset.MAX_ATTESTATIONS_ELECTRA.toNat ∧
      body.voluntaryExits.data.size ≤ preset.MAX_VOLUNTARY_EXITS.toNat ∧
      (body.blsToExecutionChanges (Nat.le_trans (by decide) gloas)).data.size ≤
        preset.MAX_BLS_TO_EXECUTION_CHANGES.toNat ∧
      (body.payloadAttestations gloas).data.size ≤ preset.MAX_PAYLOAD_ATTESTATIONS.toNat := by
  unfold processOperationsGloas at computed
  simp only [bind_ok_iff, checkCount, ensure_ok_iff] at computed
  obtain ⟨_, _, _, proposers, _, attesters, _, attestations, _, exits, _, changes, _, payloads,
    _⟩ := computed
  exact ⟨proposers, attesters, attestations, exits, changes, payloads⟩

/-- From Fulu, a valid block holds no deposit. -/
theorem processOperations_no_deposit (fulu : .fusaka ≤ fork) {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∀ before : fork < .hegota, (body.deposits before).data.size = 0 := by
  intro before
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [before, ↓reduceDIte, bind_ok_iff, ensure_ok_iff] at computed
    obtain ⟨_, zero, _⟩ := computed
    exact zero
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  rw [expectedDepositCount_of_fusaka fulu] at computed
  obtain ⟨_, zero, rest⟩ := computed
  simp only [Except.ok.injEq] at zero
  subst zero
  obtain ⟨_, sized, _⟩ := rest
  simpa using sized

end EthLib.Consensus
