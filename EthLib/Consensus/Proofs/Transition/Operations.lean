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

From Electra, the committees of an attestation, cut from one shuffle, are checked each in turn.

A deposit lies in the deposit tree, and moves the next deposit index on by one.

A deposit to a known key adds its amount to the sum of the balances.

A valid deposit to a new key adds one validator and its balance.

An invalid deposit to a new key changes nothing.

A deposit to a known key raises the balance at the index of that key, and no other.

From Electra a deposit request joins the end of the pending deposits.

A voluntary exit is signed by an active validator, which then has an exit epoch.

The operations of a block hold every outstanding deposit, up to the most per block.

They keep one balance for each validator.

From Gloas, an attestation weighs the payment of its slot by the balances of its new attesters.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {parentSlot : Slot}

/-- The sum of the balances, on natural numbers. -/
def balanceSum (state : BeaconState preset fork) : Nat :=
  (state.balances.data.toList.map (·.toNat)).sum

/-- The sum of the amounts of a list of pending deposits, on natural numbers. -/
def pendingAmount (deposits : List PendingDeposit) : Nat :=
  (deposits.map (·.amount.toNat)).sum

/-- The registry and the balances have one entry for each validator. -/
def BalancesMatch (state : BeaconState preset fork) : Prop :=
  state.balances.data.size = state.validators.data.size

/-- The public keys of the validators, in the order of the registry. -/
def validatorKeys (state : BeaconState preset fork) : List BLSPubkey :=
  state.validators.data.toList.map (·.pubkey)

/-- No two validators of the registry have the same public key. -/
def PubkeysDistinct (state : BeaconState preset fork) : Prop :=
  (validatorKeys state).Nodup

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
  have countOk := getCommitteeCountPerSlotChecked_of_within
    (state.validators.bound (Nat.lt_trans before (by decide))) attestation.data.target.epoch
  dsimp only at computed
  rw [countOk] at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, Except.ok.injEq] at computed
  obtain ⟨_, recent, _, slotEpoch, earliest, ⟨_, earliestSum⟩, _, early, latest,
    ⟨_, latestSum⟩, _, late, count, countEq, _, index, committee, found, _, bits,
    _, _, _, source, _⟩ :=
    computed
  subst count
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
  have countOk := getCommitteeCountPerSlotChecked_of_within
    (state.validators.bound (Nat.lt_trans before (by decide))) attestation.data.target.epoch
  dsimp only at computed
  rw [countOk] at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposer, proposerOk, _, _,
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

/-- From Electra: with a shuffle that has a value, the committees are checked on that shuffle.

Each index is checked against the count of committees per slot of the target epoch.

Each committee is cut with the count of committees per slot of the epoch of the slot. -/
theorem attestationCommitteesSize_of_attesterShuffle {data : AttestationData}
    {active : Array ValidatorIndex} {shuffled : Array UInt64}
    (shuffleOk :
      attesterShuffle state (computeEpochAtSlot preset data.slot) = .ok (active, shuffled))
    (countOk : getCommitteeCountPerSlotChecked state data.target.epoch =
      .ok (getCommitteeCountPerSlot state data.target.epoch))
    (bits : Array Bool) (committees : List CommitteeIndex) (offset : Nat) :
    attestationCommitteesSize state data bits committees offset =
      attestationCommitteesSizeOf preset data.slot bits
        (getCommitteeCountPerSlot state data.target.epoch)
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset data.slot)) active shuffled
        committees offset := by
  cases committees with
  | nil => rfl
  | cons index rest =>
    simp only [attestationCommitteesSize, attestationCommitteesSizeOf, countOk, shuffleOk,
      liftAccessor,
      Except.mapError, bind, Except.bind]
    -- The left side checks the first index twice, and a check that passed passes again.
    cases ensure (index < getCommitteeCountPerSlot state data.target.epoch)
      (TransitionError.committeeIndexOutOfRange index
        (getCommitteeCountPerSlot state data.target.epoch)) <;> rfl

/-- From Electra: the total size of no committee is the offset that it starts from. -/
theorem attestationCommitteesSize_nil (data : AttestationData) (bits : Array Bool)
    (offset : Nat) : attestationCommitteesSize state data bits [] offset = .ok offset :=
  rfl

/-- From Electra: the total size of a list of committees adds the first committee, then the rest.

The committees share one shuffle, and the first committee alone passes the same checks.

The two sides fail with the same error too. -/
theorem attestationCommitteesSize_cons (data : AttestationData) (bits : Array Bool)
    (index : CommitteeIndex) (rest : List CommitteeIndex) (offset : Nat) :
    attestationCommitteesSize state data bits (index :: rest) offset = (do
      let count ← liftAccessor (getCommitteeCountPerSlotChecked state data.target.epoch)
      ensure (index < count) (.committeeIndexOutOfRange index count)
      let committee ← liftAccessor (getBeaconCommittee state data.slot index)
      let attesters ← liftAccessor (committeeAttesters bits offset committee)
      ensure (attesters ≠ []) (.noCommitteeAttester index)
      attestationCommitteesSize state data bits rest (offset + committee.size)) := by
  cases countOk : getCommitteeCountPerSlotChecked state data.target.epoch with
  | error error =>
    simp [attestationCommitteesSize, countOk, liftAccessor, Except.mapError, bind, Except.bind]
  | ok count =>
    have same := getCommitteeCountPerSlotChecked_ok countOk
    subst count
    rw [getBeaconCommittee_eq]
    -- A committee reads the shuffle after its index is checked, so both sides fail in one order.
    cases shuffleOk : attesterShuffle state (computeEpochAtSlot preset data.slot) with
    | error e =>
      simp only [attestationCommitteesSize, countOk, shuffleOk, liftAccessor, Except.mapError, bind,
        Except.bind]
    | ok pair =>
      obtain ⟨active, shuffled⟩ := pair
      simp only [attestationCommitteesSize_of_attesterShuffle shuffleOk countOk,
        attestationCommitteesSizeOf, liftAccessor, Except.mapError, bind, Except.bind]

/-- Each committee that a checked attestation names has an index below the count.

The count is that of the committees in each slot of the target epoch. -/
theorem lt_getCommitteeCountPerSlot_of_checkAttestationCommittees
    {attestation : Attestation preset fork} {index : CommitteeIndex}
    (checked : checkAttestationCommittees state attestation = .ok ())
    (named : if electra : .pectra ≤ fork then
        index ∈ getCommitteeIndices (attestation.committeeBits electra)
      else index = attestation.data.index) :
    index < getCommitteeCountPerSlot state attestation.data.target.epoch := by
  -- Each committee of the walk has its index checked against the count.
  have walk : ∀ {committees : List CommitteeIndex} {offset size : Nat},
      attestationCommitteesSize state attestation.data attestation.aggregationBits.bits
        committees offset = .ok size →
      index ∈ committees →
        index < getCommitteeCountPerSlot state attestation.data.target.epoch := by
    intro committees
    induction committees with
    | nil =>
      intro _ _ _ mem
      simp at mem
    | cons first rest ih =>
      intro offset size sized mem
      rw [attestationCommitteesSize_cons] at sized
      obtain ⟨count, countOk, sized⟩ := bind_ok_iff.mp sized
      rw [getCommitteeCountPerSlotChecked_ok (liftAccessor_ok.mp countOk)] at sized
      obtain ⟨below, sized⟩ := bind_unit_ok_iff.mp sized
      obtain ⟨committee, -, sized⟩ := bind_ok_iff.mp sized
      obtain ⟨attesters, -, sized⟩ := bind_ok_iff.mp sized
      obtain ⟨-, sized⟩ := bind_unit_ok_iff.mp sized
      rcases List.mem_cons.mp mem with rfl | later
      · exact ensure_ok_iff.mp below
      · exact ih sized later
  by_cases electra : .pectra ≤ fork
  · simp only [electra, ↓reduceDIte] at named
    simp only [checkAttestationCommittees, electra, ↓reduceDIte] at checked
    obtain ⟨size, sizeOk⟩ : ∃ size, attestationCommitteesSize state attestation.data
        attestation.aggregationBits.bits
        (getCommitteeIndices (attestation.committeeBits electra)) 0 = .ok size := by
      split at checked <;>
      · obtain ⟨size, sizeOk, -⟩ := bind_ok_iff.mp (bind_unit_ok_iff.mp checked).2
        exact ⟨size, sizeOk⟩
    exact walk sizeOk named
  · simp only [electra, ↓reduceDIte] at named
    subst named
    simp only [checkAttestationCommittees, electra, ↓reduceDIte] at checked
    obtain ⟨count, countOk, checked⟩ := bind_ok_iff.mp checked
    rw [getCommitteeCountPerSlotChecked_ok (liftAccessor_ok.mp countOk)] at checked
    exact ensure_ok_iff.mp (bind_unit_ok_iff.mp checked).1

/-- An attester of an attestation that passes the committee check sits in one of its committees.

That committee is one of the slot of the attestation.

Its index is below the count of committees in each slot of the target epoch. -/
theorem exists_mem_getBeaconCommittee_of_checkAttestationCommittees
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    {validator : ValidatorIndex}
    (checked : checkAttestationCommittees state attestation = .ok ())
    (indexedOk : getIndexedAttestation state attestation = .ok indexed)
    (attests : validator ∈ indexed.attestingIndices.data.toList) :
    ∃ index committee,
      index < getCommitteeCountPerSlot state attestation.data.target.epoch ∧
      getBeaconCommittee state attestation.data.slot index = .ok committee ∧
      validator ∈ committee := by
  obtain ⟨attesters, attestersOk, data⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
  rw [data] at attests
  obtain ⟨index, committee, named, committeeOk, member⟩ :=
    exists_mem_getBeaconCommittee_of_getAttestingIndices attestersOk (by simpa using attests)
  exact ⟨index, committee, lt_getCommitteeCountPerSlot_of_checkAttestationCommittees checked named,
    committeeOk, member⟩

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
        attestationPaymentPosition preset current data.slot] := by
    rw [RootedVector.getElem?_eq]
    exact Vector.getElem?_eq_getElem inside
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
    apply RootedVector.ext
    rw [RootedVector.elements_set]
    ext index bound
    by_cases same : index = attestationPaymentPosition preset current data.slot
    · subst same
      simp
      rfl
    · exact Vector.getElem_set_ne _ _ (Ne.symm same)
  simp only [kept]

/-- From Gloas, the weight of a payment after one attester.

The attester must have an entry in both participation lists, else the index is out of range.

It adds its effective balance exactly when it had no flag before and has one after.

It must then be in the registry, and the sum must be below `2^64`, else it is an overflow.

An attester that had a flag before, or has none after, leaves the weight as it was. -/
theorem addPaymentWeight_eq_ok_iff {before updated : EpochParticipation preset fork}
    {weight result : Gwei} {index : ValidatorIndex} :
    addPaymentWeight state before updated weight index = .ok result ↔
      ∃ old new, before.data[index.toNat]? = some old ∧ updated.data[index.toNat]? = some new ∧
        if old = 0 ∧ new ≠ 0 then
          ∃ validator, state.validators.data[index.toNat]? = some validator ∧
            weight.toNat + validator.effectiveBalance.toNat < 2 ^ 64 ∧
            result.toNat = weight.toNat + validator.effectiveBalance.toNat
        else result = weight := by
  unfold addPaymentWeight
  rcases oldAt : before.data[index.toNat]? with _ | old
  · simp
  rcases newAt : updated.data[index.toNat]? with _ | new
  · simp
  simp only [Option.some.injEq, exists_and_left, exists_eq_left']
  by_cases zero : old = 0
  · subst zero
    by_cases unflagged : new = 0
    · subst unflagged
      simp [pure, Except.pure, eq_comm]
    · rcases found : state.validators.data[index.toNat]? with _ | validator <;>
        simp [unflagged, found, getValidator, bind_ok_iff, liftAccessor_ok, liftArith,
          mapError_ok_iff, addChecked_ok_iff]
  · simp [zero, pure, Except.pure, eq_comm]

/-- From Gloas, an attester that already had a flag in the epoch adds no weight to a payment.

That holds even when the attester gains another flag. -/
theorem addPaymentWeight_of_ne_zero {before updated : EpochParticipation preset fork}
    {weight : Gwei} {index : ValidatorIndex} {old new : ParticipationFlags}
    (oldAt : before.data[index.toNat]? = some old) (flagged : old ≠ 0)
    (newAt : updated.data[index.toNat]? = some new) :
    addPaymentWeight state before updated weight index = .ok weight :=
  addPaymentWeight_eq_ok_iff.mpr ⟨old, new, oldAt, newAt, by simp [flagged]⟩

/-- From Gloas, when no attester fails, the attesters add their effective balances to a weight.

Each adds its balance when it had no flag before and has one after, and nothing otherwise. -/
theorem foldlM_addPaymentWeight {before updated : EpochParticipation preset fork} :
    ∀ {attesters : List ValidatorIndex} {weight result : Gwei},
      attesters.foldlM (addPaymentWeight state before updated) weight = .ok result →
        result.toNat = weight.toNat + (attesters.map fun index =>
          if before.data[index.toNat]? = some 0 ∧ updated.data[index.toNat]? ≠ some 0 then
            ((state.validators.data[index.toNat]?).map (·.effectiveBalance.toNat)).getD 0
          else 0).sum
  | [], _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    simp [computed]
  | index :: rest, weight, result, computed => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, step, folded⟩ := computed
    rw [foldlM_addPaymentWeight folded, List.map_cons, List.sum_cons, ← Nat.add_assoc]
    congr 1
    obtain ⟨old, new, oldAt, newAt, value⟩ := addPaymentWeight_eq_ok_iff.mp step
    rw [oldAt, newAt]
    split at value
    · rename_i fresh
      obtain ⟨validator, found, _, sum⟩ := value
      simp [fresh, found, sum]
    · rename_i fresh
      have notFresh : ¬(some old = some (0 : ParticipationFlags) ∧ some new ≠ some 0) := by
        simpa using fresh
      simp only [notFresh, value, ite_false, Nat.add_zero]

/-- From Gloas, an attestation weighs the payment of its slot by the balances of its new attesters.

A new attester had no flag in the epoch before the attestation and has one after it.

Only a vote for the block of its own slot weighs, and only a payment of a positive amount.

Only the weight of the payment changes. -/
theorem recordPaymentWeight_weight {gloas : .glamsterdam ≤ fork} {data : AttestationData}
    {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex} {sameSlot : Bool} {payment : BuilderPendingPayment}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after)
    (same : isAttestationSameSlot state data = .ok sameSlot)
    (found : (state.builderPendingPayments gloas)[
      attestationPaymentPosition preset current data.slot]? = some payment) :
    ∃ weight : Gwei, (after.builderPendingPayments gloas)[
        attestationPaymentPosition preset current data.slot]? = some { payment with weight } ∧
      weight.toNat = payment.weight.toNat +
        if sameSlot = true ∧ 0 < payment.withdrawal.amount then
          (attesters.map fun index =>
            if before.data[index.toNat]? = some 0 ∧ updated.data[index.toNat]? ≠ some 0 then
              ((state.validators.data[index.toNat]?).map (·.effectiveBalance.toNat)).getD 0
            else 0).sum
        else 0 := by
  unfold recordPaymentWeight at computed
  dsimp only at computed
  split at computed
  rotate_left
  · cases computed
  rename_i inside
  have stored : (state.builderPendingPayments gloas)[
      attestationPaymentPosition preset current data.slot] = payment := by
    rw [RootedVector.getElem?_eq, Vector.getElem?_eq_getElem inside] at found
    exact Option.some.inj found
  subst stored
  simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨sameSlot', sameOk, weight, weightOk, rfl⟩ := computed
  rw [same, Except.ok.injEq] at sameOk
  subst sameOk
  refine ⟨weight, by simp, ?_⟩
  split at weightOk
  · rename_i weighs
    simp only [weighs, and_self, ite_true]
    exact foldlM_addPaymentWeight weightOk
  · rename_i weighs
    simp only [Except.ok.injEq] at weightOk
    simp [weighs, weightOk]

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
  simp only [applyPendingDeposit, known, liftAccessor_ok, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
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

/-- A set or an append on a rooted list adds one entry exactly when the index is its size. -/
theorem setOrAppendRooted_size {switch : Base.Fork} {α : Type} [SszType α] {limit : Nat}
    {list list' : RootedForkList switch fork α limit} {index : UInt64} {value : α}
    (computed : setOrAppendRooted list index value = .ok list') :
    list'.data.size = if index.toNat = list.data.size then list.data.size + 1
      else list.data.size := by
  unfold setOrAppendRooted at computed
  split at computed
  · rename_i atEnd
    split at computed
    · cases computed
      simp [atEnd]
    · cases computed
  · rename_i notEnd
    split at computed
    · cases computed
      simp [notEnd]
    · cases computed

/-- A set or an append on a rooted list has the outcome of the plain one, on the elements. -/
theorem setOrAppendRooted_toForkList {switch : Base.Fork} {α : Type} [SszType α] {limit : Nat}
    (list : RootedForkList switch fork α limit) (index : UInt64) (value : α) :
    RootedForkList.toForkList <$> setOrAppendRooted list index value
      = setOrAppendList list.toForkList index value := by
  unfold setOrAppendRooted setOrAppendList appendWithinLimit
  by_cases atEnd : index.toNat = list.data.size
  · have atEnd' : index.toNat = list.toForkList.data.size := atEnd
    by_cases fits : fork < switch → list.data.size + 1 ≤ limit
    · have fits' : fork < switch → list.toForkList.data.size + 1 ≤ limit := fits
      rw [ite_eq_left atEnd, ite_eq_left atEnd', dite_eq_left fits, dite_eq_left fits']
      rfl
    · have fits' : ¬(fork < switch → list.toForkList.data.size + 1 ≤ limit) := fits
      rw [ite_eq_left atEnd, ite_eq_left atEnd', dite_eq_right fits, dite_eq_right fits']
      rfl
  · by_cases inside : index.toNat < list.data.size
    · simp [atEnd, inside, RootedForkList.toForkList, Functor.map, Except.map]
    · simp [atEnd, inside, RootedForkList.toForkList, Functor.map, Except.map]

/-- A set or an append on a rooted list puts the value at the index, and keeps the rest. -/
theorem setOrAppendRooted_getElem? {switch : Base.Fork} {α : Type} [SszType α] {limit : Nat}
    {list list' : RootedForkList switch fork α limit} {index : UInt64} {value : α}
    (computed : setOrAppendRooted list index value = .ok list') (i : Nat) :
    list'.data[i]? = if i = index.toNat then some value else list.data[i]? := by
  have plain := setOrAppendRooted_toForkList list index value
  rw [computed] at plain
  exact setOrAppendList_getElem? plain.symm i

/-- The index of a new validator is the size of the registry, which must be below `2^64`. -/
theorem getIndexForNewValidator_ok_iff {index : ValidatorIndex} :
    getIndexForNewValidator state = .ok index ↔
      state.validators.data.size < 2 ^ 64 ∧ index.toNat = state.validators.data.size := by
  rw [getIndexForNewValidator, liftArith, mapError_ok_iff, ofNatChecked_ok_iff]

/-- From Altair, a new validator keeps the deposit data and the next deposit index. -/
theorem addValidatorToRegistryAltair_eth1 {altair : .altair ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistryAltair state altair pubkey withdrawalCredentials amount =
      .ok after) :
    after.eth1DepositIndex = state.eth1DepositIndex ∧ after.eth1Data = state.eth1Data := by
  unfold addValidatorToRegistryAltair at computed
  simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
  exact ⟨rfl, rfl⟩

/-- From Altair, a new validator keeps one balance for each validator. -/
theorem balancesMatch_addValidatorToRegistryAltair {altair : .altair ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistryAltair state altair pubkey withdrawalCredentials amount =
      .ok after) (holds : BalancesMatch state) : BalancesMatch after := by
  unfold addValidatorToRegistryAltair at computed
  simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, validators, validatorsOk, balances, balancesOk, _, _, _, _, _, _, rfl⟩ := computed
  unfold BalancesMatch at holds ⊢
  rw [setOrAppendRooted_size validatorsOk, setOrAppendList_size balancesOk, holds]

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
      simp only [Array.size_push, RootedForkList.data_push, holds]
    · cases computed

/-- A new validator joins the end of the registry. -/
theorem addValidatorToRegistry_validators_eq_push {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    after.validators.data = state.validators.data.push
      (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount) := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, indexOk, _, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    simp only [setOrAppendRooted, atEnd, ↓reduceIte] at validatorsOk
    split at validatorsOk
    · cases validatorsOk
      rfl
    · cases validatorsOk
  · split at computed
    · cases computed
      rfl
    · cases computed

/-- Adding a validator keeps the slot. -/
theorem addValidatorToRegistry_slot {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    after.slot = state.slot := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rfl
  split at computed
  · cases computed
    rfl
  · cases computed

/-- A new validator joins a registry of fewer than `2^64` validators.

So its position fits a validator index. -/
theorem addValidatorToRegistry_size_lt {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    state.validators.data.size < 2 ^ 64 := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, indexOk, _⟩ := computed
    exact (getIndexForNewValidator_ok_iff.mp indexOk).1
  · split at computed
    · rename_i fits
      exact Nat.lt_trans fits.1 preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    · cases computed

/-- A new validator joins the end of the registry, and its balance joins the end of the balances.

That needs one balance for each validator. -/
theorem addValidatorToRegistry_push {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    (holds : BalancesMatch state) :
    after.validators.data = state.validators.data.push
        (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount) ∧
      after.balances.data = state.balances.data.push amount := by
  refine ⟨addValidatorToRegistry_validators_eq_push computed, ?_⟩
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨index, indexOk, _, _, _, balancesOk, _, _, _, _, _, _, rfl⟩ := computed
    -- The index is the size of the registry, and so the size of the balances.
    have atBalances : index.toNat = state.balances.data.size := by
      rw [(getIndexForNewValidator_ok_iff.mp indexOk).2, holds]
    simp only [setOrAppendList, atBalances, ↓reduceIte, appendWithinLimit] at balancesOk
    split at balancesOk
    · cases balancesOk
      rfl
    · cases balancesOk
  · split at computed
    · cases computed
      rfl
    · cases computed

/-- A new validator raises the sum of the balances by at most its amount. -/
private theorem balanceSum_addValidatorToRegistry_le {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    balanceSum after ≤ balanceSum state + amount.toNat := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨index, _, _, _, balances, balancesOk, _, _, _, _, _, _, rfl⟩ := computed
    unfold setOrAppendList at balancesOk
    split at balancesOk
    · simp only [appendWithinLimit] at balancesOk
      split at balancesOk
      · cases balancesOk
        simp [balanceSum]
      · cases balancesOk
    · split at balancesOk
      · rename_i inside
        cases balancesOk
        -- Overwriting one balance raises the sum by at most the amount.
        unfold balanceSum
        simp only [Array.toList_set, List.map_set]
        have := sum_set_add (l := state.balances.data.toList.map (·.toNat))
          (i := index.toNat) (by simpa using inside) amount.toNat
        omega
      · cases balancesOk
  · split at computed
    · cases computed
      simp [balanceSum]
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
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
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
    obtain ⟨_, _, validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rw [setOrAppendRooted_getElem? validatorsOk] at found
    split at found
    · exact .inr (Option.some.inj found).symm
    · exact .inl found
  · split at computed
    · cases computed
      rw [RootedForkList.data_push, Array.getElem?_push] at found
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
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    obtain ⟨_, set⟩ := increaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact found

/-- A pending deposit is droppable at a state under two conditions.

No validator has its key.

Its signature is invalid or, from Heze, it has BLS withdrawal credentials. -/
def DepositDroppable (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (deposit : PendingDeposit) : Prop :=
  state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = none ∧
    (isValidDepositSignature config checks deposit.pubkey deposit.withdrawalCredentials
        deposit.amount deposit.signature = .ok false ∨
      .hegota ≤ fork ∧ deposit.withdrawalCredentials[0] = BLS_WITHDRAWAL_PREFIX[0])

/-- A deposit droppable at a state is droppable at an earlier one whose validators all stay. -/
private theorem DepositDroppable.of_kept {earlier : BeaconState preset fork}
    {deposit : PendingDeposit}
    (kept : ∀ validator ∈ earlier.validators.data, validator ∈ state.validators.data)
    (droppable : DepositDroppable config checks state deposit) :
    DepositDroppable config checks earlier deposit := by
  refine ⟨?_, droppable.2⟩
  have unknown := Array.findIdx?_eq_none_iff.mp droppable.1
  exact Array.findIdx?_eq_none_iff.mpr fun validator member => unknown validator (kept _ member)

/-- Applying a droppable deposit changes nothing. -/
theorem applyPendingDeposit_of_droppable {deposit : PendingDeposit}
    (droppable : DepositDroppable config checks state deposit) :
    applyPendingDeposit config checks state deposit = .ok state := by
  obtain ⟨new, invalid | ⟨heze, bls⟩⟩ := droppable
  · simp [applyPendingDeposit, new, invalid, bind, Except.bind, pure, Except.pure]
  · exact applyPendingDeposit_of_blsCredentials heze new bls

/-- A deposit adds its amount to the sum of the balances, or it is droppable and changes nothing.

That needs one balance for each validator. -/
theorem balanceSum_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (holds : BalancesMatch state) :
    balanceSum after = balanceSum state + deposit.amount.toNat ∨
      after = state ∧ DepositDroppable config checks state deposit := by
  unfold applyPendingDeposit at computed
  split at computed
  · rename_i unknown
    split at computed
    · rename_i bls
      cases computed
      exact .inr ⟨rfl, unknown, .inr bls⟩
    simp only [bind_ok_iff] at computed
    obtain ⟨valid, checked, computed⟩ := computed
    split at computed
    · have pushed := (addValidatorToRegistry_push computed holds).2
      exact .inl (by simp [balanceSum, pushed])
    · rename_i invalid
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      simp only [Bool.not_eq_true] at invalid
      subst invalid
      exact .inr ⟨computed.symm, unknown, .inl checked⟩
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact .inl (balanceSum_increaseBalance computed)

/-- A deposit raises the sum of the balances by at most its amount. -/
theorem balanceSum_applyPendingDeposit_le {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    balanceSum after ≤ balanceSum state + deposit.amount.toNat := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact Nat.le_add_right _ _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact balanceSum_addValidatorToRegistry_le computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact Nat.le_add_right _ _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact Nat.le_of_eq (balanceSum_increaseBalance computed)

/-- A valid deposit to a new key adds its validator and its amount at the ends of their lists.

From Heze that needs withdrawal credentials other than BLS.

It also needs one balance for each validator. -/
theorem applyPendingDeposit_new_valid {deposit : PendingDeposit}
    (new : state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = none)
    (notBls : ¬(.hegota ≤ fork ∧ deposit.withdrawalCredentials[0] = BLS_WITHDRAWAL_PREFIX[0]))
    (valid : isValidDepositSignature config checks deposit.pubkey deposit.withdrawalCredentials
      deposit.amount deposit.signature = .ok true)
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (holds : BalancesMatch state) :
    after.validators.data = state.validators.data.push (getValidatorFromDeposit preset fork
        deposit.pubkey deposit.withdrawalCredentials deposit.amount) ∧
      after.balances.data = state.balances.data.push deposit.amount := by
  simp only [applyPendingDeposit, new, notBls, ↓reduceIte, bind, Except.bind, valid] at computed
  exact addValidatorToRegistry_push computed holds

/-- A pending deposit changes nothing, raises a balance, or adds a fresh key.

The first case covers a deposit to a new key with an invalid signature.

From Heze it also covers a new key with BLS withdrawal credentials.

The second case is a deposit to a known key.

The third case adds a validator at the end of the registry, and no other validator has its key. -/
theorem applyPendingDeposit_cases {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    after = state ∨
    (∃ index : ValidatorIndex, increaseBalance state index deposit.amount = .ok after) ∨
    (deposit.pubkey ∉ validatorKeys state ∧
      addValidatorToRegistry state deposit.pubkey deposit.withdrawalCredentials deposit.amount =
        .ok after) := by
  unfold applyPendingDeposit at computed
  split at computed
  · rename_i absent
    split at computed
    · cases computed
      exact .inl rfl
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · refine .inr (.inr ⟨?_, computed⟩)
      simp only [Array.findIdx?_eq_none_iff, beq_eq_false_iff_ne] at absent
      simpa [validatorKeys, List.mem_map] using absent
    · cases computed
      exact .inl rfl
  · simp only [liftAccessor_ok, bind_ok_iff, liftArith, mapError_ok_iff] at computed
    obtain ⟨index, _, computed⟩ := computed
    exact .inr (.inl ⟨index, computed⟩)

/-- A deposit adds at most one entry to the registry, and keeps each validator there. -/
theorem applyPendingDeposit_validators_size_le_and_mem {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    after.validators.data.size ≤ state.validators.data.size + 1 ∧
      ∀ validator ∈ state.validators.data, validator ∈ after.validators.data := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact ⟨Nat.le_succ _, fun _ member => member⟩
  · rw [increaseBalance_validators raised]
    exact ⟨Nat.le_succ _, fun _ member => member⟩
  · rw [addValidatorToRegistry_validators_eq_push added]
    exact ⟨by simp, fun _ member => Array.mem_push.mpr (.inl member)⟩

/-- A deposit to a known key raises the balance at the index of that key by its amount.

No other balance changes. -/
theorem applyPendingDeposit_known_balances {deposit : PendingDeposit} {index : Nat}
    (known : state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some index)
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    (∃ balance raised : Gwei, state.balances.data[index]? = some balance ∧
      after.balances.data[index]? = some raised ∧
        raised.toNat = balance.toNat + deposit.amount.toNat) ∧
      ∀ i, i ≠ index → after.balances.data[i]? = state.balances.data[i]? := by
  simp only [applyPendingDeposit, known, liftAccessor_ok, increaseBalance, bind_ok_iff, liftArith,
    mapError_ok_iff, ofNatChecked_ok_iff, addChecked_ok_iff] at computed
  obtain ⟨validatorIndex, ⟨_, same⟩, balance, found, raised, ⟨_, summed⟩, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setBalance_ok set
  unfold getBalance at found
  split at found
  · rename_i read
    cases found
    rw [same] at read inside
    refine ⟨⟨_, raised, read, ?_, summed⟩, fun i other => ?_⟩
    · simp [BeaconState.putBalance, same, inside]
    · simp [BeaconState.putBalance, same, Ne.symm other]
  · cases found

/-- Applying deposits in order adds the amounts of some of them to the balances.

The others are droppable at the start, and the sum of the balances rises by the amounts added.

That needs one balance for each validator. -/
theorem foldlM_applyPendingDeposit_partition :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset fork},
      deposits.foldlM (applyPendingDeposit config checks) state = .ok after →
      BalancesMatch state →
      ∃ added dropped : List PendingDeposit,
        (added ++ dropped).Perm deposits ∧
          (∀ deposit ∈ dropped, DepositDroppable config checks state deposit) ∧
          balanceSum after = balanceSum state + pendingAmount added
  | [], _, _, computed, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], [], List.Perm.refl _, by simp, by simp [pendingAmount]⟩
  | deposit :: rest, state, after, computed, holds => by
    simp only [List.foldlM_cons, bind, Except.bind] at computed
    split at computed
    · cases computed
    rename_i next applied
    have grown := applyPendingDeposit_validators_size_le_and_mem applied
    obtain ⟨added, dropped, perm, all, sum⟩ :=
      foldlM_applyPendingDeposit_partition computed ((applyPendingDeposit_kept applied).1 holds)
    rcases balanceSum_applyPendingDeposit applied holds with raised | ⟨same, lost⟩
    · have front : pendingAmount (deposit :: added) =
          deposit.amount.toNat + pendingAmount added := by
        simp [pendingAmount]
      -- A key that no validator has after this deposit had none before it.
      exact ⟨deposit :: added, dropped, perm.cons deposit,
        fun _ member => DepositDroppable.of_kept grown.2 (all _ member), by omega⟩
    · subst same
      refine ⟨added, deposit :: dropped, List.perm_middle.trans (perm.cons deposit), ?_, sum⟩
      intro _ member
      rcases List.mem_cons.mp member with rfl | member
      · exact lost
      · exact all _ member

/-- Deposits applied in order raise the sum of the balances by at most their amounts. -/
theorem foldlM_applyPendingDeposit_le :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset fork},
      deposits.foldlM (applyPendingDeposit config checks) state = .ok after →
      balanceSum after ≤ balanceSum state + pendingAmount deposits
  | [], _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp [pendingAmount]
  | deposit :: rest, state, after, computed => by
    simp only [List.foldlM_cons, bind, Except.bind] at computed
    split at computed
    · cases computed
    rename_i next applied
    have first := balanceSum_applyPendingDeposit_le applied
    have later := foldlM_applyPendingDeposit_le computed
    simp only [pendingAmount, List.map_cons, List.sum_cons] at later ⊢
    omega

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
