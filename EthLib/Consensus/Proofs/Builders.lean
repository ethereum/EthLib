module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Builders
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Serialization.Proofs.Ssz.Typed.Rooted

/-!
# Proofs: builder indices and builder rules

Setting the flag on a builder index gives an index that names a builder.

Below 2^40, clearing the flag gives the builder index back.

An index that names a builder comes back from its builder index.

No index below 2^40 names a builder, so no validator of a registry within a limit of 2^40 does.

What a builder owes fits in 64 bits exactly when its sum does, and then it is that sum.

A builder can cover a bid exactly when its balance holds the bid, its debt and the minimum deposit.

With at least six slots in an epoch, the quorum of a payment never overflows.

On a preset whose increment per slot is large enough, every quorum is at least one gwei.

A builder that starts to exit is no longer active, unless its withdrawable epoch is the far future.

Settling a payment empties its position and queues at most one withdrawal, of its amount.

So settling keeps what each builder owes.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

/-- The flag is the single bit 40. -/
theorem toBitVec_BUILDER_INDEX_FLAG : BUILDER_INDEX_FLAG.toBitVec = BitVec.twoPow 64 40 := by
  rfl

/-- Bit 40 of an index below 2^40 is clear. -/
theorem getElem_forty_eq_false {index : UInt64} (small : index.toNat < 2 ^ 40) :
    index.toBitVec[40] = false := by
  have low : index.toBitVec.getLsbD 40 = false := by
    simpa [BitVec.getLsbD] using Nat.testBit_lt_two_pow small
  simpa using low

/-- Setting the flag gives an index that names a builder. -/
theorem isBuilderIndex_convertBuilderIndexToValidatorIndex (index : BuilderIndex) :
    isBuilderIndex (convertBuilderIndexToValidatorIndex index) = true := by
  simp only [isBuilderIndex, convertBuilderIndexToValidatorIndex, bne_iff_ne, ne_eq,
    ← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_or, toBitVec_BUILDER_INDEX_FLAG]
  intro zero
  have := congrArg (·.getLsbD 40) zero
  simp at this

/-- A builder index below 2^40 comes back once the flag is set, then cleared. -/
theorem convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex
    {index : BuilderIndex} (small : index.toNat < 2 ^ 40) :
    convertValidatorIndexToBuilderIndex (convertBuilderIndexToValidatorIndex index) = index := by
  simp only [convertValidatorIndexToBuilderIndex, convertBuilderIndexToValidatorIndex,
    ← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not,
    toBitVec_BUILDER_INDEX_FLAG]
  apply BitVec.eq_of_getLsbD_eq
  intro i inRange
  by_cases forty : i = 40
  · subst forty
    simp [getElem_forty_eq_false small]
  · simp [forty, inRange]

/-- An index that names a builder comes back once the flag is cleared, then set. -/
theorem convertBuilderIndexToValidatorIndex_convertValidatorIndexToBuilderIndex
    {index : ValidatorIndex} (builder : isBuilderIndex index = true) :
    convertBuilderIndexToValidatorIndex (convertValidatorIndexToBuilderIndex index) = index := by
  simp only [isBuilderIndex, convertValidatorIndexToBuilderIndex,
    convertBuilderIndexToValidatorIndex, bne_iff_ne, ne_eq, ← UInt64.toBitVec_inj,
    UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not,
    toBitVec_BUILDER_INDEX_FLAG] at *
  apply BitVec.eq_of_getLsbD_eq
  intro i inRange
  by_cases forty : i = 40
  · subst forty
    cases bit : index.toBitVec[40]
    · -- A clear bit 40 would make the flag test zero.
      refine absurd ?_ builder
      apply BitVec.eq_of_getLsbD_eq
      intro j _
      by_cases same : j = 40
      · subst same
        simp [bit]
      · simp [Ne.symm same]
    · simp [bit]
  · simp [forty, inRange]

/-- No index below 2^40 names a builder. -/
theorem isBuilderIndex_eq_false_of_lt {index : ValidatorIndex} (small : index.toNat < 2 ^ 40) :
    isBuilderIndex index = false := by
  simp only [isBuilderIndex, bne_eq_false_iff_eq, ← UInt64.toBitVec_inj, UInt64.toBitVec_and,
    toBitVec_BUILDER_INDEX_FLAG]
  apply BitVec.eq_of_getLsbD_eq
  intro i inRange
  by_cases forty : i = 40
  · subst forty
    simp [getElem_forty_eq_false small]
  · simp [forty, inRange]

/-- The registry limit of both presets is 2^40. -/
theorem registryLimit_presets :
    Preset.mainnet.VALIDATOR_REGISTRY_LIMIT.toNat = 2 ^ 40 ∧
      Preset.minimal.VALIDATOR_REGISTRY_LIMIT.toNat = 2 ^ 40 := by
  decide

variable {preset : Preset} {fork : Base.Fork}

/-- No validator of a registry within a limit of at most 2^40 has an index that names a builder.
-/
theorem isBuilderIndex_eq_false_of_registry {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (limit : preset.VALIDATOR_REGISTRY_LIMIT.toNat ≤ 2 ^ 40)
    {index : ValidatorIndex} (member : index.toNat < state.validators.data.size) :
    isBuilderIndex index = false :=
  isBuilderIndex_eq_false_of_lt (Nat.lt_of_lt_of_le member (Nat.le_trans within limit))

/-- What a builder owes succeeds exactly when its sum is below 2^64, and then it is that sum. -/
theorem getPendingBalanceToWithdrawForBuilder_ok_iff {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {index : BuilderIndex} {amount : Gwei} :
    getPendingBalanceToWithdrawForBuilder state gloas index = .ok amount ↔
      pendingBuilderTotal state gloas index < 2 ^ 64 ∧
        amount.toNat = pendingBuilderTotal state gloas index := by
  unfold getPendingBalanceToWithdrawForBuilder
  by_cases large : 2 ^ 64 ≤ pendingBuilderTotal state gloas index
  · simp [large, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, bind, Except.bind]
    omega
  · have small : pendingBuilderTotal state gloas index < 2 ^ 64 := Nat.lt_of_not_le large
    simp only [large, ite_false, pure, Except.pure, Except.ok.injEq, small, true_and]
    constructor
    · rintro rfl
      simp [Nat.mod_eq_of_lt small]
    · intro sum
      apply UInt64.toNat_inj.mp
      simp [sum, Nat.mod_eq_of_lt small]

/-- A builder can cover a bid exactly when its balance holds the bid, its debt and the minimum.

The minimum is the minimum deposit. -/
theorem canBuilderCoverBid_eq_ok_true_iff {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {index : BuilderIndex} {bidAmount : Gwei} :
    canBuilderCoverBid state gloas index bidAmount = .ok true ↔
      ∃ builder pending, getBuilder state gloas index = .ok builder ∧
        getPendingBalanceToWithdrawForBuilder state gloas index = .ok pending ∧
        preset.MIN_DEPOSIT_AMOUNT.toNat + pending.toNat + bidAmount.toNat ≤
          builder.balance.toNat := by
  simp only [canBuilderCoverBid, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff]
  constructor
  · rintro ⟨builder, found, pending, owed, minBalance, ⟨_, sum⟩, covered⟩
    refine ⟨builder, pending, found, owed, ?_⟩
    split at covered
    · cases covered
    · rename_i enough
      simp only [pure, Except.pure, Except.ok.injEq, decide_eq_true_eq] at covered
      rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at enough
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ enough] at covered
      omega
  · rintro ⟨builder, pending, found, owed, enough⟩
    have bound := builder.balance.toNat_lt
    refine ⟨builder, found, pending, owed, preset.MIN_DEPOSIT_AMOUNT + pending,
      ⟨by omega, ?_⟩, ?_⟩
    · exact toNat_add_of_lt (by omega)
    have sum : (preset.MIN_DEPOSIT_AMOUNT + pending).toNat =
        preset.MIN_DEPOSIT_AMOUNT.toNat + pending.toNat :=
      toNat_add_of_lt (by omega)
    have fits : preset.MIN_DEPOSIT_AMOUNT + pending ≤ builder.balance := by
      rw [UInt64.le_iff_toNat_le, sum]
      omega
    simp only [UInt64.not_lt.mpr fits, ite_false]
    simp only [pure, Except.pure, Except.ok.injEq, decide_eq_true_eq]
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ fits, sum]
    omega

/-- A preset whose payment quorum is at least one gwei on every state.

Every total active balance is at least one effective balance increment.

So the quorum is at least the share of one slot in that increment, times six, divided by ten.

Each division rounds down, so the preset needs that share, times six, to be at least ten. -/
abbrev Preset.PaymentQuorumPositive (preset : Preset) : Prop :=
  BUILDER_PAYMENT_THRESHOLD_DENOMINATOR.toNat ≤
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat / preset.SLOTS_PER_EPOCH.toNat *
      BUILDER_PAYMENT_THRESHOLD_NUMERATOR.toNat

/-- The mainnet and minimal presets have a payment quorum of at least one gwei. -/
theorem paymentQuorumPositive_presets :
    Preset.mainnet.PaymentQuorumPositive ∧ Preset.minimal.PaymentQuorumPositive := by
  decide

/-- On a preset with this property, every quorum that is computed is at least one gwei.

So a payment of zero weight, which no attester voted for, is never released. -/
theorem getBuilderPaymentQuorumThreshold_pos {state : BeaconState preset fork}
    (positive : preset.PaymentQuorumPositive) {quorum : Gwei}
    (computed : getBuilderPaymentQuorumThreshold state = .ok quorum) : 0 < quorum := by
  simp only [getBuilderPaymentQuorumThreshold, bind_ok_iff, liftArith, mapError_ok_iff,
    mulChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨total, totalOk, product, ⟨-, productIs⟩, rfl⟩ := computed
  have least := UInt64.le_iff_toNat_le.mp (le_getTotalBalance totalOk)
  -- The share of one slot in the total is at least its share in one increment.
  have share : preset.EFFECTIVE_BALANCE_INCREMENT.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      (total / preset.SLOTS_PER_EPOCH).toNat := by
    rw [UInt64.toNat_div]
    exact Nat.div_le_div_right least
  have enough : BUILDER_PAYMENT_THRESHOLD_DENOMINATOR.toNat ≤ product.toNat := by
    rw [productIs]
    exact Nat.le_trans positive (Nat.mul_le_mul_right _ share)
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
  have ten : BUILDER_PAYMENT_THRESHOLD_DENOMINATOR.toNat = 10 := rfl
  rw [ten] at enough ⊢
  simp only [UInt64.toNat_zero]
  omega

/-- With at least six slots in an epoch, the quorum of a payment never overflows.

It is then six tenths of the active balance of one slot, each division rounded down. -/
theorem getBuilderPaymentQuorumThreshold_of_total {state : BeaconState preset fork}
    {total : Gwei} (computed : getTotalActiveBalance state = .ok total)
    (slots : 6 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    getBuilderPaymentQuorumThreshold state =
      .ok (total / preset.SLOTS_PER_EPOCH * BUILDER_PAYMENT_THRESHOLD_NUMERATOR /
        BUILDER_PAYMENT_THRESHOLD_DENOMINATOR) := by
  have fits :
      total.toNat / preset.SLOTS_PER_EPOCH.toNat * BUILDER_PAYMENT_THRESHOLD_NUMERATOR.toNat <
        2 ^ 64 := by
    have bound := total.toNat_lt
    have six : BUILDER_PAYMENT_THRESHOLD_NUMERATOR.toNat = 6 := rfl
    rw [six]
    have : total.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ total.toNat / 6 :=
      Nat.div_le_div_left slots (by decide)
    omega
  simp [getBuilderPaymentQuorumThreshold, computed, liftArith, mulChecked, fits, bind,
    Except.bind, Except.mapError, pure, Except.pure]

/-- A builder that is set is set in the registry. -/
theorem setBuilder_ok {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {index : BuilderIndex} {builder : Builder}
    (set : state.setBuilder gloas index builder = .ok after) :
    ∃ inside, after = state.putBuilder gloas index.toNat inside builder := by
  unfold BeaconState.setBuilder at set
  split at set
  · rename_i inside
    cases set
    exact ⟨inside, rfl⟩
  · cases set

/-- A builder that starts to exit may withdraw the delay after the current epoch. -/
theorem getBuilder_initiateBuilderExit {config : Config} {state after : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {index : BuilderIndex}
    (computed : initiateBuilderExit config state gloas index = .ok after) :
    ∃ builder withdrawableEpoch, getBuilder state gloas index = .ok builder ∧
      withdrawableEpoch.toNat =
        (getCurrentEpoch state).toNat + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat ∧
      getBuilder after gloas index = .ok { builder with withdrawableEpoch } := by
  simp only [initiateBuilderExit, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff]
    at computed
  obtain ⟨builder, found, withdrawableEpoch, ⟨_, sum⟩, set⟩ := computed
  refine ⟨builder, withdrawableEpoch, found, sum, ?_⟩
  obtain ⟨inside, rfl⟩ := setBuilder_ok set
  simp [getBuilder, BeaconState.putBuilder, inside]

/-- Setting a builder keeps the slot. -/
theorem setBuilder_slot {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {index : BuilderIndex} {builder : Builder}
    (set : state.setBuilder gloas index builder = .ok after) : after.slot = state.slot := by
  obtain ⟨_, rfl⟩ := setBuilder_ok set
  rfl

/-- A builder that starts to exit is no longer active.

The exception is a withdrawable epoch equal to the far future. -/
theorem isActiveBuilder_initiateBuilderExit {config : Config}
    {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork} {index : BuilderIndex}
    (computed : initiateBuilderExit config state gloas index = .ok after)
    (early : (getCurrentEpoch state).toNat + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat <
      2 ^ 64 - 1) :
    isActiveBuilder after gloas index = .ok false := by
  obtain ⟨builder, withdrawableEpoch, _, sum, exited⟩ := getBuilder_initiateBuilderExit computed
  have far : withdrawableEpoch ≠ FAR_FUTURE_EPOCH := by
    intro same
    rw [same] at sum
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  simp [isActiveBuilder, exited, bind, Except.bind, pure, Except.pure, far]

/-- Settling a payment empties its position and queues its withdrawal if its amount is positive.

The position must be one of the pending payments. -/
theorem settleBuilderPayment_spec {state after : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {paymentIndex : UInt64}
    (computed : settleBuilderPayment state gloas paymentIndex = .ok after) :
    ∃ inRange : paymentIndex.toNat < 2 * preset.SLOTS_PER_EPOCH.toNat,
      after.builderPendingPayments gloas =
          (state.builderPendingPayments gloas).set paymentIndex.toNat .empty inRange ∧
        (after.builderPendingWithdrawals gloas).data.toList =
          (state.builderPendingWithdrawals gloas).data.toList ++
            let payment := (state.builderPendingPayments gloas)[paymentIndex.toNat]
            if 0 < payment.withdrawal.amount then [payment.withdrawal] else [] := by
  unfold settleBuilderPayment at computed
  split at computed
  · rename_i inRange
    cases computed
    refine ⟨inRange, rfl, ?_⟩
    split <;> simp_all
  · cases computed

/-- The sum owed after one entry of a list is replaced. -/
theorem owedBy_set {index : BuilderIndex} :
    ∀ {withdrawals : List BuilderPendingWithdrawal} {k : Nat} (inRange : k < withdrawals.length)
      (entry : BuilderPendingWithdrawal),
      owedBy index (withdrawals.set k entry) + owedBy index [withdrawals[k]] =
        owedBy index withdrawals + owedBy index [entry]
  | [], _, inRange, _ => absurd inRange (Nat.not_lt_zero _)
  | first :: rest, 0, _, entry => by
    simp [owedBy]
    omega
  | first :: rest, k + 1, inRange, entry => by
    have step :=
      owedBy_set (index := index) (withdrawals := rest) (k := k) (by simpa using inRange) entry
    simp only [owedBy, List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ,
      List.map_nil, List.sum_nil] at step ⊢
    omega

/-- Settling a payment keeps what each builder owes.

The amount moves from the payment to the queue of withdrawals, and the empty payment owes nothing.
-/
theorem pendingBuilderTotal_settleBuilderPayment {state after : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {paymentIndex : UInt64}
    (computed : settleBuilderPayment state gloas paymentIndex = .ok after) (index : BuilderIndex) :
    pendingBuilderTotal after gloas index = pendingBuilderTotal state gloas index := by
  obtain ⟨inRange, payments, withdrawals⟩ := settleBuilderPayment_spec computed
  have moved := owedBy_set (index := index)
    (withdrawals := (state.builderPendingPayments gloas).elements.toList.map (·.withdrawal))
    (k := paymentIndex.toNat) (by simpa using inRange) BuilderPendingPayment.empty.withdrawal
  have empty : owedBy index [BuilderPendingPayment.empty.withdrawal] = 0 := by
    simp [owedBy, BuilderPendingPayment.empty]
  have amount : owedBy index
      [(state.builderPendingPayments gloas)[paymentIndex.toNat].withdrawal] =
      owedBy index
        (if 0 < (state.builderPendingPayments gloas)[paymentIndex.toNat].withdrawal.amount then
          [(state.builderPendingPayments gloas)[paymentIndex.toNat].withdrawal] else []) := by
    split
    · rfl
    · rename_i positive
      have zero : (state.builderPendingPayments gloas)[paymentIndex.toNat].withdrawal.amount.toNat =
          0 := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] at positive
        omega
      simp [owedBy, zero]
  -- A read of the rooted payments is a read of their elements.
  have read : (state.builderPendingPayments gloas)[paymentIndex.toNat] =
      (state.builderPendingPayments gloas).elements[paymentIndex.toNat] := rfl
  simp only [List.getElem_map, Vector.getElem_toList, empty, Nat.add_zero] at moved
  unfold pendingBuilderTotal
  rw [withdrawals, payments, RootedVector.elements_set, Vector.toList_set, List.map_set]
  simp only [owedBy, List.map_append, List.sum_append, read] at moved amount ⊢
  omega

end EthLib.Consensus
