module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Nat
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Participation
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
public import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
public import EthLib.Consensus.Proofs.DirectSafety.Cohorts
public import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
public import EthLib.Consensus.Proofs.DirectSafety.FundingBlock
public import EthLib.Consensus.Proofs.DirectSafety.FundingEpoch
public import EthLib.Consensus.Proofs.DirectSafety.FundingSlot
public import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.Provenance
public import EthLib.Consensus.Proofs.DirectSafety.Safety
public import EthLib.Consensus.Proofs.Participation
public import EthLib.Consensus.Proofs.Transition.ActivationReserve
public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
public import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
public import EthLib.Consensus.Proofs.Transition.BlockRewards
public import EthLib.Consensus.Proofs.Transition.EpochParticipation
public import EthLib.Consensus.Proofs.Transition.InactivityLeakVoter
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.RetiredValidator
public import EthLib.Consensus.Proofs.Transition.SlashedExit
public import EthLib.Consensus.Proofs.Transition.Totality.Inactivity
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
public import EthLib.Consensus.Proofs.Transition.Totality.SupplyBeforeAltair
public import EthLib.Consensus.Proofs.Transition.ValidatorCaps
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.Ring

/-!
# A priori bounds on the balance changes of one epoch

From Altair, the base reward of one increment of effective balance is a factor times the increment.

That product is divided by the integer square root of the total active balance, rounding down.

The total base rewards of an epoch are that reward for each whole increment of the total.

They bound what one epoch can issue, but they are not monotone in the total.

On mainnet, a total of 36,066,180 ETH gives 12,154,302,660 Gwei.

One more ETH gives 12,118,236,816 Gwei, since the square root steps up while the increments do not.

This module bounds them by an issuance envelope `BRF * (isqrt T + 2)`, monotone in the total.

The envelope does not depend on the fork, so it holds from Electra on.

It also bounds what the rewards pass of an epoch takes from the balances, inside a leak or not.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-- The total base rewards of an epoch are at most the issuance envelope of its total.

They are the whole increments of the total active balance, times the base reward per increment.

The bound needs no premise beyond the success of the reward per increment. -/
private theorem totalBaseRewards_le_envelope {total perIncrement : Gwei}
    (computed : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat ≤
      preset.epochIssuanceBeforeAltair total.toNat := by
  rw [toNat_getBaseRewardPerIncrement computed]
  unfold Preset.epochIssuanceBeforeAltair
  rcases Nat.eq_zero_or_pos total.toNat with zero | positive
  · simp [zero]
  exact div_mul_div_sqrt_le positive _

/-! ## The issuance of one epoch

From Electra, an epoch pays three kinds of credit that no deposit funds.

The rewards pass pays the flags of the previous epoch.

The blocks pay their proposers for newly set flags, and the sync committee for each slot.

They stay below twice the issuance envelope of the ceiling `T_plus`.

That needs `T_plus` to be at most three halves of the total active balance.

The bound is `3439 / 1792` of the envelope, where `3439 / 1792 < 2`.
-/

/-- Four times a stake `a` is at most `5 * sqrt T * (sqrt a + 2)`, in integer roots.

The total must be positive and at least two thirds of the stake.

It is the integer form of `sqrt(3/2) < 5/4`. -/
private theorem four_le_five_sqrt {a T : Nat} (positive : 0 < T) (ratio : 2 * a ≤ 3 * T) :
    4 * a ≤ 5 * T.sqrt * (a.sqrt + 2) := by
  have below := Nat.lt_succ_sqrt T
  have belowStake := Nat.lt_succ_sqrt a
  have one : 0 < T.sqrt := Nat.sqrt_pos.mpr positive
  generalize T.sqrt = s at *
  generalize a.sqrt = S at *
  have total : T ≤ s * (s + 2) := by
    have square : s.succ * s.succ = s * (s + 2) + 1 := by rw [Nat.succ_eq_add_one]; ring
    omega
  have stake : a ≤ S * (S + 2) := by
    have square : S.succ * S.succ = S * (S + 2) + 1 := by rw [Nat.succ_eq_add_one]; ring
    omega
  by_cases wide : 6 * (s + 2) ≤ 5 * (S + 2)
  · calc 4 * a ≤ s * (6 * (s + 2)) := by
          rw [show s * (6 * (s + 2)) = 6 * (s * (s + 2)) by ring]
          omega
      _ ≤ s * (5 * (S + 2)) := Nat.mul_le_mul_left s wide
      _ = 5 * s * (S + 2) := by ring
  · have narrow : 4 * S ≤ 5 * s := by omega
    calc 4 * a ≤ 4 * S * (S + 2) := by rw [Nat.mul_assoc]; omega
      _ ≤ 5 * s * (S + 2) := Nat.mul_le_mul_right _ narrow

/-- The credits of one epoch are at most twice the issuance envelope of the ceiling `a`.

`F` bounds the flag rewards, `G` the proposer credits and `Y` the sync credits.

They are read at a total `T` of `n` whole increments `I`, with base reward per increment `perInc`.

`p` bounds the increments that set a flag, and `q` those that pay a proposer, over two epochs.

The total is at most `a` and at least two thirds of it. -/
theorem issuance_certificate {I a T n perInc p q F G Y : Nat} (inc : 0 < I)
    (aligned : n * I = T) (positive : 0 < T) (ratio : 2 * a ≤ 3 * T) (bounded : T ≤ a)
    (rate : perInc * T.sqrt ≤ I * preset.BASE_REWARD_FACTOR.toNat)
    (part : p * I ≤ a) (attesters : q * I ≤ 2 * a)
    (flags : F * (n * 64) ≤ 54 * perInc * p ^ 2) (proposers : G * 448 ≤ 54 * perInc * q)
    (sync : Y * 28 ≤ preset.epochIssuanceBeforeAltair T) :
    F + G + Y ≤ 2 * preset.epochIssuanceBeforeAltair a := by
  have key := four_le_five_sqrt positive ratio
  have rootPos : 0 < T.sqrt := Nat.sqrt_pos.mpr positive
  have roots : T.sqrt ≤ a.sqrt := Nat.sqrt_le_sqrt bounded
  unfold Preset.epochIssuanceBeforeAltair at sync ⊢
  generalize preset.BASE_REWARD_FACTOR.toNat = B at *
  generalize T.sqrt = s at *
  generalize a.sqrt = S at *
  -- The flag rewards: `F * 64 * T * s <= 54 * B * a^2`, then `F * 256 <= 405 * B * (S + 2)`.
  have flagsScaled : F * 64 * T * s * I ≤ 54 * B * a ^ 2 * I := by
    calc F * 64 * T * s * I = F * (n * 64) * (s * I ^ 2) := by rw [← aligned]; ring
      _ ≤ 54 * perInc * p ^ 2 * (s * I ^ 2) := Nat.mul_le_mul_right _ flags
      _ = 54 * (perInc * s) * (p * I) ^ 2 := by ring
      _ ≤ 54 * (I * B) * a ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ rate) (Nat.pow_le_pow_left part 2)
      _ = 54 * B * a ^ 2 * I := by ring
  have flagsRatio : F * 64 * s * T ≤ 81 * B * a * T := by
    calc F * 64 * s * T = F * 64 * T * s := by ring
      _ ≤ 54 * B * a ^ 2 := Nat.le_of_mul_le_mul_right flagsScaled inc
      _ = 27 * B * a * (2 * a) := by ring
      _ ≤ 27 * B * a * (3 * T) := Nat.mul_le_mul_left _ ratio
      _ = 81 * B * a * T := by ring
  have flagsRoot : F * 256 * s ≤ 405 * B * (S + 2) * s := by
    calc F * 256 * s = F * 64 * s * 4 := by ring
      _ ≤ 81 * B * a * 4 := Nat.mul_le_mul_right _ (Nat.le_of_mul_le_mul_right flagsRatio positive)
      _ = 81 * B * (4 * a) := by ring
      _ ≤ 81 * B * (5 * s * (S + 2)) := Nat.mul_le_mul_left _ key
      _ = 405 * B * (S + 2) * s := by ring
  have flagsBound := Nat.le_of_mul_le_mul_right flagsRoot rootPos
  -- The proposer credits: `G * 448 * s <= 108 * B * a`, then `G * 1792 <= 540 * B * (S + 2)`.
  have proposersScaled : G * 448 * s * I ≤ 108 * B * a * I := by
    calc G * 448 * s * I = G * 448 * (s * I) := by ring
      _ ≤ 54 * perInc * q * (s * I) := Nat.mul_le_mul_right _ proposers
      _ = 54 * (perInc * s) * (q * I) := by ring
      _ ≤ 54 * (I * B) * (2 * a) := Nat.mul_le_mul (Nat.mul_le_mul_left _ rate) attesters
      _ = 108 * B * a * I := by ring
  have proposersRoot : G * 1792 * s ≤ 540 * B * (S + 2) * s := by
    calc G * 1792 * s = G * 448 * s * 4 := by ring
      _ ≤ 108 * B * a * 4 := Nat.mul_le_mul_right _ (Nat.le_of_mul_le_mul_right proposersScaled inc)
      _ = 108 * B * (4 * a) := by ring
      _ ≤ 108 * B * (5 * s * (S + 2)) := Nat.mul_le_mul_left _ key
      _ = 540 * B * (S + 2) * s := by ring
  have proposersBound := Nat.le_of_mul_le_mul_right proposersRoot rootPos
  -- The sync credits read the total itself, which is at most the ceiling.
  have syncBound : Y * 28 ≤ B * (S + 2) :=
    sync.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right roots 2))
  have flagsAtom : 405 * B * (S + 2) = 405 * (B * (S + 2)) := by ring
  have proposersAtom : 540 * B * (S + 2) = 540 * (B * (S + 2)) := by ring
  rw [flagsAtom] at flagsBound
  rw [proposersAtom] at proposersBound
  generalize B * (S + 2) = X at *
  omega

/-- The sync credits of one block are at most the issuance envelope over `28` per slot.

The participant reward is the base rewards of the total, times `2 / 64`, per slot and member.

The proposer share is at most a seventh of it.

The reward divides by the slots of an epoch, so a reward that exists makes them positive. -/
theorem syncCredit_le {fork : Fork} {s : BeaconState preset fork}
    {reward proposer total : Gwei} (rewardOk : syncParticipantReward s = .ok reward)
    (share : proposer.toNat * 7 ≤ reward.toNat) (totalOk : getTotalActiveBalance s = .ok total) :
    preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat) *
        (28 * preset.SLOTS_PER_EPOCH.toNat) ≤ preset.epochIssuanceBeforeAltair total.toNat ∧
      0 < preset.SLOTS_PER_EPOCH.toNat := by
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at rewardOk
  obtain ⟨read, readOk, perIncrement, perOk, rewardOk⟩ := rewardOk
  have same : read = total := Except.ok.inj (readOk.symm.trans totalOk)
  subst read
  obtain ⟨increments, incrementsOk, base, baseOk, weighted, weightedOk, perWeight, perWeightOk,
    perSlot, perSlotOk, rewardOk⟩ := rewardOk
  rw [divChecked_ok_iff] at incrementsOk perWeightOk perSlotOk rewardOk
  rw [mulChecked_ok_iff] at baseOk weightedOk
  have envelope := totalBaseRewards_le_envelope perOk
  have weightValue : SYNC_REWARD_WEIGHT.toNat = 2 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := rfl
  rw [weightValue] at weightedOk
  rw [denominator] at perWeightOk
  -- Each step of the reward rounds down, so the members' rewards of a slot fit its share.
  have member : preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat ≤ perSlot.toNat := by
    rw [rewardOk.2, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have slot : perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ perWeight.toNat := by
    rw [perSlotOk.2]
    exact Nat.div_mul_le_self _ _
  have weight : perWeight.toNat * 32 ≤ base.toNat := by
    rw [perWeightOk.2, weightedOk.2]
    have := Nat.div_mul_le_self (base.toNat * 2) 64
    omega
  have baseLe : base.toNat ≤ preset.epochIssuanceBeforeAltair total.toNat := by
    rw [baseOk.2, incrementsOk.2, Nat.mul_comm]
    exact envelope
  have proposerLe : preset.SYNC_COMMITTEE_SIZE.toNat * proposer.toNat * 7 ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ share
  have members := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat member
  have chain : preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat *
      32 ≤ preset.epochIssuanceBeforeAltair total.toNat := by
    have := Nat.mul_le_mul_right 32 (members.trans slot)
    omega
  have scaled := Nat.mul_le_mul_right (4 * preset.SLOTS_PER_EPOCH.toNat) proposerLe
  refine ⟨?_, Nat.pos_of_ne_zero fun zero =>
    perSlotOk.1 (UInt64.toNat_inj.mp (by simpa using zero))⟩
  calc preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat) *
        (28 * preset.SLOTS_PER_EPOCH.toNat) =
      preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat * 28 +
        preset.SYNC_COMMITTEE_SIZE.toNat * proposer.toNat * 7 *
          (4 * preset.SLOTS_PER_EPOCH.toNat) := by ring
    _ ≤ preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat * 28 +
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * (4 * preset.SLOTS_PER_EPOCH.toNat) :=
        Nat.add_le_add_left scaled _
    _ = preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat * 32 := by
        ring
    _ ≤ preset.epochIssuanceBeforeAltair total.toNat := chain

/-! ## The penalties of one rewards pass

From Altair, the rewards pass charges an eligible validator three penalties at most.

It pays the weight of the source flag and of the target flag, each when that flag is missing.

The base reward times the weight is divided by the weight denominator, rounding down.

It also pays the inactivity penalty when the target flag is missing.

That penalty is the effective balance times the new score, over the score bias times the quotient.

A missing head flag costs nothing, and the rewards only raise the balance.

The sync committee penalties are not part of this pass.

The processing of the sync aggregate applies them in each block.

The bound reads the replay of the pass, which records each penalty entry as its own event.
-/

variable {config : Config} {fork : Fork} {state scored after : BeaconState preset fork}
  {total : Gwei}

/-- One pass of deltas records the reward of each validator as its credit, and keeps the registry.

Its penalties are recorded with no credit. -/
private theorem replayDeltas_credits {fork : Fork} (source : BalanceSource)
    (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
    (ok : replayDeltas source deltas pre = .ok post) :
    post.1.validators = pre.1.validators ∧
      (post.2.map (·.creditLimit)).sum = (pre.2.map (·.creditLimit)).sum +
        ((List.range pre.1.validators.data.size).map fun i => (deltas.1.getD i 0).toNat).sum := by
  unfold replayDeltas at ok
  generalize List.range pre.1.validators.data.size = indices at ok ⊢
  induction indices generalizing pre with
  | nil => cases ok; simp
  | cons i rest ih =>
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, stepOk, restOk⟩ := ok
    obtain ⟨registry, sum⟩ := ih restOk
    simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq, exists_eq_left'] at stepOk
    obtain ⟨index, -, _, ⟨raised, raisedOk, rfl⟩, lowered, loweredOk, rfl⟩ := stepOk
    refine ⟨registry.trans ((decreaseBalance_validators loweredOk).trans
      (increaseBalance_validators raisedOk)), ?_⟩
    rw [sum]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega

/-- The debit of one event at one position, when the event is a penalty or an inactivity penalty.

This is the non-slashing debit of that position, for the two sources of the rewards pass. -/
def penaltyDebit (j : Nat) (event : BalanceEvent preset) : Nat :=
  if event.source = .penalties ∨ event.source = .inactivity then
    actualBalanceAt event.before j - actualBalanceAt event.after j
  else 0

/-- The effective balance of a key that is eligible for the rewards of the previous epoch.

A key that is not eligible, or whose eligibility cannot be decided, counts nothing. -/
def eligibleWeight (state : BeaconState preset fork) (j : Nat) : Nat :=
  match state.validators.data[j]? with
  | some validator =>
    match isEligibleValidator (getPreviousEpoch state) validator with
    | .ok true => validator.effectiveBalance.toNat
    | _ => 0
  | none => 0

/-- The debit of one position in a step is at most the debits of the whole step. -/
private theorem debit_le_balanceDebits {f : Fork} (s t : BeaconState preset f) (j : Nat) :
    actualBalanceAt ⟨f, s⟩ j - actualBalanceAt ⟨f, t⟩ j ≤ balanceDebits s t := by
  by_cases inside : j < s.balances.data.size
  · exact Finset.single_le_sum (f := fun i => actualBalanceAt ⟨f, s⟩ i - actualBalanceAt ⟨f, t⟩ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr inside)
  · simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt inside)]

/-- The credit of one event at one position, when the event is a reward. -/
def rewardCredit (j : Nat) (event : BalanceEvent preset) : Nat :=
  if event.source = .rewards then
    actualBalanceAt event.after j - actualBalanceAt event.before j
  else 0

/-- One pass of deltas debits a position at most its penalty and credits it at most its reward. -/
theorem replayDeltas_flows {fork : Fork} (source : BalanceSource)
    (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
    (ok : replayDeltas source deltas pre = .ok post) (j : Nat) :
    (post.2.map (penaltyDebit j)).sum ≤
      (pre.2.map (penaltyDebit j)).sum + (deltas.2.getD j 0).toNat ∧
    (post.2.map (rewardCredit j)).sum ≤
      (pre.2.map (rewardCredit j)).sum + (deltas.1.getD j 0).toNat := by
  unfold replayDeltas at ok
  have nodup := List.nodup_range (n := pre.1.validators.data.size)
  generalize List.range pre.1.validators.data.size = indices at ok nodup
  -- Each position of the list flows through `j` only when it is `j`, and the list holds `j` once.
  suffices bound : (post.2.map (penaltyDebit j)).sum ≤
      (pre.2.map (penaltyDebit j)).sum + indices.count j * (deltas.2.getD j 0).toNat ∧
      (post.2.map (rewardCredit j)).sum ≤
      (pre.2.map (rewardCredit j)).sum + indices.count j * (deltas.1.getD j 0).toNat by
    obtain ⟨debit, credit⟩ := bound
    have onceDebit := Nat.mul_le_mul_right (deltas.2.getD j 0).toNat
      (List.nodup_iff_count_le_one.mp nodup j)
    have onceCredit := Nat.mul_le_mul_right (deltas.1.getD j 0).toNat
      (List.nodup_iff_count_le_one.mp nodup j)
    exact ⟨by omega, by omega⟩
  clear nodup
  induction indices generalizing pre with
  | nil => cases ok; simp
  | cons i rest ih =>
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, stepOk, restOk⟩ := ok
    obtain ⟨laterDebit, laterCredit⟩ := ih restOk
    simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq, exists_eq_left'] at stepOk
    obtain ⟨index, indexOk, _, ⟨raised, raisedOk, rfl⟩, lowered, loweredOk, rfl⟩ := stepOk
    have position : index.toNat = i :=
      (ofNatChecked_ok_iff.mp (mapError_ok_iff.mp indexOk)).2
    -- The penalty event debits `j` its penalty when it names `j`, and nothing otherwise.
    have penalty : actualBalanceAt ⟨fork, raised⟩ j - actualBalanceAt ⟨fork, lowered⟩ j ≤
        if i = j then (deltas.2.getD j 0).toNat else 0 := by
      by_cases same : i = j
      · subst same
        simp only [↓reduceIte]
        exact (debit_le_balanceDebits raised lowered _).trans (debits_decrease loweredOk).2
      · obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp loweredOk
        have other : j ≠ index.toNat := by omega
        simp [actualBalanceAt, BeaconState.putBalance, Ne.symm other, same]
    -- The reward event credits `j` its reward when it names `j`, and nothing otherwise.
    have reward : actualBalanceAt ⟨fork, raised⟩ j - actualBalanceAt ⟨fork, pre.1⟩ j ≤
        if i = j then (deltas.1.getD j 0).toNat else 0 := by
      have moved := actualBalanceAt_increaseBalance raisedOk j
      rw [position] at moved
      by_cases same : i = j
      · subst same
        simp only [↓reduceIte] at moved ⊢
        omega
      · simp only [same, ↓reduceIte] at moved ⊢
        omega
    have lowerKeep : actualBalanceAt ⟨fork, lowered⟩ j ≤ actualBalanceAt ⟨fork, raised⟩ j := by
      rw [actualBalanceAt_decreaseBalance loweredOk j]
      exact Nat.sub_le _ _
    refine ⟨?_, ?_⟩
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.count_cons, beq_iff_eq, penaltyDebit, reduceCtorEq, or_self,
        ↓reduceIte, Nat.add_zero] at laterDebit ⊢
      have gated : (if source = .penalties ∨ source = .inactivity then
          actualBalanceAt ⟨fork, raised⟩ j - actualBalanceAt ⟨fork, lowered⟩ j else 0) ≤
          actualBalanceAt ⟨fork, raised⟩ j - actualBalanceAt ⟨fork, lowered⟩ j := by
        split <;> omega
      split at penalty <;> rename_i same
      · simp only [same, ↓reduceIte]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [same, ↓reduceIte, Nat.add_zero]
        omega
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.count_cons, beq_iff_eq, rewardCredit, eq_self, ↓reduceIte,
        Nat.add_zero] at laterCredit ⊢
      have quiet : (if source = .rewards then
          actualBalanceAt ⟨fork, lowered⟩ j - actualBalanceAt ⟨fork, raised⟩ j else 0) = 0 := by
        split <;> omega
      split at reward <;> rename_i same
      · simp only [same, ↓reduceIte]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [same, ↓reduceIte, Nat.add_zero]
        omega

/-- One pass of deltas debits each position at most its penalty, in its penalty events.

Its reward events debit nothing, and a penalty at another position keeps this balance. -/
private theorem replayDeltas_debits {fork : Fork} (source : BalanceSource)
    (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
    (ok : replayDeltas source deltas pre = .ok post) (j : Nat) :
    (post.2.map (penaltyDebit j)).sum ≤
      (pre.2.map (penaltyDebit j)).sum + (deltas.2.getD j 0).toNat :=
  (replayDeltas_flows source deltas ok j).1

/-- From Altair and after the first epoch, the replay of the rewards runs four passes of deltas.

They are the passes of the source, target and head flags, and then the inactivity pass. -/
theorem replayRewards_passes (altair : .altair ≤ fork)
    (later : getCurrentEpoch state ≠ GENESIS_EPOCH) {post : BalanceReplay preset fork}
    (replayed : replayRewards (config := config) (state, []) = .ok post) :
    ∃ source target head inactivity first second third,
      getFlagIndexDeltas state altair ⟨0, by decide⟩ = .ok source ∧
      getFlagIndexDeltas state altair ⟨1, by decide⟩ = .ok target ∧
      getFlagIndexDeltas state altair ⟨2, by decide⟩ = .ok head ∧
      getInactivityPenaltyDeltas config state = .ok inactivity ∧
      replayDeltas .penalties source (state, []) = .ok first ∧
      replayDeltas .penalties target first = .ok second ∧
      replayDeltas .penalties head second = .ok third ∧
      replayDeltas .inactivity inactivity third = .ok post := by
  unfold replayRewards at replayed
  split at replayed
  · rename_i genesis
    exact absurd genesis later
  simp only [bind_ok_iff] at replayed
  obtain ⟨ordinary, ordinaryOk, inactivity, inactivityOk, middle, folded, last⟩ := replayed
  simp only [rewardPasses, later, altair, ↓reduceIte, ↓reduceDIte] at ordinaryOk
  have finRange : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl
  rw [finRange] at ordinaryOk
  simp only [List.mapM_cons, List.mapM_nil, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ordinaryOk
  obtain ⟨source, sourceOk, _, ⟨target, targetOk, _, ⟨head, headOk, _, rfl, rfl⟩, rfl⟩, rfl⟩ :=
    ordinaryOk
  rw [List.foldlM_cons, bind_ok_iff] at folded
  obtain ⟨first, firstOk, folded⟩ := folded
  rw [List.foldlM_cons, bind_ok_iff] at folded
  obtain ⟨second, secondOk, folded⟩ := folded
  rw [List.foldlM_cons, bind_ok_iff] at folded
  obtain ⟨third, thirdOk, folded⟩ := folded
  obtain rfl : third = middle := Except.ok.inj folded
  exact ⟨source, target, head, inactivity, first, second, third, sourceOk, targetOk, headOk,
    inactivityOk, firstOk, secondOk, thirdOk, last⟩

/-- A rewards replay pays nothing at genesis, otherwise the sum of its three flag rewards. -/
theorem replayRewards_credit_sum (altair : .altair ≤ fork)
    {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (state, []) = .ok (after, events)) :
    (getCurrentEpoch state = GENESIS_EPOCH ∧ (events.map (·.creditLimit)).sum = 0) ∨
      ∃ source target head : Array Gwei × Array Gwei,
        getFlagIndexDeltas state altair ⟨0, by decide⟩ = .ok source ∧
        getFlagIndexDeltas state altair ⟨1, by decide⟩ = .ok target ∧
        getFlagIndexDeltas state altair ⟨2, by decide⟩ = .ok head ∧
        (events.map (·.creditLimit)).sum =
          ((List.range state.validators.data.size).map fun i => (source.1.getD i 0).toNat).sum +
          ((List.range state.validators.data.size).map fun i => (target.1.getD i 0).toNat).sum +
          ((List.range state.validators.data.size).map fun i => (head.1.getD i 0).toNat).sum := by
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · simp only [replayRewards, genesis, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at replayed
    obtain ⟨-, rfl⟩ := replayed
    exact .inl ⟨genesis, rfl⟩
  obtain ⟨source, target, head, inactivity, first, second, third, sourceOk, targetOk, headOk,
    inactivityOk, firstOk, secondOk, thirdOk, last⟩ := replayRewards_passes altair genesis replayed
  obtain ⟨firstSize, firstSum⟩ := replayDeltas_credits _ _ firstOk
  obtain ⟨secondSize, secondSum⟩ := replayDeltas_credits _ _ secondOk
  obtain ⟨-, thirdSum⟩ := replayDeltas_credits _ _ thirdOk
  obtain ⟨-, lastSum⟩ := replayDeltas_credits _ _ last
  have noReward : ((List.range third.1.validators.data.size).map fun i =>
      (inactivity.1.getD i 0).toNat).sum = 0 := by
    simp [getInactivityPenaltyDeltas_rewards inactivityOk]
  refine .inr ⟨source, target, head, sourceOk, targetOk, headOk, ?_⟩
  rw [lastSum, noReward, thirdSum, secondSum, firstSum, secondSize, firstSize]
  simp only [List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero]

/-- The credits of the rewards pass, from Altair, are its three flag rewards.

Each flag pays at most `w * perInc * p^2 / (n * 64)`.

There `w` is its weight, `p` its increments and `n` the active increments.

The weights sum to `54`, and `P` bounds the balance that sets each flag. -/
theorem replayRewards_credits_le (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit) {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (state, []) = .ok (after, events))
    (active : getTotalActiveBalance state = .ok total) {perIncrement : Gwei}
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement) (P : Nat)
    (participating : ∀ flag participating (balance : Gwei),
      getUnslashedParticipatingIndices state altair flag (getPreviousEpoch state) =
        .ok participating →
      getTotalBalance state participating = .ok balance → balance.toNat ≤ P) :
    (events.map (·.creditLimit)).sum *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
      54 * perIncrement.toNat * (P / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ^ 2 := by
  rcases replayRewards_credit_sum altair replayed with ⟨_, zero⟩ |
    ⟨source, target, head, sourceOk, targetOk, headOk, creditSum⟩
  · rw [zero, Nat.zero_mul]
    exact Nat.zero_le _
  -- Each flag pays at most its weight times the square of its increments.
  have flag {index : Fin PARTICIPATION_FLAG_WEIGHTS.length} {deltas : Array Gwei × Array Gwei}
      (computed : getFlagIndexDeltas state altair index = .ok deltas) :
      ((List.range state.validators.data.size).map fun i => (deltas.1.getD i 0).toNat).sum *
          (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
        PARTICIPATION_FLAG_WEIGHTS[index].toNat * perIncrement.toNat *
          (P / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ^ 2 := by
    obtain ⟨rewards, penalties⟩ := deltas
    obtain ⟨flagged, balance, total', flaggedOk, weighed, totalOk, -⟩ :=
      getFlagIndexDeltas_getD within computed
    obtain rfl : total' = total := Except.ok.inj (totalOk.symm.trans active)
    have bound := getFlagIndexDeltas_rewards_le within computed flaggedOk weighed active per
    have balanceLe := participating _ _ _ flaggedOk weighed
    exact bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.div_le_div_right balanceLe) 2))
  have one := flag sourceOk
  have two := flag targetOk
  have three := flag headOk
  have weights : PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ : Fin 3)].toNat = 54 := rfl
  rw [creditSum]
  rw [← weights]
  simp only [Nat.add_mul] at one two three ⊢
  omega

/-- A sum of quotients over a finite set is at most the quotient of the sum. -/
theorem sum_div_le {ι : Type} (s : Finset ι) (f : ι → Nat) (d : Nat) :
    ∑ i ∈ s, f i / d ≤ (∑ i ∈ s, f i) / d := by
  simpa only [Finset.sum_map_toList] using sum_map_div_le f d s.toList

/-- A rewards pass has zero genesis debits, otherwise its debits are bounded by four entries. -/
private theorem replayRewards_penalty_entries (altair : .altair ≤ fork)
    {rewarded : BalanceReplay preset fork}
    (replayed : replayRewards (config := config) (state, []) = .ok rewarded) :
    (∀ j, (rewarded.2.map (penaltyDebit j)).sum = 0) ∨
      ∃ (total : Gwei) (source target head inactivity : Array Gwei × Array Gwei),
        getTotalActiveBalance state = .ok total ∧
        getFlagIndexDeltas state altair ⟨0, by decide⟩ = .ok source ∧
        getFlagIndexDeltas state altair ⟨1, by decide⟩ = .ok target ∧
        getFlagIndexDeltas state altair ⟨2, by decide⟩ = .ok head ∧
        getInactivityPenaltyDeltas config state = .ok inactivity ∧
        ∀ j, (rewarded.2.map (penaltyDebit j)).sum ≤
          (source.2.getD j 0).toNat + (target.2.getD j 0).toNat +
          (head.2.getD j 0).toNat + (inactivity.2.getD j 0).toNat := by
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · simp only [replayRewards, genesis, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at replayed
    subst replayed
    exact .inl (by intro j; rfl)
  obtain ⟨source, target, head, inactivity, first, second, third, sourceOk, targetOk, headOk,
    inactivityOk, firstOk, secondOk, thirdOk, last⟩ := replayRewards_passes altair genesis replayed
  obtain ⟨total, totalOk⟩ : ∃ total, getTotalActiveBalance state = .ok total := by
    have read := sourceOk
    simp only [getFlagIndexDeltas, bind_ok_iff] at read
    obtain ⟨_, _, _, _, total, totalOk, _⟩ := read
    exact ⟨total, liftAccessor_ok.mp totalOk⟩
  refine .inr ⟨total, source, target, head, inactivity, totalOk, sourceOk, targetOk, headOk,
    inactivityOk, ?_⟩
  intro j
  have one := replayDeltas_debits _ _ firstOk j
  have two := replayDeltas_debits _ _ secondOk j
  have three := replayDeltas_debits _ _ thirdOk j
  have four := replayDeltas_debits _ _ last j
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at one
  omega

/-- Nonzero penalty debits supply actual total and per-increment reads. -/
theorem replayRewards_penalty_scalar_cases (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit) {post : BalanceReplay preset fork}
    (replayed : replayRewards (config := config) (state, []) = .ok post)
    (S : Finset Nat) (inside : ∀ j ∈ S, j < state.validators.data.size) :
    (∃ total perIncrement, getTotalActiveBalance state = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement) ∨
      (∑ j ∈ S, (post.2.map (penaltyDebit j)).sum) = 0 := by
  rcases replayRewards_penalty_entries altair replayed with quiet |
    ⟨total, source, target, head, inactivity, totalOk, sourceOk, targetOk, headOk,
      inactivityOk, entries⟩
  · exact .inr (Finset.sum_eq_zero fun j _ => quiet j)
  by_cases reads : ∃ perIncrement, getBaseRewardPerIncrement preset total = .ok perIncrement
  · obtain ⟨perIncrement, per⟩ := reads
    exact .inl ⟨total, perIncrement, totalOk, per⟩
  right
  apply Finset.sum_eq_zero
  intro j member
  rcases penaltyEntries_le altair within totalOk sourceOk targetOk headOk inactivityOk
    (inside j member) with zero | ⟨base, _, baseOk, _⟩
  · exact Nat.eq_zero_of_le_zero (zero ▸ entries j)
  · simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff] at baseOk
    obtain ⟨_, _, perIncrement, per, _⟩ := baseOk
    exact (reads ⟨perIncrement, per⟩).elim

/-- The penalty debits of one rewards pass, from Altair, over a set `S` of keys.

The pass is replayed from the state `state`, after the update of the inactivity scores.

`E` is the eligible effective stake of `S` there, and `T` the total active balance.

Each score of `S` must be at most `maxScore`.

```text
debits of S <= (W_source + W_target) * BASE_REWARD_FACTOR * E / (WEIGHT_DENOMINATOR * isqrt T)
               + E * maxScore / (INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT)
```

Each key rounds down on its own, and the sum of those quotients is at most the quotient of the sum.
-/
theorem passPenalties_le (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    {rewarded : BalanceReplay preset fork}
    (replayed : replayRewards (config := config) (state, []) = .ok rewarded)
    (active : getTotalActiveBalance state = .ok total) (S : Finset Nat)
    (inside : ∀ j ∈ S, j < state.validators.data.size) {maxScore : Nat}
    (capped : ∀ j ∈ S, ∀ score : UInt64,
      (state.inactivityScores altair).data[j]? = some score → score.toNat ≤ maxScore) :
    ∑ j ∈ S, (rewarded.2.map (penaltyDebit j)).sum ≤
      (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) *
          preset.BASE_REWARD_FACTOR.toNat * (∑ j ∈ S, eligibleWeight state j) /
          (WEIGHT_DENOMINATOR.toNat * total.toNat.sqrt) +
        (∑ j ∈ S, eligibleWeight state j) * maxScore /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  rcases replayRewards_penalty_entries altair replayed with quiet |
    ⟨_, source, target, head, inactivity, _, sourceOk, targetOk, headOk,
      inactivityOk, entries⟩
  · simp only [quiet, Finset.sum_const_zero]
    exact Nat.zero_le _
  -- Short names for the constants of the bound.
  generalize hweights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = weights
  generalize hdenominator : WEIGHT_DENOMINATOR.toNat = denominator
  generalize hquotient : config.INACTIVITY_SCORE_BIAS.toNat *
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat = quotient
  generalize hincrement : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = increment
  generalize hfactor : preset.BASE_REWARD_FACTOR.toNat = factor
  generalize hroot : total.toNat.sqrt = root
  let weight := eligibleWeight state
  have heligible : ∀ j (inside : j < state.validators.data.size),
      isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true →
        weight j = state.validators.data[j].effectiveBalance.toNat := fun j inside eligible => by
    simp only [weight, eligibleWeight, Array.getElem?_eq_getElem inside, eligible]
  -- Each key's debits are at most the bound of its own weight.
  have point : ∀ j ∈ S, (rewarded.2.map (penaltyDebit j)).sum ≤
      weight j / increment * (increment * factor / root) * weights / denominator +
        weight j * maxScore / quotient := by
    intro j member
    have position := inside j member
    rcases penaltyEntries_le altair within active sourceOk targetOk headOk inactivityOk
      position with zero | ⟨base, eligible, baseOk, bound⟩
    · exact (entries j).trans ((Nat.le_of_eq zero).trans (Nat.zero_le _))
    · have baseLe := toNat_getBaseReward_le altair baseOk
        (by rw [toNat_toUInt64_of_lt within position]; exact Array.getElem?_eq_getElem position)
      have scoreLe : ((state.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0 ≤
          maxScore := by
        rcases found : (state.inactivityScores altair).data[j]? with _ | score
        · exact Nat.zero_le _
        · exact capped j member score found
      rw [heligible j position eligible]
      rw [hweights, hdenominator, hquotient] at bound
      rw [hincrement, hfactor, hroot] at baseLe
      refine Nat.le_trans (entries j) (Nat.le_trans bound (Nat.add_le_add ?_ ?_))
      · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ baseLe)
      · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ scoreLe)
  -- The whole increments of the eligible stake bound those of each key.
  have increments : ∑ j ∈ S, weight j / increment ≤ (∑ j ∈ S, weight j) / increment :=
    sum_div_le _ _ _
  change _ ≤ weights * factor * (∑ j ∈ S, weight j) / (denominator * root) +
    (∑ j ∈ S, weight j) * maxScore / quotient
  generalize hsum : ∑ j ∈ S, weight j = eligible at increments ⊢
  have rewardsPart : ∑ j ∈ S,
      weight j / increment * (increment * factor / root) * weights / denominator ≤
        weights * factor * eligible / (denominator * root) := by
    -- Both roundings only lower the product.
    calc ∑ j ∈ S, weight j / increment * (increment * factor / root) * weights / denominator
        ≤ (∑ j ∈ S, weight j / increment * (increment * factor / root) * weights) /
            denominator := sum_div_le _ _ _
      _ ≤ eligible / increment * (increment * factor / root) * weights / denominator := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          exact Nat.div_le_div_right
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ increments))
      _ ≤ eligible * factor / root * weights / denominator :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ (div_mul_div_le_mul_div _ _ _ _))
      _ ≤ weights * (eligible * factor) / root / denominator := by
          rw [Nat.mul_comm _ weights]
          exact Nat.div_le_div_right (Nat.mul_div_le_mul_div_assoc _ _ _)
      _ = weights * factor * eligible / (denominator * root) := by
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm root, Nat.mul_assoc, Nat.mul_comm eligible]
  have scorePart : ∑ j ∈ S, weight j * maxScore / quotient ≤ eligible * maxScore / quotient := by
    refine Nat.le_trans (sum_div_le _ _ _) (Nat.le_of_eq ?_)
    rw [← Finset.sum_mul, hsum]
  calc ∑ j ∈ S, (rewarded.2.map (penaltyDebit j)).sum
      ≤ ∑ j ∈ S, (weight j / increment * (increment * factor / root) * weights / denominator +
          weight j * maxScore / quotient) := Finset.sum_le_sum point
    _ ≤ weights * factor * eligible / (denominator * root) + eligible * maxScore / quotient := by
        rw [Finset.sum_add_distrib]
        exact Nat.add_le_add rewardsPart scorePart

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
