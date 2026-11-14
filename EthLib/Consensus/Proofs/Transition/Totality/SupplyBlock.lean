module

public import EthLib.Consensus.Proofs.Transition.Totality.Bound
public import EthLib.Consensus.Transition.StateTransition
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.PayloadTimeliness
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.BuilderRequests
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.Execution
import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.ParentPayload
import EthLib.Consensus.Proofs.Transition.Payload
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: a block raises the supply by its deposits and its rewards

The supply is the balances plus, from Electra, the pending deposits.

A block brings in the amounts of its deposits and of its deposit requests.

A slashing moves at most the whistleblower reward into the balances, beyond the penalty it takes.

From Altair, the proposer earns a share of the base rewards of each flag newly set.

Each flag of each validator is newly set at most once in the previous and the current epoch.

So the proposer earns at most the rise of the weight of the flags, over 448.

That weight reads the effective balances, which the steps before the attestations keep.

The sync committee members that sign earn a fixed reward, and the proposer a share of it.

Every other step of a block moves balances out of the supply, or within it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}

/-- The Gwei that the deposits and the deposit requests of a block body bring in.

Deposits come with the block before Heze.

Deposit requests come with the block from Electra, and with the payload of its parent from Gloas. -/
def blockDepositAmount (body : BeaconBlockBody preset fork) : Nat :=
  (if before : fork < .hegota then
    ((body.deposits before).data.toList.map (·.data.amount.toNat)).sum
  else 0) +
  (if gloas : .glamsterdam ≤ fork then
    ((body.parentExecutionRequests gloas).deposits.data.toList.map (·.amount.toNat)).sum
  else if electra : .pectra ≤ fork then
    ((body.executionRequests ⟨electra, Nat.lt_of_not_le gloas⟩).deposits.data.toList.map
      (·.amount.toNat)).sum
  else 0)

/-- From Altair, the base reward of one increment at the total active balance of a state.

It is zero before Altair, and when the total or the reward cannot be computed. -/
def blockPerIncrement (preset : Preset) (state : BeaconState preset fork) : Nat :=
  if .altair ≤ fork then
    match getTotalActiveBalance state with
    | .ok total =>
      match getBaseRewardPerIncrement preset total with
      | .ok perIncrement => perIncrement.toNat
      | .error _ => 0
    | .error _ => 0
  else 0

/-- From Altair, the weight of the participation flags of a state, at a base reward per increment.

It sums over the positions of the registry, in the previous and the current epoch.

Each flag set counts the base reward of its validator times the weight of the flag.

That base reward is the number of whole increments of the effective balance, times the given one.

It is zero before Altair. -/
def flagRewardWeight (preset : Preset) (perIncrement : Nat) (state : BeaconState preset fork) :
    Nat :=
  if altair : .altair ≤ fork then
    let weigh (participation : EpochParticipation preset fork) : Nat :=
      ((List.range state.validators.data.size).map fun j =>
        ((participation.data[j]?).map fun flags =>
          ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
            if hasFlag flags flag.val.toUInt64 then
              ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0 /
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement *
                  PARTICIPATION_FLAG_WEIGHTS[flag].toNat
            else 0).sum).getD 0).sum
    weigh (state.previousEpochParticipation altair) + weigh (state.currentEpochParticipation altair)
  else 0

/-- From Altair, a bound on the rewards that a block pays for its sync aggregate.

It reads the base reward of one increment at the total active balance of the state.

Each sync committee member earns at most the participant reward, and the proposer a share.

It is zero before Altair, and when the total or the reward cannot be computed. -/
def syncRewardCap (preset : Preset) (state : BeaconState preset fork) : Nat :=
  if .altair ≤ fork then
    match getTotalActiveBalance state with
    | .ok total =>
      match getBaseRewardPerIncrement preset total with
      | .ok perIncrement =>
        let participant := total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          perIncrement.toNat * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
            preset.SLOTS_PER_EPOCH.toNat / preset.SYNC_COMMITTEE_SIZE.toNat
        preset.SYNC_COMMITTEE_SIZE.toNat * (participant + participant * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
      | .error _ => 0
    | .error _ => 0
  else 0

/-- From Altair, a bound on the rewards that a block pays to its proposer and its sync committee.

The attestations set each flag of each validator at most once in each of two epochs.

So they pay the proposer at most twice the base rewards of all the validators, times 54 over 448.

The weights of the three flags add up to 54, and the proposer share divides their sum by 448.

The sync aggregate adds its own bound. -/
def blockRewardCap (preset : Preset) (state : BeaconState preset fork) : Nat :=
  2 * (effectiveBalanceSum state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
      blockPerIncrement preset state * 54 / 448 +
    syncRewardCap preset state

/-! ## The supply and its rise -/

section Rise

/-- The balances plus the pending deposits of a state. -/
private def supply (state : BeaconState preset fork) : Nat :=
  balanceSum state + pendingDepositSum state

/-- The quotient of the whistleblower reward at the fork, on natural numbers. -/
private def quotient (preset : Preset) (fork : Fork) : Nat :=
  (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat

/-- A step raises the supply by at most an amount, plus a share of the new slashed balances.

The share is the rise of the slashed balances over the whistleblower quotient.

The slashed balances do not fall. -/
private def Rise (amount : Nat) (a b : BeaconState preset fork) : Prop :=
  slashedBalanceSum a ≤ slashedBalanceSum b ∧
    supply b ≤ supply a + amount +
      (slashedBalanceSum b - slashedBalanceSum a) / quotient preset fork

private theorem Rise.refl (a : BeaconState preset fork) : Rise 0 a a :=
  ⟨Nat.le_refl _, by simp⟩

private theorem Rise.trans {one two : Nat} {a b c : BeaconState preset fork}
    (first : Rise one a b) (second : Rise two b c) : Rise (one + two) a c := by
  refine ⟨Nat.le_trans first.1 second.1, ?_⟩
  have floors := Nat.div_add_div_le_add_div (x := slashedBalanceSum b - slashedBalanceSum a)
    (y := slashedBalanceSum c - slashedBalanceSum b) (z := quotient preset fork)
  have sum : slashedBalanceSum b - slashedBalanceSum a +
      (slashedBalanceSum c - slashedBalanceSum b) =
      slashedBalanceSum c - slashedBalanceSum a := by
    have := first.1
    have := second.1
    omega
  rw [sum] at floors
  have := first.2
  have := second.2
  omega

private theorem Rise.mono {small large : Nat} {a b : BeaconState preset fork}
    (rise : Rise small a b) (le : small ≤ large) : Rise large a b :=
  ⟨rise.1, by have := rise.2; omega⟩

/-- A step that keeps the slashed balances and raises the supply by at most an amount. -/
private theorem Rise.of_le {amount : Nat} {a b : BeaconState preset fork}
    (slashings : b.slashings = a.slashings) (le : supply b ≤ supply a + amount) :
    Rise amount a b := by
  have same : slashedBalanceSum b = slashedBalanceSum a := by
    unfold slashedBalanceSum
    rw [slashings]
  refine ⟨Nat.le_of_eq same.symm, ?_⟩
  rw [same, Nat.sub_self, Nat.zero_div, Nat.add_zero]
  exact le

/-- A fold raises the supply by at most the sum of the amounts of its steps. -/
private theorem Rise.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    {amount : α → Nat} (each : ∀ a x b, step a x = .ok b → Rise (amount x) a b) :
    ∀ {items : List α} {a b : BeaconState preset fork}, items.foldlM step a = .ok b →
      Rise ((items.map amount).sum) a b
  | [], a, b, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Rise.refl a
  | x :: items, a, b, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    simp only [List.map_cons, List.sum_cons]
    exact (each _ _ _ first).trans (Rise.foldlM each rest)

/-- A fold of steps that each raise nothing raises nothing. -/
private theorem Rise.foldlM_zero {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Rise 0 a b) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) : Rise 0 a b := by
  have := Rise.foldlM (amount := fun _ => 0) each computed
  simpa using this

end Rise

/-! ## Steps that keep the supply -/

section Fixed

/-- A step that keeps the balances, the pending deposits and the slashed balances.

It also keeps the participation flags of both recent epochs. -/
private def Fixed (a b : BeaconState preset fork) : Prop :=
  b.balances = a.balances ∧ b.pendingDeposits = a.pendingDeposits ∧ b.slashings = a.slashings ∧
    b.previousEpochParticipation = a.previousEpochParticipation ∧
    b.currentEpochParticipation = a.currentEpochParticipation

private theorem Fixed.refl (a : BeaconState preset fork) : Fixed a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Fixed.trans {a b c : BeaconState preset fork} (one : Fixed a b)
    (two : Fixed b c) : Fixed a c :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.trans one.2.2.2.2⟩

private theorem Fixed.same {a b : BeaconState preset fork} (fixed : Fixed a b) :
    supply b = supply a := by
  unfold supply balanceSum pendingDepositSum
  rw [fixed.1, fixed.2.1]

private theorem Fixed.rise {a b : BeaconState preset fork} (fixed : Fixed a b) : Rise 0 a b :=
  Rise.of_le fixed.2.2.1 (Nat.le_of_eq fixed.same)

private theorem fixed_setValidator {s t : BeaconState preset fork} {i : ValidatorIndex}
    {v : Validator} (ok : s.setValidator i v = .ok t) : Fixed s t := by
  obtain ⟨_, rfl⟩ := setValidator_ok ok
  exact Fixed.refl _

private theorem fixed_exit {s t : BeaconState preset fork} {i : ValidatorIndex}
    (ok : initiateValidatorExit config s i = .ok t) : Fixed s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · exact Fixed.refl _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    have set := fixed_setValidator set
    exact Fixed.trans ⟨rfl, rfl, rfl, rfl, rfl⟩ set

private theorem fixed_exitChurn {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (ok : computeExitEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    Fixed s t := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  cases ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem fixed_consolidationChurn {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {balance : Gwei} {epoch : Epoch}
    (ok : computeConsolidationEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    Fixed s t := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  cases ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem fixed_partialWithdrawal {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index validator amount owed = .ok t) :
    Fixed s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact (fixed_exitChurn churned).trans ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases ok
    exact Fixed.refl _

private theorem fixed_withdrawalRequest {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : Fixed s t := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · exact Fixed.refl _
  · exact fixed_exit exited
  · exact fixed_partialWithdrawal withdrawn

private theorem fixed_queueConsolidation {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Fixed s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churn, _, _, marked, set, pending, appended, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  exact ((fixed_consolidationChurn churn).trans (fixed_setValidator set)).trans
    ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem fixed_voluntaryExit {s t : BeaconState preset fork}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : Fixed s t :=
  fixed_exit (processVoluntaryExit_initiates ok)

private theorem fixed_blsChange {s t : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : Fixed s t := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact fixed_setValidator set

private theorem fixed_header {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    (ok : processBlockHeader s block = .ok t) : Fixed s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem fixed_randao {s t : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (ok : processRandao config checks s body = .ok t) : Fixed s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem fixed_eth1 {s t : BeaconState preset fork} {before : fork < .hegota}
    {body : BeaconBlockBody preset fork} (ok : processEth1Data before s body = .ok t) :
    Fixed s t := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest]⟩

private theorem fixed_payloadAttestation {s t : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {attestation : PayloadAttestation preset}
    (ok : processPayloadAttestation config checks s gloas attestation = .ok t) : Fixed s t := by
  rw [processPayloadAttestation_eq ok]
  exact Fixed.refl _

end Fixed

/-! ## Steps that move the supply -/

section Moves

/-- Writing a balance replaces its old value in the sum of the balances. -/
private theorem balanceSum_putBalance (s : BeaconState preset fork) {i : Nat}
    (inside : i < s.balances.data.size) (v : Gwei) :
    balanceSum (s.putBalance i inside v) + s.balances.data[i].toNat = balanceSum s + v.toNat := by
  unfold balanceSum BeaconState.putBalance
  simp only [Array.toList_set, List.map_set]
  have := sum_set_add (l := s.balances.data.toList.map (·.toNat)) (i := i)
    (by simpa using inside) v.toNat
  simp only [List.getElem_map, Array.getElem_toList] at this
  exact this

/-- Lowering a balance, down to zero at most, does not raise the sum of the balances. -/
private theorem balanceSum_decreaseBalance_le {s t : BeaconState preset fork}
    {i : ValidatorIndex} {d : Gwei} (ok : decreaseBalance s i d = .ok t) :
    balanceSum t ≤ balanceSum s := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  have sum := balanceSum_putBalance s inside (Uint64.saturatingSub s.balances.data[i.toNat] d)
  rw [Uint64.toNat_saturatingSub] at sum
  omega

/-- A deposit at the end of the queue adds its amount to the pending deposits. -/
private theorem pendingDepositSum_of_push {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deposit : PendingDeposit}
    (pushed : (t.pendingDeposits electra).data = (s.pendingDeposits electra).data.push deposit) :
    pendingDepositSum t = pendingDepositSum s + deposit.amount.toNat := by
  unfold pendingDepositSum pendingAmount
  simp [electra, pushed]

/-- A deposit request adds its amount to the pending deposits. -/
private theorem rise_depositRequest {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : DepositRequest} (ok : processDepositRequest s electra request = .ok t) :
    Rise request.amount.toNat s t := by
  obtain ⟨pushed, -, balances⟩ := processDepositRequest_ok ok
  have slashings : t.slashings = s.slashings := by
    obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
    simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
      bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    rfl
  have summed : balanceSum t = balanceSum s := by
    unfold balanceSum
    rw [balances]
  refine Rise.of_le slashings (Nat.le_of_eq ?_)
  unfold supply
  rw [pendingDepositSum_of_push electra pushed, summed]
  simp only [Nat.add_assoc]

/-- Moving the balance above the activation balance to the queue keeps the supply. -/
private theorem rise_queueExcess {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {index : ValidatorIndex} (ok : queueExcessActiveBalance s electra index = .ok t) :
    Rise 0 s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨balance, found, ok⟩ := ok
  split at ok
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨validator, _, pending, appended, mid, setOk, rfl⟩ := ok
    obtain ⟨inside, rfl⟩ := setBalance_ok setOk
    have old : s.balances.data[index.toNat] = balance := by
      unfold getBalance at found
      simpa [Array.getElem?_eq_getElem inside] using found
    have sum := balanceSum_putBalance s inside preset.MIN_ACTIVATION_BALANCE
    have pend := pendingDepositSum_of_push (s := s)
      (t := { s.putBalance index.toNat inside preset.MIN_ACTIVATION_BALANCE with
        pendingDeposits := fun _ => pending }) electra (appendWithinLimit_data appended)
    refine Rise.of_le rfl (Nat.le_of_eq ?_)
    have low := UInt64.lt_iff_toNat_lt.mp above
    rw [old] at sum
    unfold supply
    rw [pend, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)]
    change balanceSum (s.putBalance index.toNat inside preset.MIN_ACTIVATION_BALANCE) + _ = _
    omega
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact Rise.refl _

/-- A consolidation request moves at most an excess balance to the pending deposits. -/
private theorem rise_consolidationRequest {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : Rise 0 s t := by
  have compounding {a b : BeaconState preset fork} {index : ValidatorIndex}
      (switched : switchToCompoundingValidator a electra index = .ok b) : Rise 0 a b := by
    simp only [switchToCompoundingValidator, bind_ok_iff] at switched
    obtain ⟨_, _, _, set, queued⟩ := switched
    exact (fixed_setValidator set).rise.trans (rise_queueExcess queued)
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact Rise.refl _)
    | exact compounding (liftAccessor_ok.mp ok)
    | exact (fixed_queueConsolidation ok).rise

/-- Withdrawals lower the balances and keep the pending deposits. -/
private theorem rise_withdrawals {s t : BeaconState preset fork} {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) : Rise 0 s t := by
  have withdraw {a b : BeaconState preset fork} {w : Withdrawal}
      (applied : applyWithdrawal a w = .ok b) : Rise 0 a b := by
    have shape := applyWithdrawal_eq applied
    have slashings : b.slashings = a.slashings := by rw [shape]
    have pending : pendingDepositSum b = pendingDepositSum a := by
      unfold pendingDepositSum
      rw [shape]
    refine Rise.of_le slashings ?_
    unfold applyWithdrawal at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, set⟩ := applied
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      exact Nat.le_refl _
    · unfold supply
      have := balanceSum_decreaseBalance_le applied
      omega
  have expected {a b : BeaconState preset fork} {expected : ExpectedWithdrawals}
      (applied : applyExpectedWithdrawals a capella expected = .ok b) : Rise 0 a b := by
    apply applyExpectedWithdrawals_of_setters (Rise 0) Rise.refl
      (fun one two => by simpa using one.trans two) withdraw _ _ _ _ _ _ applied
    all_goals exact fun _ _ => Fixed.rise ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact expected applied
    · cases ok
      exact Rise.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact expected applied

/-- The execution part of a block does not raise the supply. -/
private theorem rise_blockExecution {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) : Rise 0 s t := by
  have payload {a b : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (paid : processExecutionPayload config engine a body execution = .ok b) : Rise 0 a b := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    exact Fixed.rise ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact (rise_withdrawals withdrawn).trans (Fixed.rise ⟨rfl, rfl, rfl, rfl, rfl⟩)
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (rise_withdrawals withdrawn).trans (payload paid)
  · dsimp only at ok
    split at ok
    · exact payload ok
    · cases ok
      exact Rise.refl _

/-- The payload of the parent brings the amounts of its deposit requests. -/
private theorem rise_parentPayload {s t : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks s gloas body = .ok t) :
    Rise (((body.parentExecutionRequests gloas).deposits.data.toList.map
      (·.amount.toNat)).sum) s t := by
  rcases processParentExecutionPayload_ok ok with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact (Rise.refl _).mono (Nat.zero_le _)
  have settle : Fixed s settled := by
    rw [settleParentPayment_eq settledOk]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have deposits := Rise.foldlM (amount := fun request : DepositRequest => request.amount.toNat)
    (fun _ _ _ ok => rise_depositRequest ok) depositsOk
  have withdrawals := Rise.foldlM_zero (fun _ _ _ ok => (fixed_withdrawalRequest ok).rise)
    withdrawalsOk
  have consolidations := Rise.foldlM_zero (fun _ _ _ ok => rise_consolidationRequest ok)
    consolidationsOk
  have builders := Rise.foldlM_zero (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_eq ok
    exact Fixed.rise ⟨rfl, rfl, rfl, rfl, rfl⟩) buildersOk
  have exits := Rise.foldlM_zero (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_eq ok
    exact Fixed.rise ⟨rfl, rfl, rfl, rfl, rfl⟩) exitsOk
  have whole := (settle.rise.trans deposits).trans <| withdrawals.trans <| consolidations.trans <|
    builders.trans <| exits.trans (Fixed.rise ⟨rfl, rfl, rfl, rfl, rfl⟩)
  exact whole.mono (by simp)

/-- Raising a balance adds the amount to the supply, and keeps the slashed balances. -/
private theorem increase_facts {s t : BeaconState preset fork} {i : ValidatorIndex} {d : Gwei}
    (ok : increaseBalance s i d = .ok t) :
    t.slashings = s.slashings ∧ supply t = supply s + d.toNat := by
  have summed := balanceSum_increaseBalance ok
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  refine ⟨rfl, ?_⟩
  unfold supply at *
  rw [summed]
  simp only [pendingDepositSum, BeaconState.putBalance]
  omega

/-- Lowering a balance does not raise the supply, and keeps the slashed balances. -/
private theorem decrease_facts {s t : BeaconState preset fork} {i : ValidatorIndex} {d : Gwei}
    (ok : decreaseBalance s i d = .ok t) : t.slashings = s.slashings ∧ supply t ≤ supply s := by
  have lowered := balanceSum_decreaseBalance_le ok
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  refine ⟨rfl, ?_⟩
  unfold supply at *
  simp only [pendingDepositSum, BeaconState.putBalance] at lowered ⊢
  omega

/-- A slashing pays at most the whistleblower reward, and adds the effective balance it reads.

That reward is the effective balance over the whistleblower quotient. -/
private theorem rise_slashValidator {a b : BeaconState preset fork} {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config a i whistleblower = .ok b) : Rise 0 a b := by
  obtain ⟨exited, validator, delay, marked, slashed, total, slashings, lowered, proposer, reward,
    raised, last, exitedOk, _, _, markedOk, readOk, totalOk, writeOk, loweredOk, _, rewardOk,
    raisedOk, lastOk, done⟩ := slashValidator_ok ok
  have earlier : Fixed a marked := (fixed_exit exitedOk).trans (fixed_setValidator markedOk)
  have low := decrease_facts loweredOk
  have first := increase_facts raisedOk
  have second := increase_facts lastOk
  -- Cancelling the payments of builders keeps the supply and the slashed balances.
  have cancelled : b.slashings = last.slashings ∧ supply b = supply last := by
    subst done
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have share := proposerShare_le rewardOk
  -- The slashed balances rise by the effective balance of the validator.
  have nonzero : preset.EPOCHS_PER_SLASHINGS_VECTOR ≠ 0 := by
    intro zero
    simp [readCircular, zero] at readOk
  simp only [readCircular, nonzero, ↓reduceDIte, Except.ok.injEq] at readOk
  simp only [writeCircularRooted, nonzero, ↓reduceDIte, Except.ok.injEq] at writeOk
  obtain ⟨_, totalNat⟩ := Base.Uint64.addChecked_ok_iff.mp totalOk
  have finalSlashings : b.slashings = slashings :=
    cancelled.1.trans (second.1.trans (first.1.trans low.1))
  have summed : slashedBalanceSum b + slashed.toNat = slashedBalanceSum a + total.toNat := by
    unfold slashedBalanceSum
    rw [finalSlashings, ← writeOk, ← readOk, ← earlier.2.2.1]
    simp only [Serialization.Ssz.RootedVector.elements_set, Vector.toList_set, List.map_set]
    have moved := sum_set_add (l := marked.slashings.elements.toList.map (·.toNat))
      (i := (getCurrentEpoch a % preset.EPOCHS_PER_SLASHINGS_VECTOR).toNat)
      (by simp only [List.length_map, Vector.length_toList]; exact toNat_mod_lt nonzero)
      total.toNat
    simpa using moved
  have markedSupply : supply { marked with slashings } = supply a := by
    have := earlier.same
    unfold supply at this ⊢
    exact this
  have difference : (validator.effectiveBalance /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT - reward).toNat =
      (validator.effectiveBalance /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat - reward.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr share)
  rw [UInt64.toNat_div] at share difference
  refine ⟨by omega, ?_⟩
  have rise : slashedBalanceSum b - slashedBalanceSum a = validator.effectiveBalance.toNat := by
    omega
  rw [rise]
  unfold quotient
  have := low.2
  rw [markedSupply] at this
  omega

/-- A new validator keeps the slashed balances and the pending deposits.

It raises the sum of the balances by at most its amount. -/
private theorem add_facts {s t : BeaconState preset fork} {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    t.slashings = s.slashings ∧ t.pendingDeposits = s.pendingDeposits ∧
      balanceSum t ≤ balanceSum s + amount.toNat := by
  unfold addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨index, _, _, _, balances, balancesOk, _, _, _, _, _, _, rfl⟩ := ok
    refine ⟨rfl, rfl, ?_⟩
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
        have := sum_set_add (l := s.balances.data.toList.map (·.toNat))
          (i := index.toNat) (by simpa using inside) amount.toNat
        omega
      · cases balancesOk
  · split at ok
    · cases ok
      exact ⟨rfl, rfl, by simp [balanceSum]⟩
    · cases ok

/-- A deposit of a block raises the supply by at most its amount. -/
private theorem rise_deposit {s t : BeaconState preset fork} {before : fork < .hegota}
    {deposit : Deposit} (ok : processDeposit config checks before s deposit = .ok t) :
    Rise deposit.data.amount.toNat s t := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok ok
  have start : Fixed s { s with eth1DepositIndex := fun _ => next } := ⟨rfl, rfl, rfl, rfl, rfl⟩
  suffices rest : ∀ {u : BeaconState preset fork}, applyDeposit config checks u
      deposit.data.pubkey deposit.data.withdrawalCredentials deposit.data.amount
      deposit.data.signature = .ok t → Rise deposit.data.amount.toNat u t by
    simpa using start.rise.trans (rest applied)
  intro u applied
  have queue {middle : BeaconState preset fork} (electra : .pectra ≤ fork)
      (queued : addPendingDeposit middle electra ⟨deposit.data.pubkey,
        deposit.data.withdrawalCredentials, deposit.data.amount, deposit.data.signature,
        GENESIS_SLOT⟩ = .ok t) :
      t.slashings = middle.slashings ∧
        supply t = supply middle + deposit.data.amount.toNat := by
    simp only [addPendingDeposit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨pending, appended, rfl⟩ := queued
    have pend := pendingDepositSum_of_push (s := middle)
      (t := { middle with pendingDeposits := fun _ => pending }) electra
      (appendWithinLimit_data appended)
    refine ⟨rfl, ?_⟩
    unfold supply
    rw [pend]
    simp only [balanceSum]
    omega
  unfold applyDeposit at applied
  split at applied
  · rename_i electra
    unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨middle, added, queued⟩ := applied
        obtain ⟨slashings, pending, balances⟩ := add_facts added
        have pendingSum : pendingDepositSum middle = pendingDepositSum u := by
          unfold pendingDepositSum
          rw [pending]
        have queued := queue electra queued
        refine Rise.of_le (queued.1.trans slashings) ?_
        rw [queued.2]
        unfold supply
        simp only [UInt64.toNat_zero, Nat.add_zero] at balances
        omega
      · cases applied
        exact (Rise.refl _).mono (Nat.zero_le _)
    · have queued := queue electra (liftAccessor_ok.mp applied)
      exact Rise.of_le queued.1 (Nat.le_of_eq queued.2)
  · rename_i early
    have balances := balanceSum_applyPendingDeposit_le applied
    have pending : pendingDepositSum t = pendingDepositSum u := by
      unfold pendingDepositSum
      simp [early]
    have slashings : t.slashings = u.slashings := by
      rcases applyPendingDeposit_cases applied with rfl | ⟨_, raised⟩ | ⟨_, added⟩
      · rfl
      · exact (increase_facts raised).1
      · exact (add_facts added).1
    refine Rise.of_le slashings ?_
    unfold supply
    simp only at balances
    omega

private theorem rise_proposerSlashing {a b : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks a slashing = .ok b) : Rise 0 a b := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact rise_slashValidator slashed

private theorem rise_attesterSlashing {a b : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks a slashing = .ok b) : Rise 0 a b := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step : BeaconState preset fork × Bool => Rise 0 a step.1)
    (fun step _ _ before ok => ?_) (Rise.refl a) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact before.trans (rise_slashValidator slashed)
  · cases ok
    exact before

end Moves

/-! ## Steps that keep the participation flags -/

section Kept

/-- A step that keeps the participation flags of both recent epochs. -/
private def Flags (a b : BeaconState preset fork) : Prop :=
  b.previousEpochParticipation = a.previousEpochParticipation ∧
    b.currentEpochParticipation = a.currentEpochParticipation

private theorem Flags.refl (a : BeaconState preset fork) : Flags a a := ⟨rfl, rfl⟩

private theorem Flags.trans {a b c : BeaconState preset fork} (one : Flags a b)
    (two : Flags b c) : Flags a c :=
  ⟨two.1.trans one.1, two.2.trans one.2⟩

private theorem Fixed.flags {a b : BeaconState preset fork} (fixed : Fixed a b) : Flags a b :=
  fixed.2.2.2

private theorem Flags.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Flags a b) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) : Flags a b :=
  (foldlM_ok_steps Flags Flags.refl Flags.trans each computed).1

private theorem flags_setBalance {s t : BeaconState preset fork} {i : ValidatorIndex} {v : Gwei}
    (ok : s.setBalance i v = .ok t) : Flags s t := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  exact ⟨rfl, rfl⟩

private theorem flags_increase {s t : BeaconState preset fork} {i : ValidatorIndex} {d : Gwei}
    (ok : increaseBalance s i d = .ok t) : Flags s t :=
  flags_setBalance (increaseBalance_ok ok).choose_spec

private theorem flags_decrease {s t : BeaconState preset fork} {i : ValidatorIndex} {d : Gwei}
    (ok : decreaseBalance s i d = .ok t) : Flags s t :=
  flags_setBalance (decreaseBalance_ok ok).choose_spec

private theorem flags_depositRequest {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : DepositRequest} (ok : processDepositRequest s electra request = .ok t) :
    Flags s t := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact ⟨rfl, rfl⟩

private theorem flags_queueExcess {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {index : ValidatorIndex} (ok : queueExcessActiveBalance s electra index = .ok t) :
    Flags s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, setOk, rfl⟩ := ok
    have set := flags_setBalance setOk
    exact set.trans ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact Flags.refl _

private theorem flags_consolidationRequest {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : Flags s t := by
  have compounding {a b : BeaconState preset fork} {index : ValidatorIndex}
      (switched : switchToCompoundingValidator a electra index = .ok b) : Flags a b := by
    simp only [switchToCompoundingValidator, bind_ok_iff] at switched
    obtain ⟨_, _, _, set, queued⟩ := switched
    exact (fixed_setValidator set).flags.trans (flags_queueExcess queued)
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact Flags.refl _)
    | exact compounding (liftAccessor_ok.mp ok)
    | exact (fixed_queueConsolidation ok).flags

private theorem flags_withdrawals {s t : BeaconState preset fork} {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) : Flags s t := by
  have withdraw {a b : BeaconState preset fork} {w : Withdrawal}
      (applied : applyWithdrawal a w = .ok b) : Flags a b := by
    have shape := applyWithdrawal_eq applied
    exact ⟨by rw [shape], by rw [shape]⟩
  have expected {a b : BeaconState preset fork} {expected : ExpectedWithdrawals}
      (applied : applyExpectedWithdrawals a capella expected = .ok b) : Flags a b := by
    apply applyExpectedWithdrawals_of_setters Flags Flags.refl
      (fun one two => one.trans two) withdraw _ _ _ _ _ _ applied
    all_goals exact fun _ _ => ⟨rfl, rfl⟩
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact expected applied
    · cases ok
      exact Flags.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact expected applied

private theorem flags_blockExecution {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) : Flags s t := by
  have payload {a b : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (paid : processExecutionPayload config engine a body execution = .ok b) : Flags a b := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    exact ⟨rfl, rfl⟩
  unfold processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact (flags_withdrawals withdrawn).trans ⟨rfl, rfl⟩
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (flags_withdrawals withdrawn).trans (payload paid)
  · dsimp only at ok
    split at ok
    · exact payload ok
    · cases ok
      exact Flags.refl _

private theorem flags_parentPayload {s t : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks s gloas body = .ok t) : Flags s t := by
  rcases processParentExecutionPayload_ok ok with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact Flags.refl _
  have settle : Flags s settled := by
    rw [settleParentPayment_eq settledOk]
    exact ⟨rfl, rfl⟩
  exact settle.trans <|
    (Flags.foldlM (fun _ _ _ ok => flags_depositRequest ok) depositsOk).trans <|
    (Flags.foldlM (fun _ _ _ ok => (fixed_withdrawalRequest ok).flags) withdrawalsOk).trans <|
    (Flags.foldlM (fun _ _ _ ok => flags_consolidationRequest ok) consolidationsOk).trans <|
    (Flags.foldlM (fun _ _ _ ok => by
      obtain ⟨_, rfl⟩ := processBuilderDepositRequest_eq ok
      exact ⟨rfl, rfl⟩) buildersOk).trans <|
    (Flags.foldlM (fun _ _ _ ok => by
      obtain ⟨_, rfl⟩ := processBuilderExitRequest_eq ok
      exact ⟨rfl, rfl⟩) exitsOk).trans ⟨rfl, rfl⟩

private theorem flags_slashValidator {a b : BeaconState preset fork} {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config a i whistleblower = .ok b) : Flags a b := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, exitedOk, _, _, markedOk, _, _, _, loweredOk, _, _,
    raisedOk, lastOk, done⟩ := slashValidator_ok ok
  have earlier := (fixed_exit exitedOk).trans (fixed_setValidator markedOk)
  refine earlier.flags.trans <| (flags_decrease loweredOk).trans <|
    (flags_increase raisedOk).trans <| (flags_increase lastOk).trans ?_
  subst done
  split
  · exact ⟨rfl, rfl⟩
  · exact Flags.refl _

private theorem flags_proposerSlashing {a b : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks a slashing = .ok b) : Flags a b := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact flags_slashValidator slashed

private theorem flags_attesterSlashing {a b : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks a slashing = .ok b) : Flags a b := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step : BeaconState preset fork × Bool => Flags a step.1)
    (fun step _ _ before ok => ?_) (Flags.refl a) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact before.trans (flags_slashValidator slashed)
  · cases ok
    exact before

/-- The steps before the operations keep the participation flags. -/
private theorem flags_operationsInput {engine : ExecutionEngine preset fork}
    {state input : BeaconState preset fork} {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input) : Flags state input :=
  started.step_of Flags Flags.refl Flags.trans (fun _ ok => flags_parentPayload ok)
    (fun ok => (fixed_header ok).flags) (fun _ ok => flags_blockExecution ok)
    (fun ok => (fixed_randao ok).flags) (fun _ ok => (fixed_eth1 ok).flags)

/-- The participation flags at each position below the size of the earlier registry stay. -/
private def FlagsBelow (a b : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) j, j < a.validators.data.size →
    (b.previousEpochParticipation altair).data[j]? =
        (a.previousEpochParticipation altair).data[j]? ∧
      (b.currentEpochParticipation altair).data[j]? =
        (a.currentEpochParticipation altair).data[j]?

/-- A step that grows the registry, keeps its effective balances and the flags below its size. -/
private def Tail (a b : BeaconState preset fork) : Prop :=
  a.validators.data.size ≤ b.validators.data.size ∧ EffectiveKept a b ∧ FlagsBelow a b

private theorem Tail.refl (a : BeaconState preset fork) : Tail a a :=
  ⟨Nat.le_refl _, effectiveKept_refl a, fun _ _ _ => ⟨rfl, rfl⟩⟩

private theorem Tail.trans {a b c : BeaconState preset fork} (one : Tail a b) (two : Tail b c) :
    Tail a c :=
  ⟨Nat.le_trans one.1 two.1, effectiveKept_trans one.2.1 two.2.1 one.1,
    fun altair j inside =>
      ⟨((two.2.2 altair j (Nat.lt_of_lt_of_le inside one.1)).1).trans
          (one.2.2 altair j inside).1,
        ((two.2.2 altair j (Nat.lt_of_lt_of_le inside one.1)).2).trans
          (one.2.2 altair j inside).2⟩⟩

private theorem Tail.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Tail a b) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) : Tail a b :=
  (foldlM_ok_steps Tail Tail.refl Tail.trans each computed).1

private theorem Tail.of_flags {a b : BeaconState preset fork}
    (grows : a.validators.data.size ≤ b.validators.data.size) (kept : EffectiveKept a b)
    (flags : Flags a b) : Tail a b :=
  ⟨grows, kept, fun _ _ _ => ⟨by rw [flags.1], by rw [flags.2]⟩⟩

/-- A new validator takes the position at the end of the registry, and keeps the earlier flags. -/
private theorem flagsBelow_add {s t : BeaconState preset fork} {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) : FlagsBelow s t := by
  intro altair j inside
  unfold addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨index, indexOk, _, _, _, _, previous, previousOk, current, currentOk, _, _, rfl⟩ := ok
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    have apart : j ≠ index.toNat := by omega
    exact ⟨by simpa [apart] using setOrAppendList_getElem? previousOk j,
      by simpa [apart] using setOrAppendList_getElem? currentOk j⟩
  · exact absurd altair ‹_›

/-- A deposit of a block keeps the flags below the size of the registry. -/
private theorem flagsBelow_deposit {s t : BeaconState preset fork} {before : fork < .hegota}
    {deposit : Deposit} (ok : processDeposit config checks before s deposit = .ok t) :
    FlagsBelow s t := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok ok
  suffices rest : ∀ {u : BeaconState preset fork}, u.validators = s.validators → Flags s u →
      applyDeposit config checks u deposit.data.pubkey deposit.data.withdrawalCredentials
        deposit.data.amount deposit.data.signature = .ok t → FlagsBelow s t from
    rest (u := { s with eth1DepositIndex := fun _ => next }) rfl ⟨rfl, rfl⟩ applied
  intro u validators flags applied altair j inside
  have kept : ∀ {v : BeaconState preset fork}, Flags u v → FlagsBelow s v := by
    intro v later _ _ _
    exact ⟨by rw [later.1, flags.1], by rw [later.2, flags.2]⟩
  have added : ∀ {v w : BeaconState preset fork} {amount : Gwei},
      addValidatorToRegistry u deposit.data.pubkey deposit.data.withdrawalCredentials amount =
        .ok v → Flags v w → FlagsBelow s w := by
    intro v w amount addedOk later _ i below
    have below' : i < u.validators.data.size := by rw [validators]; exact below
    have step := flagsBelow_add addedOk altair i below'
    exact ⟨by rw [later.1, step.1, flags.1], by rw [later.2, step.2, flags.2]⟩
  have queue : ∀ {v : BeaconState preset fork} (electra : .pectra ≤ fork)
      {pending : PendingDeposit}, addPendingDeposit v electra pending = .ok t → Flags v t := by
    intro v electra pending queued
    obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
    exact ⟨rfl, rfl⟩
  unfold applyDeposit at applied
  split at applied
  · rename_i electra
    unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨middle, addedOk, queued⟩ := applied
        exact added addedOk (queue electra queued) altair j inside
      · cases applied
        exact kept (Flags.refl _) altair j inside
    · exact kept (queue electra (liftAccessor_ok.mp applied)) altair j inside
  · rcases applyPendingDeposit_cases applied with rfl | ⟨_, raised⟩ | ⟨_, addedOk⟩
    · exact kept (Flags.refl _) altair j inside
    · exact kept (flags_increase raised) altair j inside
    · exact added addedOk (Flags.refl _) altair j inside

end Kept

/-! ## The active balance along a block -/

section Totals

/-- A step that keeps the slot, the activity and the earlier effective balances keeps the total.

The registry must not shrink. -/
private theorem total_congr {s t : BeaconState preset fork} (step : ActiveStep s t)
    (kept : EffectiveKept s t) (grows : s.validators.data.size ≤ t.validators.data.size) :
    getTotalActiveBalance t = getTotalActiveBalance s := by
  classical
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, step.1]
  have active := step.2.mono (getCurrentEpoch_le_activityFixedEpoch s)
  have checked := active.getActiveValidatorIndicesChecked_eq (UInt64.le_refl _)
  unfold getTotalActiveBalance
  rw [epoch, checked]
  cases found : getActiveValidatorIndicesChecked s (getCurrentEpoch s) with
  | error e => rfl
  | ok indices =>
    simp only [bind, Except.bind]
    have inside (i : ValidatorIndex) (member : i ∈ indices) :
        i.toNat < s.validators.data.size := by
      obtain ⟨_, there, _⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok found).mp member
      exact (Array.getElem?_eq_some_iff.mp there).1
    have sum : Models.stake (fun i => balanceAt t i.toNat) indices.toFinset =
        Models.stake (fun i => balanceAt s i.toNat) indices.toFinset := by
      apply Finset.sum_congr rfl
      intro i member
      exact kept i.toNat (inside i (List.mem_toFinset.mp member))
    have sourceNone : indices.find? (s.validators.data.size ≤ ·.toNat) = none := by
      apply List.find?_eq_none.mpr
      intro i member
      have := inside i member
      simp only [decide_eq_true_eq]
      omega
    have targetNone : indices.find? (t.validators.data.size ≤ ·.toNat) = none := by
      apply List.find?_eq_none.mpr
      intro i member
      have := inside i member
      simp only [decide_eq_true_eq]
      omega
    simp only [getTotalBalance, sourceNone, targetNone, sumMarked_markIndices_eq_stake, sum]

/-- A step that keeps the slot, the activity, the effective balances and the size of the registry.
-/
private def Steady (a b : BeaconState preset fork) : Prop :=
  ActiveStep a b ∧ EffectiveKept a b ∧ b.validators.data.size = a.validators.data.size

private theorem Steady.refl (a : BeaconState preset fork) : Steady a a :=
  ⟨ActiveStep.refl a, effectiveKept_refl a, rfl⟩

private theorem Steady.trans {a b c : BeaconState preset fork} (one : Steady a b)
    (two : Steady b c) : Steady a c :=
  ⟨one.1.trans two.1, effectiveKept_trans one.2.1 two.2.1 (Nat.le_of_eq one.2.2.symm),
    two.2.2.trans one.2.2⟩

private theorem Steady.of_validators {a b : BeaconState preset fork}
    (validators : b.validators = a.validators) (slot : b.slot = a.slot) : Steady a b :=
  ⟨ActiveStep.of_validators (congrArg (·.data) validators) slot,
    effectiveKept_data (congrArg (·.data) validators), by rw [validators]⟩

/-- A steady step keeps the sum of the effective balances. -/
private theorem Steady.effectiveBalanceSum_eq {a b : BeaconState preset fork}
    (steady : Steady a b) :
    effectiveBalanceSum b = effectiveBalanceSum a := by
  rw [effectiveBalanceSum_eq_sum_range, effectiveBalanceSum_eq_sum_range, steady.2.2]
  congr 1
  refine List.map_congr_left fun j member => ?_
  exact steady.2.1 j (List.mem_range.mp member)

private theorem Steady.total {a b : BeaconState preset fork} (steady : Steady a b) :
    getTotalActiveBalance b = getTotalActiveBalance a :=
  total_congr steady.1 steady.2.1 (Nat.le_of_eq steady.2.2.symm)

end Totals

/-! ## The flags of participation as a potential -/

section Flags

/-- The weighted base reward of each flag set, for one validator. -/
private def flagValue (flags : ParticipationFlags) (base : Nat) : Nat :=
  ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
    if hasFlag flags flag.val.toUInt64 then base * PARTICIPATION_FLAG_WEIGHTS[flag].toNat
    else 0).sum

/-- The base reward of a position, read from the effective balances of a fixed state. -/
private def baseAt (first : BeaconState preset fork) (perIncrement : Nat) (j : Nat) : Nat :=
  effectiveAt ⟨fork, first⟩ j / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement

/-- The weighted base rewards of the flags set in a list, over the positions of a fixed registry.
-/
private def flagSum (first : BeaconState preset fork) (perIncrement : Nat)
    (participation : EpochParticipation preset fork) : Nat :=
  ((List.range first.validators.data.size).map fun j =>
    ((participation.data[j]?).map (flagValue · (baseAt first perIncrement j))).getD 0).sum

/-- A sum over a list with no repeat gains one term when one test turns from false to true. -/
private theorem sum_ite_flip {α : Type} [DecidableEq α] {P Q : α → Bool} {c : α → Nat} {f : α}
    (here : P f = false) (there : Q f = true) (others : ∀ g, g ≠ f → Q g = P g) :
    ∀ {l : List α}, l.Nodup → f ∈ l →
      (l.map fun g => if Q g then c g else 0).sum =
        (l.map fun g => if P g then c g else 0).sum + c f
  | [], _, member => absurd member List.not_mem_nil
  | g :: l, distinct, member => by
    rw [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases same : g = f
    · subst same
      have rest : (l.map fun h => if Q h then c h else 0) =
          l.map fun h => if P h then c h else 0 :=
        List.map_congr_left fun h inside => by
          rw [others h fun equal => distinct.1 (equal ▸ inside)]
      rw [rest, here, there]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · rw [others g same, sum_ite_flip here there others distinct.2
        ((List.mem_cons.mp member).resolve_left (Ne.symm same))]
      omega

/-- Setting a flag not yet set adds its weighted base reward. -/
private theorem flagValue_addFlag {flags : ParticipationFlags}
    {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length} (unset : hasFlag flags flag.val.toUInt64 = false)
    (base : Nat) :
    flagValue (addFlag flags flag.val.toUInt64) base =
      flagValue flags base + base * PARTICIPATION_FLAG_WEIGHTS[flag].toNat := by
  have key := sum_ite_flip (P := fun g : Fin PARTICIPATION_FLAG_WEIGHTS.length =>
      hasFlag flags g.val.toUInt64)
    (Q := fun g => hasFlag (addFlag flags flag.val.toUInt64) g.val.toUInt64)
    (c := fun g => base * PARTICIPATION_FLAG_WEIGHTS[g].toNat) (f := flag) unset
    (hasFlag_addFlag flags _) (fun _ different => hasFlag_addFlag_of_ne flags different)
    (List.nodup_finRange _) (List.mem_finRange _)
  unfold flagValue
  exact key

/-- The flags of one validator weigh at most 54 base rewards. -/
private theorem flagValue_le (flags : ParticipationFlags) (base : Nat) :
    flagValue flags base ≤ base * 54 := by
  unfold flagValue
  have bound := sum_map_le_sum_map (xs := List.finRange PARTICIPATION_FLAG_WEIGHTS.length)
    (f := fun flag => if hasFlag flags flag.val.toUInt64 then
      base * PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0)
    (g := fun flag => base * PARTICIPATION_FLAG_WEIGHTS[flag].toNat)
    fun flag _ => by
      split
      · exact Nat.le_refl _
      · exact Nat.zero_le _
  refine bound.trans (Nat.le_of_eq ?_)
  simp [List.finRange_succ, PARTICIPATION_FLAG_WEIGHTS, TIMELY_SOURCE_WEIGHT, TIMELY_TARGET_WEIGHT,
    TIMELY_HEAD_WEIGHT]
  omega

/-- No base reward weighs nothing. -/
private theorem flagValue_zero (flags : ParticipationFlags) : flagValue flags 0 = 0 := by
  simp [flagValue]

/-- A position past the fixed registry has no base reward. -/
private theorem baseAt_of_le {first : BeaconState preset fork} {perIncrement j : Nat}
    (outside : first.validators.data.size ≤ j) : baseAt first perIncrement j = 0 := by
  simp [baseAt, effectiveAt, Array.getElem?_eq_none outside]

/-- From Altair, a base reward read in a state with the fixed registry is the one of its position.
-/
private theorem baseAt_of_getBaseReward (altair : .altair ≤ fork)
    {s first : BeaconState preset fork} (validators : s.validators = first.validators)
    {total perIncrement : Gwei}
    (perIncrementOk : getBaseRewardPerIncrement preset total = .ok perIncrement)
    {index : ValidatorIndex} {base : Gwei} (computed : getBaseReward s total index = .ok base) :
    base.toNat = baseAt first perIncrement.toNat index.toNat := by
  simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff, liftArith, mapError_ok_iff,
    perIncrementOk, Uint64.mulChecked_ok_iff] at computed
  obtain ⟨validator, found, _, same, -, value⟩ := computed
  cases Except.ok.inj same
  rw [getValidator_eq_getValidatorAt, getValidatorAt_eq_ok_iff] at found
  rw [validators] at found
  rw [value, UInt64.toNat_div]
  simp [baseAt, effectiveAt, found]

/-- A sum grows by an offset when one term does and no other term falls. -/
private theorem sum_range_offset {f g : Nat → Nat} {i a c : Nat} :
    ∀ {count : Nat}, i < count → a + f i ≤ c + g i → (∀ j < count, j ≠ i → f j ≤ g j) →
      a + ((List.range count).map f).sum ≤ c + ((List.range count).map g).sum
  | 0, inside, _, _ => absurd inside (Nat.not_lt_zero _)
  | count + 1, inside, here, others => by
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    by_cases last : i = count
    · subst last
      have below := sum_map_le_sum_map (xs := List.range i) (f := f) (g := g) fun j member =>
        others j (by have := List.mem_range.mp member; omega)
          (by have := List.mem_range.mp member; omega)
      omega
    · have below := sum_range_offset (count := count) (by omega) here
        (fun j lt apart => others j (by omega) apart)
      have top := others count (by omega) (Ne.symm last)
      omega

/-- Writing the flags of one position moves the flag sum by the change at that position. -/
private theorem flagSum_step {first : BeaconState preset fork} {perIncrement : Nat}
    {p q : EpochParticipation preset fork} {i a c : Nat} {old new : ParticipationFlags}
    (oldAt : p.data[i]? = some old) (newAt : q.data[i]? = some new)
    (others : ∀ j, j ≠ i → q.data[j]? = p.data[j]?)
    (step : a + flagValue old (baseAt first perIncrement i) ≤
      c + flagValue new (baseAt first perIncrement i)) :
    a + flagSum first perIncrement p ≤ c + flagSum first perIncrement q := by
  unfold flagSum
  by_cases inside : i < first.validators.data.size
  · refine sum_range_offset inside (by simpa [oldAt, newAt] using step) fun j _ apart => ?_
    rw [others j apart]
  · rw [baseAt_of_le (Nat.le_of_not_lt inside), flagValue_zero, flagValue_zero] at step
    have same : ((List.range first.validators.data.size).map fun j =>
        ((q.data[j]?).map (flagValue · (baseAt first perIncrement j))).getD 0) =
        (List.range first.validators.data.size).map fun j =>
          ((p.data[j]?).map (flagValue · (baseAt first perIncrement j))).getD 0 :=
      List.map_congr_left fun j member => by
        rw [others j fun equal => inside (equal ▸ List.mem_range.mp member)]
    rw [same]
    omega

/-- Setting the flags of one attester raises its flag value by at least the numerator gained.

The base reward of the attester must be the one given, whenever it is read. -/
private theorem flagValue_foldlM_addFlagReward {s : BeaconState preset fork} {total : Gwei}
    {earned : List UInt64} {index : ValidatorIndex} {b : Nat}
    (based : ∀ base, getBaseReward s total index = .ok base → base.toNat = b)
    {flagList : List (Fin PARTICIPATION_FLAG_WEIGHTS.length)} {flags : ParticipationFlags}
    {numerator : Gwei} {result : ParticipationFlags × Gwei}
    (computed :
      flagList.foldlM (addFlagReward s total earned index) (flags, numerator) = .ok result) :
    result.2.toNat + flagValue flags b ≤ numerator.toNat + flagValue result.1 b := by
  refine foldlM_ok_invariant (fun step : ParticipationFlags × Gwei =>
      step.2.toNat + flagValue flags b ≤ numerator.toNat + flagValue step.1 b)
    (fun step flag next before ok => ?_) (Nat.le_refl _) computed
  obtain ⟨current, gained⟩ := step
  simp only [addFlagReward] at ok
  split at ok
  · rename_i newly
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨reward, rewardOk, weighted, weightedOk, added, addedOk, rfl⟩ := ok
    rw [Uint64.mulChecked_ok_iff] at weightedOk
    rw [Uint64.addChecked_ok_iff] at addedOk
    have value := flagValue_addFlag newly.2 b
    have read := based reward rewardOk
    simp only at before ⊢
    rw [value, addedOk.2, weightedOk.2, read]
    omega
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact before

/-- Setting the flags of the attesters raises the flag sum by at least the numerator gained.

The base reward of each attester must be the one of its position, whenever it is read. -/
private theorem flagSum_foldlM_addAttesterFlags {s first : BeaconState preset fork}
    {total : Gwei} {perIncrement : Nat} {earned : List UInt64}
    (based : ∀ index base, getBaseReward s total index = .ok base →
      base.toNat = baseAt first perIncrement index.toNat)
    {attesters : List ValidatorIndex} {participation : EpochParticipation preset fork}
    {numerator : Gwei} {result : EpochParticipation preset fork × Gwei}
    (computed : attesters.foldlM (addAttesterFlags s total earned) (participation, numerator) =
      .ok result) :
    result.2.toNat + flagSum first perIncrement participation ≤
      numerator.toNat + flagSum first perIncrement result.1 := by
  refine foldlM_ok_invariant (fun step : EpochParticipation preset fork × Gwei =>
      step.2.toNat + flagSum first perIncrement participation ≤
        numerator.toNat + flagSum first perIncrement step.1)
    (fun step index next before ok => ?_) (Nat.le_refl _) computed
  obtain ⟨current, gained⟩ := step
  unfold addAttesterFlags at ok
  dsimp only at ok
  split at ok
  · rename_i inside
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨flags, raised⟩, loop, rfl⟩ := ok
    have inner := flagValue_foldlM_addFlagReward (based index) loop
    simp only at before inner ⊢
    have moved := flagSum_step (first := first) (perIncrement := perIncrement) (p := current)
      (q := ⟨current.data.set index.toNat flags inside, by
        intro early
        simpa using current.bound early⟩)
      (Array.getElem?_eq_getElem inside) (by simp)
      (fun j apart => by simp [Ne.symm apart]) inner
    omega
  · cases ok

/-- The flag sums of the two recent epochs of a state, over a fixed registry. -/
private def potential (altair : .altair ≤ fork) (first : BeaconState preset fork)
    (perIncrement : Nat) (s : BeaconState preset fork) : Nat :=
  flagSum first perIncrement (s.previousEpochParticipation altair) +
    flagSum first perIncrement (s.currentEpochParticipation altair)

/-- From Altair, an attestation pays its proposer at most the rise of the flag sums over 448.

The state must have the fixed registry, and the total active balance given. -/
private theorem rise_attestation (altair : .altair ≤ fork) {first s t : BeaconState preset fork}
    {total perIncrement : Gwei} (validators : s.validators = first.validators)
    (totalOk : getTotalActiveBalance s = .ok total)
    (perIncrementOk : getBaseRewardPerIncrement preset total = .ok perIncrement)
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (computed : processAttestation config checks s parentSlot attestation = .ok t) :
    potential altair first perIncrement.toNat s ≤ potential altair first perIncrement.toNat t ∧
      Rise ((potential altair first perIncrement.toNat t -
        potential altair first perIncrement.toNat s) / 448) s t := by
  rw [processAttestation_of_altair altair] at computed
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, _, _, _, _, _, _, _, read, readOk,
    attesters, _, ⟨updated, numerator⟩, folded, proposer, _, raised, raisedOk, final⟩ := computed
  rw [totalOk] at readOk
  cases Except.ok.inj readOk
  dsimp only at folded raisedOk
  have flags := flagSum_foldlM_addAttesterFlags
    (fun _ _ ok => baseAt_of_getBaseReward altair validators perIncrementOk ok) folded
  dsimp only at flags
  have raisedFacts := increase_facts raisedOk
  -- Weighing a payment from Gloas changes only the pending payments of builders.
  have tail : t.previousEpochParticipation = raised.previousEpochParticipation ∧
      t.currentEpochParticipation = raised.currentEpochParticipation ∧
      t.slashings = raised.slashings ∧ supply t = supply raised := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases final
      exact ⟨rfl, rfl, rfl, rfl⟩
  -- Raising the balance of the proposer keeps the flags.
  have kept : raised.previousEpochParticipation = (setEpochParticipation s
        (attestation.data.target.epoch == getCurrentEpoch s) updated).previousEpochParticipation ∧
      raised.currentEpochParticipation = (setEpochParticipation s
        (attestation.data.target.epoch == getCurrentEpoch s)
          updated).currentEpochParticipation := by
    obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
    obtain ⟨_, same⟩ := setBalance_ok set
    rw [same]
    exact ⟨rfl, rfl⟩
  have denominator : ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT).toNat = 448 := by decide
  rw [UInt64.toNat_div, denominator] at raisedFacts
  -- Writing the flags keeps the supply and the slashed balances.
  have written : supply (setEpochParticipation s
      (attestation.data.target.epoch == getCurrentEpoch s) updated) = supply s ∧
      (setEpochParticipation s (attestation.data.target.epoch == getCurrentEpoch s)
        updated).slashings = s.slashings := by
    unfold setEpochParticipation
    split <;> exact ⟨rfl, rfl⟩
  have moved : numerator.toNat + potential altair first perIncrement.toNat s ≤
      potential altair first perIncrement.toNat t := by
    unfold potential
    rw [tail.1, tail.2.1, kept.1, kept.2]
    by_cases current : (attestation.data.target.epoch == getCurrentEpoch s) = true
    · simp only [current, ↓reduceIte, UInt64.toNat_zero, Nat.zero_add] at flags
      simp only [setEpochParticipation, current, ↓reduceIte]
      omega
    · simp only [current, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_zero, Nat.zero_add] at flags
      simp only [setEpochParticipation, current, Bool.false_eq_true, ↓reduceIte]
      omega
  refine ⟨by omega, Rise.of_le (tail.2.2.1.trans (raisedFacts.1.trans written.2)) ?_⟩
  rw [tail.2.2.2, raisedFacts.2, written.1]
  have := Nat.div_le_div_right (c := 448) (show numerator.toNat ≤
    potential altair first perIncrement.toNat t -
      potential altair first perIncrement.toNat s by omega)
  omega

/-- The flags of one epoch weigh at most 54 base rewards per increment of the registry. -/
private theorem flagSum_le (first : BeaconState preset fork) (perIncrement : Nat)
    (participation : EpochParticipation preset fork) :
    flagSum first perIncrement participation ≤
      effectiveBalanceSum first / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (perIncrement * 54) := by
  unfold flagSum
  have each := sum_map_le_sum_map (xs := List.range first.validators.data.size)
    (f := fun j => ((participation.data[j]?).map
      (flagValue · (baseAt first perIncrement j))).getD 0)
    (g := fun j => effectiveAt ⟨fork, first⟩ j / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (perIncrement * 54)) fun j _ => by
      cases participation.data[j]? with
      | none => exact Nat.zero_le _
      | some flags =>
        have := flagValue_le flags (baseAt first perIncrement j)
        simp only [Option.map_some, Option.getD_some]
        unfold baseAt at this
        rw [← Nat.mul_assoc]
        exact this
  refine each.trans ?_
  rw [sum_map_mul_right
    (fun j => effectiveAt ⟨fork, first⟩ j / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)]
  refine Nat.mul_le_mul_right _ ?_
  rw [effectiveBalanceSum_eq_sum_range]
  exact sum_map_div_le (fun j => effectiveAt ⟨fork, first⟩ j)
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat _

/-- The flags of both recent epochs weigh at most twice 54 base rewards per increment. -/
private theorem potential_le (altair : .altair ≤ fork) (first : BeaconState preset fork)
    (perIncrement : Nat) (s : BeaconState preset fork) :
    potential altair first perIncrement s ≤
      2 * (effectiveBalanceSum first / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
        perIncrement * 54 := by
  have previous := flagSum_le first perIncrement (s.previousEpochParticipation altair)
  have current := flagSum_le first perIncrement (s.currentEpochParticipation altair)
  have shape : 2 * (effectiveBalanceSum first / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
      perIncrement * 54 =
      effectiveBalanceSum first / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (perIncrement * 54) +
      effectiveBalanceSum first / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (perIncrement * 54) := by
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.two_mul]
  unfold potential
  omega

end Flags

/-! ## The deposits of a block -/

section Amounts

/-- From Gloas, the Gwei of the deposit requests of the parent payload, and zero before. -/
private def parentAmount (body : BeaconBlockBody preset fork) : Nat :=
  if gloas : .glamsterdam ≤ fork then
    ((body.parentExecutionRequests gloas).deposits.data.toList.map (·.amount.toNat)).sum
  else 0

/-- The Gwei of the deposits of a block body, and of its own deposit requests before Gloas. -/
private def ownAmount (body : BeaconBlockBody preset fork) : Nat :=
  (if before : fork < .hegota then
    ((body.deposits before).data.toList.map (·.data.amount.toNat)).sum
  else 0) +
  (if gloas : .glamsterdam ≤ fork then 0
  else if electra : .pectra ≤ fork then
    ((body.executionRequests ⟨electra, Nat.lt_of_not_le gloas⟩).deposits.data.toList.map
      (·.amount.toNat)).sum
  else 0)

/-- The deposits of a block split into those of the parent payload and its own. -/
private theorem blockDepositAmount_eq (body : BeaconBlockBody preset fork) :
    blockDepositAmount body = parentAmount body + ownAmount body := by
  unfold blockDepositAmount parentAmount ownAmount
  by_cases gloas : .glamsterdam ≤ fork
  · simp only [gloas, ↓reduceDIte]
    omega
  · simp only [gloas, ↓reduceDIte]
    omega

end Amounts

/-! ## The block -/

section Block

/-- The steps before the operations bring only the deposit requests of the parent payload. -/
private theorem rise_operationsInput {engine : ExecutionEngine preset fork}
    {state input : BeaconState preset fork} {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input) :
    Rise (parentAmount block.body) state input := by
  obtain ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk, randaoOk,
    eth1Ok⟩ := started
  -- From Gloas the payload of the parent brings its deposit requests.
  have paid : Rise (parentAmount block.body) state parented := by
    unfold parentAmount
    split at paidOk
    · rename_i gloas
      simp only [gloas, ↓reduceDIte]
      exact rise_parentPayload paidOk
    · rename_i gloas
      simp only [gloas, ↓reduceDIte]
      cases paidOk
      exact Rise.refl _
  have executed : Rise 0 headed executed := by
    split at executionOk
    · exact rise_blockExecution executionOk
    · cases executionOk
      exact Rise.refl _
  have voted : Rise 0 revealed input := by
    split at eth1Ok
    · exact (fixed_eth1 eth1Ok).rise
    · cases eth1Ok
      exact Rise.refl _
  have whole := paid.trans <| (fixed_header headerOk).rise.trans <| executed.trans <|
    (fixed_randao randaoOk).rise.trans voted
  simpa using whole

/-- The changes of credentials do not raise the supply. -/
private theorem rise_blsToExecutionChanges {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) : Rise 0 s t := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    exact Rise.foldlM_zero (fun _ _ _ ok => (fixed_blsChange ok).rise) computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Rise.refl _

/-- From Electra to Fulu, the requests of a block raise the supply by at most their deposits. -/
private theorem rise_executionRequests {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {range : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body range = .ok t) :
    Rise (((body.executionRequests range).deposits.data.toList.map (·.amount.toNat)).sum) s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, requestedDeposits, _, withdrawals, consolidations⟩ := computed
  have whole := (Rise.foldlM (amount := fun request : DepositRequest => request.amount.toNat)
    (fun _ _ _ ok => rise_depositRequest ok) requestedDeposits).trans <|
    (Rise.foldlM_zero (fun _ _ _ ok => (fixed_withdrawalRequest ok).rise) withdrawals).trans
      (Rise.foldlM_zero (fun _ _ _ ok => rise_consolidationRequest ok) consolidations)
  simpa using whole

/-- The operations run the slashings, the attestations, then the steps that bring deposits.

The slashings bring only their share of the new slashed balances. -/
private theorem rise_operations {input last : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks input body parentSlot = .ok last) :
    ∃ proposersDone slashingsDone attested,
      body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks) input =
        .ok proposersDone ∧
      body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks)
        proposersDone = .ok slashingsDone ∧
      body.attestations.data.toList.foldlM (processAttestation config checks · parentSlot ·)
        slashingsDone = .ok attested ∧
      Rise 0 input slashingsDone ∧ Rise (ownAmount body) attested last ∧
        Tail attested last := by
  have exitTail {a b : BeaconState preset fork} {signed : SignedVoluntaryExit}
      (ok : processVoluntaryExit config checks a signed = .ok b) : Tail a b :=
    Tail.of_flags (frame_processVoluntaryExit ok).registryGrows (effectiveKept_voluntaryExit ok)
      (fixed_voluntaryExit ok).flags
  have changeTail {a b : BeaconState preset fork} {signed : SignedBLSToExecutionChange}
      (ok : processBlsToExecutionChange config checks a signed = .ok b) : Tail a b :=
    Tail.of_flags (frame_processBlsToExecutionChange ok).registryGrows
      (effectiveKept_blsChange ok) (fixed_blsChange ok).flags
  have slashings {a proposersDone slashingsDone : BeaconState preset fork}
      (proposersOk : body.proposerSlashings.data.toList.foldlM
        (processProposerSlashing config checks) a = .ok proposersDone)
      (attestersOk : body.attesterSlashings.data.toList.foldlM
        (processAttesterSlashing config checks) proposersDone = .ok slashingsDone) :
      Rise 0 a slashingsDone :=
    (Rise.foldlM_zero (fun _ _ _ ok => rise_proposerSlashing ok) proposersOk).trans
      (Rise.foldlM_zero (fun _ _ _ ok => rise_attesterSlashing ok) attestersOk)
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    refine ⟨_, _, _, proposersOk, attestersOk, attestedOk, slashings proposersOk attestersOk, ?_⟩
    have whole :=
      (Rise.foldlM_zero (fun _ _ _ ok => (fixed_voluntaryExit ok).rise) exitsOk).trans <|
      (Rise.foldlM_zero (fun _ _ _ ok => (fixed_blsChange ok).rise) changesOk).trans
        (Rise.foldlM_zero (fun _ _ _ ok => (fixed_payloadAttestation ok).rise) paid)
    refine ⟨whole.mono (Nat.zero_le _), ?_⟩
    exact (Tail.foldlM (fun _ _ _ ok => exitTail ok) exitsOk).trans <|
      (Tail.foldlM (fun _ _ _ ok => changeTail ok) changesOk).trans
        (Tail.foldlM (fun _ _ _ ok => by rw [processPayloadAttestation_eq ok]; exact Tail.refl _)
          paid)
  rename_i gloas
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  refine ⟨_, _, _, proposersOk, attestersOk, attestedOk, slashings proposersOk attestersOk, ?_⟩
  have deposits := Rise.foldlM (amount := fun deposit : Deposit => deposit.data.amount.toNat)
    (fun _ _ _ ok => rise_deposit ok) depositedOk
  have exits := Rise.foldlM_zero (fun _ _ _ ok => (fixed_voluntaryExit ok).rise) exitsOk
  -- From Capella the changes of credentials run, and from Electra the requests.
  have changes := rise_blsToExecutionChanges changesOk
  have requested : Rise (if electra : .pectra ≤ fork then
      ((body.executionRequests ⟨electra, Nat.lt_of_not_le gloas⟩).deposits.data.toList.map
        (·.amount.toNat)).sum else 0) changed last := by
    split at requestsOk
    · rename_i electra
      simp only [electra, ↓reduceDIte]
      exact rise_executionRequests requestsOk
    · rename_i electra
      simp only [electra, ↓reduceDIte]
      simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ Rise.refl _
  have whole := deposits.trans <| exits.trans <| changes.trans requested
  refine ⟨whole.mono (Nat.le_of_eq ?_), ?_⟩
  · have early : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le gloas) (by decide)
    unfold ownAmount
    simp only [early, gloas, ↓reduceDIte, Nat.zero_add]
  -- The deposits add validators at the end, and the other steps keep the registry.
  have depositsTail := Tail.foldlM (fun _ _ _ ok => ⟨(frame_processDeposit ok).registryGrows,
    effectiveKept_processDeposit ok, flagsBelow_deposit ok⟩) depositedOk
  have changesTail : Tail exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact Tail.foldlM (fun _ _ _ ok => changeTail ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ Tail.refl _
  have requestsTail : Tail changed last := by
    split at requestsOk
    · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requestsOk
      obtain ⟨_, requestedDeposits, _, withdrawals, consolidations⟩ := requestsOk
      refine (Tail.foldlM (fun _ _ _ ok => Tail.of_flags
        (Nat.le_of_eq (by rw [(processDepositRequest_ok ok).2.1]))
        (effectiveKept_depositRequest ok) (flags_depositRequest ok)) requestedDeposits).trans <|
        (Tail.foldlM (fun _ _ _ ok => Tail.of_flags
          (Nat.le_of_eq (sameSizes_processWithdrawalRequest ok).1.symm)
          (effectiveKept_withdrawalRequest ok) (fixed_withdrawalRequest ok).flags)
          withdrawals).trans
        (Tail.foldlM (fun _ _ _ ok => Tail.of_flags
          (Nat.le_of_eq (sameSizes_processConsolidationRequest ok).1.symm)
          (effectiveKept_consolidationRequest ok) (flags_consolidationRequest ok))
          consolidations)
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ Tail.refl _
  exact depositsTail.trans <| (Tail.foldlM (fun _ _ _ ok => exitTail ok) exitsOk).trans <|
    changesTail.trans requestsTail

/-- Along the attestations, the registry and the slot stay, and the flag sums only grow.

The supply rises by at most the rise of the flag sums over 448. -/
private def VotesKept (altair : .altair ≤ fork) (first : BeaconState preset fork)
    (perIncrement : Nat) (b : BeaconState preset fork) : Prop :=
  b.validators = first.validators ∧ b.slot = first.slot ∧
    potential altair first perIncrement first ≤ potential altair first perIncrement b ∧
    Rise ((potential altair first perIncrement b - potential altair first perIncrement first) /
      448) first b

/-- Before Altair, the attestations only record themselves. -/
private theorem rise_attestations_of_lt (before : fork < .altair)
    {first attested : BeaconState preset fork}
    {parentSlot : Slot} {attestations : List (Attestation preset fork)}
    (attestedOk :
      attestations.foldlM (processAttestation config checks · parentSlot ·) first = .ok attested) :
    Rise 0 first attested := by
  refine Rise.foldlM_zero (fun a attestation b ok => Fixed.rise ?_) attestedOk
  obtain ⟨_, _, _, _, _, recorded, _⟩ := processAttestation_records before ok
  have kept := recordPendingAttestation_ok recorded
  split at kept
  all_goals
    obtain ⟨_, rest⟩ := kept
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [← rest]

/-- From Altair, the attestations keep the registry and do not lower the flag sums.

They raise the supply by at most the rise of the flag sums, over 448.

The flag sums read the base reward at the total active balance where the attestations start. -/
private theorem rise_attestations (altair : .altair ≤ fork)
    {first attested : BeaconState preset fork}
    {total perIncrement : Gwei} (totalOk : getTotalActiveBalance first = .ok total)
    (perIncrementOk : getBaseRewardPerIncrement preset total = .ok perIncrement)
    {parentSlot : Slot} {attestations : List (Attestation preset fork)}
    (attestedOk :
      attestations.foldlM (processAttestation config checks · parentSlot ·) first = .ok attested) :
    attested.validators = first.validators ∧
      potential altair first perIncrement.toNat first ≤
        potential altair first perIncrement.toNat attested ∧
      Rise ((potential altair first perIncrement.toNat attested -
        potential altair first perIncrement.toNat first) / 448) first attested := by
  -- Along the attestations, the registry and the slot stay, and the flag sums only grow.
  have step : ∀ (b : BeaconState preset fork) (attestation : Attestation preset fork) c,
      VotesKept altair first perIncrement.toNat b →
      processAttestation config checks b parentSlot attestation = .ok c →
      VotesKept altair first perIncrement.toNat c := by
    intro b attestation c ⟨validators, slot, low, rise⟩ ok
    have totalAt : getTotalActiveBalance b = .ok total :=
      (Steady.of_validators validators slot).total.trans totalOk
    obtain ⟨up, stepRise⟩ := rise_attestation altair validators totalAt perIncrementOk ok
    refine ⟨(processAttestation_registry ok).1.trans validators,
      (frame_processAttestation ok).slot.trans slot, Nat.le_trans low up,
      (rise.trans stepRise).mono ?_⟩
    generalize potential altair first perIncrement.toNat first = x at low up ⊢
    generalize potential altair first perIncrement.toNat b = y at low up ⊢
    generalize potential altair first perIncrement.toNat c = z at low up ⊢
    have floors := Nat.div_add_div_le_add_div (x := y - x) (y := z - y) (z := 448)
    have sum : y - x + (z - y) = z - x := by omega
    rw [sum] at floors
    exact floors
  obtain ⟨validators, -, grown, rise⟩ := foldlM_ok_invariant _ step
    ⟨rfl, rfl, Nat.le_refl _, by simpa using Rise.refl first⟩ attestedOk
  exact ⟨validators, grown, rise⟩

/-- The reward of a sync committee member that signs, at a total and a base reward per increment.
-/
private def participantReward (preset : Preset) (total perIncrement : Gwei) : Nat :=
  total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
      preset.SYNC_COMMITTEE_SIZE.toNat

/-- The sync aggregate pays each seat at most the participant reward and the proposer share. -/
private theorem rise_syncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    {last after : BeaconState preset fork}
    (computed : processSyncAggregate config checks last altair aggregate = .ok after) :
    ∃ total perIncrement, getTotalActiveBalance last = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement ∧
      Rise (preset.SYNC_COMMITTEE_SIZE.toNat * (participantReward preset total perIncrement +
        participantReward preset total perIncrement * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))) last after := by
  unfold processSyncAggregate at computed
  simp only [syncProposerReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposerReward, proposerRewardOk,
    members, membersOk, folded⟩ := computed
  obtain ⟨scaled, scaledOk, proposerRewardOk⟩ := proposerRewardOk
  rw [Uint64.mulChecked_ok_iff] at scaledOk
  rw [Uint64.divChecked_ok_iff] at proposerRewardOk
  obtain ⟨total, perIncrement, totalOk, perIncrementOk, -, rewardValue⟩ :=
    syncParticipantReward_ok rewardOk
  refine ⟨total, perIncrement, totalOk, perIncrementOk, ?_⟩
  rw [← Array.foldlM_toList] at folded
  -- Each member pays at most the reward to itself and the share to the proposer.
  have each : ∀ (a : BeaconState preset fork) member b, applySyncReward reward proposerReward
      (getBeaconProposerIndex last) a member = .ok b →
        Rise (reward.toNat + proposerReward.toNat) a b := by
    intro a member b ok
    unfold applySyncReward at ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨raised, raisedOk, _, _, paid⟩ := ok
      have one := increase_facts raisedOk
      have two := increase_facts paid
      exact Rise.of_le (two.1.trans one.1) (by omega)
    · have low := decrease_facts (liftAccessor_ok.mp ok)
      exact Rise.of_le low.1 (by omega)
  have whole := Rise.foldlM (amount := fun _ => reward.toNat + proposerReward.toNat) each folded
  refine whole.mono ?_
  -- The members are the keys of the committee, one for each of its seats.
  have onList : (last.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
      (validatorIndexOfPubkey last) = .ok members.toList := by
    rw [← Array.toList_mapM, membersOk]
    rfl
  have length := mapM_ok_length onList
  have seats : (members.zip aggregate.syncCommitteeBits.bits.toArray).toList.length ≤
      preset.SYNC_COMMITTEE_SIZE.toNat := by
    simp only [Array.toList_zip, List.length_zip, Array.length_toList] at length ⊢
    simp only [Vector.size_toArray] at length
    omega
  have shares : reward.toNat + proposerReward.toNat = participantReward preset total perIncrement +
      participantReward preset total perIncrement * PROPOSER_WEIGHT.toNat /
        (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) := by
    have participant : reward.toNat = participantReward preset total perIncrement := by
      rw [rewardValue, participantReward, Nat.mul_comm perIncrement.toNat]
    rw [proposerRewardOk.2, scaledOk.2, participant]
    rfl
  simp only [List.map_const', List.sum_replicate, shares]
  exact Nat.mul_le_mul_right _ seats

/-- Where the attestations start, the registry is steady since the state before the block.

The participation flags are those before the block too. -/
private theorem attestationsStart_same {engine : ExecutionEngine preset fork}
    {state input proposersDone first : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input)
    (proposers : block.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) input = .ok proposersDone)
    (slashings : block.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposersDone = .ok first) :
    Steady state first ∧ Flags state first := by
  have paid {a b : BeaconState preset fork} (gloas : .glamsterdam ≤ fork)
      (ok : processParentExecutionPayload config checks a gloas block.body = .ok b) :
      Steady a b :=
    processParentExecutionPayload_step_of Steady Steady.refl Steady.trans
      (fun frame validators => Steady.of_validators validators frame.slot)
      (fun requested => ⟨activeStep_processWithdrawalRequest requested,
        effectiveKept_withdrawalRequest requested,
        (sameSizes_processWithdrawalRequest requested).1⟩)
      (fun requested => ⟨activeStep_processConsolidationRequest requested,
        effectiveKept_consolidationRequest requested,
        (sameSizes_processConsolidationRequest requested).1⟩) ok
  have head := started.step_of Steady Steady.refl Steady.trans paid
    (fun headed => by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
      exact Steady.of_validators rfl rfl)
    (fun _ executed => Steady.of_validators (processBlockExecution_validators executed)
      (frame_processBlockExecution executed).slot)
    (fun revealed => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
      exact Steady.of_validators rfl rfl)
    (fun _ voted => by
      obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
      exact Steady.of_validators (by rw [← rest]) (by rw [← rest]))
  have proposed := (foldlM_ok_steps Steady Steady.refl Steady.trans (fun _ _ _ ok =>
    ⟨activeStep_processProposerSlashing ok, effectiveKept_proposerSlashing ok,
      (sameSizes_processProposerSlashing ok).1⟩) proposers).1
  have slashed := (foldlM_ok_steps Steady Steady.refl Steady.trans (fun _ _ _ ok =>
    ⟨activeStep_processAttesterSlashing ok, effectiveKept_attesterSlashing ok,
      (sameSizes_processAttesterSlashing ok).1⟩) slashings).1
  refine ⟨head.trans (proposed.trans slashed), ?_⟩
  exact (flags_operationsInput started).trans <|
    (Flags.foldlM (fun _ _ _ ok => flags_proposerSlashing ok) proposers).trans
      (Flags.foldlM (fun _ _ _ ok => flags_attesterSlashing ok) slashings)

/-- Before the sync aggregate, the active balance is that of the state before the block. -/
private theorem syncStart_same {engine : ExecutionEngine preset fork}
    {state last after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (altair : .altair ≤ fork)
    (synced : processSyncAggregate config checks last altair (block.body.syncAggregate altair) =
      .ok after) :
    getTotalActiveBalance last = getTotalActiveBalance state := by
  have whole := total_congr ⟨(frame_processBlock computed).slot, activeKept_processBlock computed⟩
    (effectiveKept_processBlock computed) (frame_processBlock computed).registryGrows
  obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
  exact whole

end Block

/-! ## The weight of the participation flags -/

section Weight

/-- From Altair, the weight of the flags is the flag sums of both epochs over the own registry. -/
private theorem flagRewardWeight_eq (altair : .altair ≤ fork) (perIncrement : Nat)
    (s : BeaconState preset fork) :
    flagRewardWeight preset perIncrement s = potential altair s perIncrement s := by
  simp only [flagRewardWeight, altair, ↓reduceDIte]
  rfl

/-- Two registries of one size and the same effective balances give the same flag sums. -/
private theorem flagSum_congr {a b : BeaconState preset fork} (size :
    b.validators.data.size = a.validators.data.size) (kept : EffectiveKept a b)
    (perIncrement : Nat) (participation : EpochParticipation preset fork) :
    flagSum b perIncrement participation = flagSum a perIncrement participation := by
  unfold flagSum
  rw [size]
  refine congrArg List.sum (List.map_congr_left fun j member => ?_)
  simp only [baseAt, kept j (List.mem_range.mp member)]

/-- A sum over the first positions is at most the sum over more positions. -/
private theorem sum_range_le_of_le (f : Nat → Nat) {small : Nat} :
    ∀ {large : Nat}, small ≤ large →
      ((List.range small).map f).sum ≤ ((List.range large).map f).sum
  | 0, le => by rw [Nat.le_zero.mp le]
  | large + 1, le => by
    rcases Nat.lt_or_eq_of_le le with lt | rfl
    · have := sum_range_le_of_le f (small := small) (large := large) (by omega)
      simp only [List.range_succ, List.map_append, List.sum_append]
      omega
    · exact Nat.le_refl _

/-- A step of the tail of a block does not lower the flag sums over its own registry. -/
private theorem potential_le_of_tail (altair : .altair ≤ fork) (perIncrement : Nat)
    {a b : BeaconState preset fork} (tail : Tail a b) :
    potential altair a perIncrement a ≤ potential altair b perIncrement b := by
  have one (select : BeaconState preset fork → EpochParticipation preset fork)
      (same : ∀ j, j < a.validators.data.size → (select b).data[j]? = (select a).data[j]?) :
      flagSum a perIncrement (select a) ≤ flagSum b perIncrement (select b) := by
    unfold flagSum
    refine Nat.le_trans (Nat.le_of_eq (congrArg List.sum (List.map_congr_left
      fun j member => ?_))) (sum_range_le_of_le _ tail.1)
    have inside := List.mem_range.mp member
    simp only [baseAt, same j inside, tail.2.1 j inside]
  unfold potential
  have previous := one (fun s => s.previousEpochParticipation altair)
    fun j inside => (tail.2.2 altair j inside).1
  have current := one (fun s => s.currentEpochParticipation altair)
    fun j inside => (tail.2.2 altair j inside).2
  omega

end Weight

/-- The weight of the flags is at most twice 54 base rewards per increment of the registry. -/
theorem flagRewardWeight_le (perIncrement : Nat) (state : BeaconState preset fork) :
    flagRewardWeight preset perIncrement state ≤
      2 * (effectiveBalanceSum state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
        perIncrement * 54 := by
  by_cases altair : .altair ≤ fork
  · rw [flagRewardWeight_eq altair]
    exact potential_le altair state perIncrement state
  · simp [flagRewardWeight, altair]

/-- A block raises the supply by its deposits, a share of the slashed balances and its rewards.

The rewards of the attestations are below the rise of the weight of the flags over 448.

The weight reads the base reward of one increment of the state before the block.

The weight does not fall in the block.

The rewards are also below twice 54 base rewards per increment of the registry, over 448. -/
private theorem processBlock_rise {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ low high, flagRewardWeight preset (blockPerIncrement preset state) state ≤ low ∧
      low ≤ high ∧ high ≤ flagRewardWeight preset (blockPerIncrement preset state) after ∧
      high ≤ 2 * (effectiveBalanceSum state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
        blockPerIncrement preset state * 54 ∧
      Rise (blockDepositAmount block.body + (high - low) / 448 + syncRewardCap preset state)
        state after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  obtain ⟨proposersDone, first, attested, proposersOk, slashingsOk, attestedOk, slashed, tail,
    tailKept⟩ := rise_operations operated
  have head := rise_operationsInput started
  rw [blockDepositAmount_eq]
  by_cases altair : .altair ≤ fork
  · simp only [altair, ↓reduceDIte] at synced
    obtain ⟨total, perIncrement, totalOk, perIncrementOk, syncRise⟩ := rise_syncAggregate synced
    have totalState := (syncStart_same computed altair synced).symm.trans totalOk
    have reads : blockPerIncrement preset state = perIncrement.toNat := by
      simp only [blockPerIncrement, altair, ↓reduceIte, totalState, perIncrementOk]
    have sync : syncRewardCap preset state = preset.SYNC_COMMITTEE_SIZE.toNat *
        (participantReward preset total perIncrement +
          participantReward preset total perIncrement * PROPOSER_WEIGHT.toNat /
            (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := by
      simp only [syncRewardCap, altair, ↓reduceIte, totalState, perIncrementOk,
        participantReward]
    obtain ⟨steady, flags⟩ := attestationsStart_same started proposersOk slashingsOk
    obtain ⟨validators, grown, votes⟩ := rise_attestations altair
      (steady.total.trans totalState) perIncrementOk attestedOk
    rw [reads, sync]
    refine ⟨potential altair first perIncrement.toNat first,
      potential altair first perIncrement.toNat attested, ?_, grown, ?_, ?_, ?_⟩
    · -- The flags and the registry are those of the state before the block.
      rw [flagRewardWeight_eq altair]
      unfold potential
      rw [flagSum_congr steady.2.2 steady.2.1, flagSum_congr steady.2.2 steady.2.1, flags.1,
        flags.2]
    · -- The tail of the block keeps the flags of the registry at the attestations.
      have sameSize : attested.validators.data.size = first.validators.data.size := by
        rw [validators]
      have sameKept : EffectiveKept first attested :=
        effectiveKept_data (congrArg (·.data) validators)
      have ends : Tail last after := by
        obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
        exact ⟨Nat.le_refl _, effectiveKept_data rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
      rw [flagRewardWeight_eq altair]
      have later := potential_le_of_tail altair perIncrement.toNat (tailKept.trans ends)
      unfold potential at later ⊢
      rw [← flagSum_congr sameSize sameKept, ← flagSum_congr sameSize sameKept]
      exact later
    · rw [← steady.effectiveBalanceSum_eq]
      exact potential_le altair first perIncrement.toNat attested
    · have whole := head.trans (slashed.trans ((votes.trans tail).trans syncRise))
      refine whole.mono (Nat.le_of_eq ?_)
      omega
  · simp only [altair, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at synced
    subst synced
    have votes := rise_attestations_of_lt (Nat.lt_of_not_le altair) attestedOk
    refine ⟨0, 0, ?_, Nat.le_refl _, ?_, Nat.zero_le _, ?_⟩
    · simp [flagRewardWeight, altair]
    · exact Nat.zero_le _
    · have whole := head.trans (slashed.trans (votes.trans tail))
      refine whole.mono (Nat.le_of_eq ?_)
      simp [syncRewardCap, altair]

/-- A block raises the balances plus the pending deposits by a bounded amount.

The bound is the Gwei of its deposits and deposit requests.

It adds the rise of the slashed balances over the whistleblower quotient.

A slashing pays at most the whistleblower reward beyond the penalty it takes first.

The slashed balances count the effective balance of each validator slashed in the block.

From Altair, the attestations pay at most the rise of the weight of the flags, over 448.

That weight reads the base reward of one increment of the state before the block.

The sync aggregate pays at most its own bound. -/
theorem processBlock_supply_le {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    balanceSum after + pendingDepositSum after ≤
      balanceSum state + pendingDepositSum state + blockDepositAmount block.body +
        (slashedBalanceSum after - slashedBalanceSum state) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (flagRewardWeight preset (blockPerIncrement preset state) after -
          flagRewardWeight preset (blockPerIncrement preset state) state) / 448 +
        syncRewardCap preset state := by
  obtain ⟨low, high, lowLe, -, highLe, -, rise⟩ := processBlock_rise computed
  have share := Nat.div_le_div_right (c := 448) (show high - low ≤
    flagRewardWeight preset (blockPerIncrement preset state) after -
      flagRewardWeight preset (blockPerIncrement preset state) state by omega)
  have bound := rise.2
  unfold supply quotient at bound
  omega

/-- A block raises the balances plus the pending deposits by at most a cap.

The cap is the Gwei of its deposits and deposit requests, and a bound on its rewards.

It adds the rise of the slashed balances over the whistleblower quotient. -/
theorem processBlock_supply_le_cap {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    balanceSum after + pendingDepositSum after ≤
      balanceSum state + pendingDepositSum state + blockDepositAmount block.body +
        (slashedBalanceSum after - slashedBalanceSum state) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        blockRewardCap preset state := by
  obtain ⟨low, high, -, -, -, highCap, rise⟩ := processBlock_rise computed
  have share := Nat.div_le_div_right (c := 448) (Nat.le_trans (Nat.sub_le high low) highCap)
  have bound := rise.2
  unfold supply quotient at bound
  unfold blockRewardCap
  omega

/-- A block does not lower the weight of the flags, at the base reward of the state before it. -/
theorem processBlock_flagRewardWeight_le {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    flagRewardWeight preset (blockPerIncrement preset state) state ≤
      flagRewardWeight preset (blockPerIncrement preset state) after := by
  obtain ⟨low, high, lowLe, lowHigh, highLe, -, -⟩ := processBlock_rise computed
  omega

/-- A block keeps the total active balance, with its errors.

It keeps the slot, the activity in the current epoch and the earlier effective balances. -/
theorem processBlock_getTotalActiveBalance {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    getTotalActiveBalance after = getTotalActiveBalance state :=
  total_congr ⟨(frame_processBlock computed).slot, activeKept_processBlock computed⟩
    (effectiveKept_processBlock computed) (frame_processBlock computed).registryGrows

/-- A block keeps the base reward of one increment. -/
theorem processBlock_blockPerIncrement {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    blockPerIncrement preset after = blockPerIncrement preset state := by
  simp only [blockPerIncrement, processBlock_getTotalActiveBalance computed]

/-- A withdrawal request keeps the balances. -/
theorem processWithdrawalRequest_balances {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config s electra request = .ok t) :
    t.balances = s.balances :=
  (fixed_withdrawalRequest computed).1

/-- Before Heze, the operations of a block take its input to the state where its requests start.

They run the slashings, the attestations, the deposits, the exits and the credential changes.

The requests of the block run there from Electra to Fulu only.

From Gloas they run with the parent payload instead, before the operations. -/
def RequestsStart (config : Config) (checks : SignatureChecks) (body : BeaconBlockBody preset fork)
    (parentSlot : Slot) (before : fork < .hegota) (input changed : BeaconState preset fork) :
    Prop :=
  ∃ proposersDone slashingsDone attested deposited exited : BeaconState preset fork,
    body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks) input =
      .ok proposersDone ∧
    body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks)
      proposersDone = .ok slashingsDone ∧
    body.attestations.data.toList.foldlM (processAttestation config checks · parentSlot ·)
      slashingsDone = .ok attested ∧
    (body.deposits before).data.toList.foldlM (processDeposit config checks before) attested =
      .ok deposited ∧
    body.voluntaryExits.data.toList.foldlM (processVoluntaryExit config checks) deposited =
      .ok exited ∧
    processBlsToExecutionChanges config checks exited body = .ok changed

/-- From Electra to Fulu, the operations of a block reach the start of its requests and run them. -/
theorem processOperations_requestsStart {input last : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (electra : .pectra ≤ fork) (gloas : ¬ .glamsterdam ≤ fork)
    (computed : processOperations config checks input body parentSlot = .ok last) :
    ∃ changed, RequestsStart config checks body parentSlot
        (Nat.lt_trans (Nat.lt_of_not_le gloas) (by decide)) input changed ∧
      processExecutionRequests config changed body ⟨electra, Nat.lt_of_not_le gloas⟩ =
        .ok last := by
  unfold processOperations at computed
  simp only [gloas, electra, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList]
    at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, _,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  exact ⟨changed, ⟨_, _, _, _, _, proposersOk, attestersOk, attestedOk, depositedOk, exitsOk,
    changesOk⟩, requestsOk⟩

/-- The steps before the operations of a block reach one input. -/
private theorem operationsInput_unique {engine : ExecutionEngine preset fork}
    {state one two : BeaconState preset fork} {block : BeaconBlock preset fork}
    (first : OperationsInput config checks engine state block one)
    (second : OperationsInput config checks engine state block two) : one = two := by
  obtain ⟨_, _, _, _, paid, headed, executed, revealed, voted⟩ := first
  obtain ⟨_, _, _, _, paid', headed', executed', revealed', voted'⟩ := second
  cases paid.symm.trans paid'
  cases headed.symm.trans headed'
  cases executed.symm.trans executed'
  cases revealed.symm.trans revealed'
  cases voted.symm.trans voted'
  rfl

/-- The operations of a block reach one start of its requests. -/
private theorem requestsStart_unique {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    {before : fork < .hegota} {input one two : BeaconState preset fork}
    (first : RequestsStart config checks body parentSlot before input one)
    (second : RequestsStart config checks body parentSlot before input two) : one = two := by
  obtain ⟨_, _, _, _, _, proposers, attesters, attested, deposited, exited, changed⟩ := first
  obtain ⟨_, _, _, _, _, proposers', attesters', attested', deposited', exited', changed'⟩ :=
    second
  cases proposers.symm.trans proposers'
  cases attesters.symm.trans attesters'
  cases attested.symm.trans attested'
  cases deposited.symm.trans deposited'
  cases exited.symm.trans exited'
  cases changed.symm.trans changed'
  rfl

/-- The slashed balances where the requests start are at most those after the operations. -/
private theorem slashed_requestsStart {input last changed : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} {before : fork < .hegota}
    (computed : processOperations config checks input body parentSlot = .ok last)
    (reached : RequestsStart config checks body parentSlot before input changed) :
    slashedBalanceSum changed ≤ slashedBalanceSum last := by
  by_cases gloas : .glamsterdam ≤ fork
  · obtain ⟨_, _, _, _, _, proposersOk, attestersOk, attestedOk, depositedOk, exitsOk,
      changesOk⟩ := reached
    unfold processOperations processOperationsGloas at computed
    simp only [gloas, before, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList]
      at computed
    obtain ⟨_, empty, _, _, _, _, _, _, _, _, _, _, _, _, _, proposers, _, attesters, _, attested,
      _, exits, _, changes, paid⟩ := computed
    -- From Gloas the block holds no deposit, so the requests start after the changes.
    rw [Array.toList_eq_nil_iff.mpr (Array.size_eq_zero_iff.mp empty)] at depositedOk
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at depositedOk
    subst depositedOk
    unfold processBlsToExecutionChanges at changesOk
    have capella : .shapella ≤ fork := Nat.le_trans (by decide) gloas
    simp only [capella, ↓reduceDIte, ← Array.foldlM_toList] at changesOk
    cases proposers.symm.trans proposersOk
    cases attesters.symm.trans attestersOk
    cases attested.symm.trans attestedOk
    cases exits.symm.trans exitsOk
    cases changes.symm.trans changesOk
    exact (Rise.foldlM_zero (fun _ _ _ ok => (fixed_payloadAttestation ok).rise) paid).1
  by_cases electra : .pectra ≤ fork
  · obtain ⟨_, reached', requested⟩ := processOperations_requestsStart electra gloas computed
    cases requestsStart_unique reached' reached
    exact (rise_executionRequests requested).1
  unfold processOperations at computed
  simp only [gloas, electra, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, _,
    exitsOk, _, changesOk, rfl⟩ := computed
  cases requestsStart_unique ⟨_, _, _, _, _, proposersOk, attestersOk, attestedOk, depositedOk,
    exitsOk, changesOk⟩ reached
  exact Nat.le_refl _

/-- Before Heze, the supply where the requests of a block start is within the cap of the block.

It is the cap that bounds the supply after the whole block. -/
theorem processBlock_supply_le_cap_of_requestsStart {engine : ExecutionEngine preset fork}
    {state after input changed : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (started : OperationsInput config checks engine state block input)
    {before : fork < .hegota}
    (reached : RequestsStart config checks block.body state.latestBlockHeader.slot before input
      changed) :
    balanceSum changed + pendingDepositSum changed ≤
      balanceSum state + pendingDepositSum state + blockDepositAmount block.body +
        (slashedBalanceSum after - slashedBalanceSum state) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        blockRewardCap preset state := by
  obtain ⟨input', last, started', operated, -, synced⟩ := processBlock_operationsInput computed
  cases operationsInput_unique started' started
  obtain ⟨proposersDone, first, attested, proposersOk, slashingsOk, attestedOk, slashed, -,
    -⟩ := rise_operations operated
  have changedLe := slashed_requestsStart operated reached
  obtain ⟨proposersDone', first', attested', deposited, exited, proposersOk', slashingsOk',
    attestedOk', depositedOk, exitsOk, changesOk⟩ := reached
  cases proposersOk.symm.trans proposersOk'
  cases slashingsOk.symm.trans slashingsOk'
  cases attestedOk.symm.trans attestedOk'
  have head := rise_operationsInput started
  have deposits := Rise.foldlM (amount := fun deposit : Deposit => deposit.data.amount.toNat)
    (fun _ _ _ ok => rise_deposit ok) depositedOk
  have exits := Rise.foldlM_zero (fun _ _ _ ok => (fixed_voluntaryExit ok).rise) exitsOk
  have changes := rise_blsToExecutionChanges changesOk
  -- The attestations pay at most the cap on the flags, and the slashed balances grow after.
  obtain ⟨votes, ends⟩ : Rise (2 * (effectiveBalanceSum state /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * blockPerIncrement preset state * 54 / 448)
      first attested ∧ slashedBalanceSum last ≤ slashedBalanceSum after := by
    by_cases altair : .altair ≤ fork
    · simp only [altair, ↓reduceDIte] at synced
      obtain ⟨total, perIncrement, totalOk, perIncrementOk, syncRise⟩ := rise_syncAggregate synced
      have totalState := (syncStart_same computed altair synced).symm.trans totalOk
      have reads : blockPerIncrement preset state = perIncrement.toNat := by
        simp only [blockPerIncrement, altair, ↓reduceIte, totalState, perIncrementOk]
      obtain ⟨steady, -⟩ := attestationsStart_same started proposersOk slashingsOk
      obtain ⟨-, -, votes⟩ := rise_attestations altair
        (steady.total.trans totalState) perIncrementOk attestedOk
      refine ⟨votes.mono ?_, syncRise.1⟩
      rw [reads, ← steady.effectiveBalanceSum_eq]
      exact Nat.div_le_div_right
        (Nat.le_trans (Nat.sub_le _ _) (potential_le altair first perIncrement.toNat attested))
    · simp only [altair, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at synced
      subst synced
      exact ⟨(rise_attestations_of_lt (Nat.lt_of_not_le altair) attestedOk).mono
        (Nat.zero_le _), Nat.le_refl _⟩
  have whole := head.trans (slashed.trans (votes.trans (deposits.trans (exits.trans changes))))
  have bound := whole.2
  have amount : parentAmount block.body +
      ((block.body.deposits before).data.toList.map (·.data.amount.toNat)).sum ≤
        blockDepositAmount block.body := by
    rw [blockDepositAmount_eq]
    unfold ownAmount
    simp only [before, ↓reduceDIte]
    omega
  have share := Nat.div_le_div_right (c := quotient preset fork)
    (Nat.sub_le_sub_right (Nat.le_trans changedLe ends) (slashedBalanceSum state))
  unfold supply quotient at bound share
  unfold blockRewardCap
  omega

end EthLib.Consensus
