module

public import EthLib.Consensus.Proofs.Transition.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.EpochJustification
public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.StateTransition
public import EthLib.Consensus.Proofs.Transition.Totality.Bound

/-!
# Proofs: a slot never raises the validators plus the pending deposits

The proofs that the steps of an epoch succeed assume a registry within its limit.

From Electra an epoch adds validators, one for each pending deposit with a new key that it applies.

So the size of the registry alone can grow from one slot to the next.

The validators plus the pending deposits cannot, as each case of a pending deposit shows.

A deposit that adds a validator leaves the queue, so the count stays the same.

A top-up leaves the queue and adds no validator, so the count falls by one.

A postponed deposit leaves the queue and enters it again at its end.

No other step of a slot adds a validator or a pending deposit.

So a slot never raises the count, at every fork.

The upgrades between forks have their own statements.

The blocks have their own statements.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- A step that keeps the size of the registry and the queue of pending deposits. -/
def LoadKept (state after : BeaconState preset fork) : Prop :=
  after.validators.data.size = state.validators.data.size ∧
    after.pendingDeposits = state.pendingDeposits

/-- Each state keeps its registry size and its queue. -/
theorem LoadKept.refl (state : BeaconState preset fork) : LoadKept state state :=
  ⟨rfl, rfl⟩

/-- Two steps that keep the count chain. -/
theorem LoadKept.trans {first second third : BeaconState preset fork}
    (one : LoadKept first second) (two : LoadKept second third) : LoadKept first third :=
  ⟨two.1.trans one.1, two.2.trans one.2⟩

/-- A step that leaves the registry and the queue unchanged keeps both sizes. -/
theorem LoadKept.of_validators
    (validators : after.validators = state.validators := by rfl)
    (pending : after.pendingDeposits = state.pendingDeposits := by rfl) : LoadKept state after :=
  ⟨by rw [validators], pending⟩

/-- A step that keeps both sizes leaves the validators plus the pending deposits unchanged. -/
theorem LoadKept.registryLoad_eq (same : LoadKept state after) :
    registryLoad after = registryLoad state := by
  unfold registryLoad
  rw [same.1, same.2]

/-- A fold whose every step keeps the count keeps it. -/
theorem LoadKept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (same : ∀ s x s', step s x = .ok s' → LoadKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : LoadKept state after :=
  foldlM_ok_invariant (LoadKept state) (fun _ _ _ before ok => before.trans (same _ _ _ ok))
    (LoadKept.refl state) computed

/-- The steps of an epoch other than the pending deposits keep the registry size and the queue.

Writes to a balance or to a validator, and the start of an exit, keep them too. -/
theorem loadKeptLaws : EpochStepLaws (@LoadKept preset fork) where
  refl := LoadKept.refl
  trans := LoadKept.trans
  setValidatorAt set _ _ _ _ _ := by
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
    exact ⟨(sameSizes_putValidator _ inside _).1, rfl⟩
  increaseBalance computed := by
    obtain ⟨_, set⟩ := increaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact ⟨rfl, rfl⟩
  decreaseBalance computed := by
    obtain ⟨_, set⟩ := decreaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact ⟨rfl, rfl⟩
  initiateValidatorExit computed := by
    obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
      initiateValidatorExit_ok computed
    · exact ⟨rfl, rfl⟩
    · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
      obtain ⟨inside, rfl⟩ := setValidator_ok set
      exact ⟨(sameSizes_putValidator _ inside _).1, rfl⟩
  eth1DataVotes _ _ := ⟨rfl, rfl⟩
  inactivityScores _ _ := ⟨rfl, rfl⟩
  slashings _ _ := ⟨rfl, rfl⟩
  randaoMixes _ _ := ⟨rfl, rfl⟩
  historicalRoots _ _ := ⟨rfl, rfl⟩
  historicalSummaries _ _ := ⟨rfl, rfl⟩
  participationRecords _ := ⟨rfl, rfl⟩
  pendingConsolidations _ _ := ⟨rfl, rfl⟩
  syncCommittees _ _ _ := ⟨rfl, rfl⟩
  proposerLookahead _ _ := ⟨rfl, rfl⟩
  ptcWindow _ _ := ⟨rfl, rfl⟩

/-- Applying a list of pending deposits adds at most one validator for each of them. -/
private theorem foldlM_applyPendingDeposit_size :
    ∀ (applied : List PendingDeposit) {state next : BeaconState preset fork},
      applied.foldlM (applyPendingDeposit config checks) state = .ok next →
        next.validators.data.size ≤ state.validators.data.size + applied.length
  | [], _, _, computed => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | deposit :: rest, _, _, computed => by
    simp only [List.foldlM, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    have one := (applyPendingDeposit_validators_size_le_and_mem first).1
    have more := foldlM_applyPendingDeposit_size rest tail
    simp only [List.length_cons]
    omega

/-- The pending deposits of an epoch never raise the validators plus the pending deposits. -/
theorem processPendingDeposits_registryLoad_le {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    registryLoad after ≤ registryLoad state := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, pushed, _, _, _, perm,
    applies, rfl⟩ := processPendingDeposits_applied computed
  have grown := foldlM_applyPendingDeposit_size applied applies
  have lengths := perm.length_eq
  have queueLength := congrArg List.length queue
  have pushedLength := congrArg List.length pushed
  simp only [Array.length_toList, List.length_append] at queueLength pushedLength lengths
  unfold registryLoad
  simp only [electra, ↓reduceDIte]
  omega

/-- Justification and finalization keep the registry size and the queue. -/
private theorem loadKept_justification
    (computed : processJustificationAndFinalization state = .ok after) : LoadKept state after := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact ⟨by rw [← rest], by rw [← rest]⟩

/-- The builder payments keep the registry size and the queue. -/
private theorem loadKept_builderPayments {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) : LoadKept state after := by
  rw [processBuilderPendingPayments_eq computed]
  exact ⟨rfl, rfl⟩

/-- The pending balances never raise the validators plus the pending deposits. -/
private theorem processPendingBalances_registryLoad_le
    (computed : processPendingBalances config checks state = .ok after) :
    registryLoad after ≤ registryLoad state := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    rw [LoadKept.registryLoad_eq (loadKeptLaws.processPendingConsolidations consolidated)]
    exact processPendingDeposits_registryLoad_le deposited
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Nat.le_refl _

/-- The epoch steps before the payments never raise the validators plus the pending deposits. -/
private theorem epochBeforePayments_registryLoad_le
    (computed : epochBeforePayments config checks state = .ok after) :
    registryLoad after ≤ registryLoad state := by
  simp only [epochBeforePayments, bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pendingOk⟩ := computed
  have scoredKept : LoadKept justified scored := by
    split at scoredOk
    · exact loadKeptLaws.processInactivityUpdates scoredOk
    · simp only [pure, Except.pure, Except.ok.injEq] at scoredOk
      exact scoredOk ▸ ⟨rfl, rfl⟩
  have resetKept : LoadKept slashed reset := by
    split at resetOk
    · exact loadKeptLaws.processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ ⟨rfl, rfl⟩
  refine Nat.le_trans (processPendingBalances_registryLoad_le pendingOk) (Nat.le_of_eq ?_)
  rw [LoadKept.registryLoad_eq resetKept,
    LoadKept.registryLoad_eq (loadKeptLaws.processSlashings slashedOk),
    LoadKept.registryLoad_eq (loadKeptLaws.processRegistryUpdates registeredOk),
    LoadKept.registryLoad_eq (loadKeptLaws.processRewardsAndPenalties rewardedOk),
    LoadKept.registryLoad_eq scoredKept,
    LoadKept.registryLoad_eq (loadKept_justification justifiedOk)]

/-- The epoch transition never raises the validators plus the pending deposits, at every fork. -/
theorem processEpoch_registryLoad_le (computed : processEpoch config checks state = .ok after) :
    registryLoad after ≤ registryLoad state := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processEpoch, altair, ↓reduceDIte] at computed
    obtain ⟨pending, paid, rooted, pendingOk, paidOk, middle, tail⟩ :=
      loadKeptLaws.processEpochAltair_paymentSplit computed
    have paidKept : LoadKept pending paid := by
      split at paidOk
      · exact loadKept_builderPayments (liftAccessor_ok.mp paidOk)
      · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
        exact paidOk ▸ ⟨rfl, rfl⟩
    have rotated : LoadKept rooted (processParticipationFlagUpdates rooted altair) := ⟨rfl, rfl⟩
    refine Nat.le_trans (Nat.le_of_eq ?_) (epochBeforePayments_registryLoad_le pendingOk)
    rw [LoadKept.registryLoad_eq tail, LoadKept.registryLoad_eq rotated,
      LoadKept.registryLoad_eq middle, LoadKept.registryLoad_eq paidKept]
  · obtain ⟨justified, justifiedOk, rest⟩ :=
      loadKeptLaws.processEpoch_split_of_lt_altair (Nat.lt_of_not_le altair) computed
    exact Nat.le_of_eq ((LoadKept.registryLoad_eq rest).trans
      (LoadKept.registryLoad_eq (loadKept_justification justifiedOk)))

/-- A slot never raises the validators plus the pending deposits, at every fork.

The slot stays in its fork: the upgrades come after it. -/
theorem advanceSlot_registryLoad_le (computed : advanceSlot config checks state = .ok after) :
    registryLoad after ≤ registryLoad state := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have slotKept : LoadKept epoched { epoched with slot := next } := ⟨rfl, rfl⟩
  rw [LoadKept.registryLoad_eq slotKept]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · refine Nat.le_trans (processEpoch_registryLoad_le epochedOk) (Nat.le_of_eq ?_)
    exact LoadKept.registryLoad_eq ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    exact epochedOk ▸ Nat.le_of_eq (LoadKept.registryLoad_eq ⟨rfl, rfl⟩)

/-- A run of slots never raises the validators plus the pending deposits, at every fork. -/
theorem advanceSlots_registryLoad_le {count : Nat}
    (computed : advanceSlots config checks count state = .ok after) :
    registryLoad after ≤ registryLoad state := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Nat.le_refl _
  | succ count hold =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact Nat.le_trans (hold rest) (advanceSlot_registryLoad_le nextOk)

end EthLib.Consensus
