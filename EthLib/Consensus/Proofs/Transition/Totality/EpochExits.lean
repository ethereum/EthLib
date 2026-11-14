module

public import EthLib.Consensus.Proofs.Transition.EpochDecomposition
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryElectra
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Proofs: the exit queue after one epoch

One epoch carries a ceiling on the exit queue into the next, both before and from Electra.

From Electra, the registry updates bound the queue end and each exit epoch.

The bound is a ceiling plus the cost.

That cost counts each validator that has not started to exit.

Each one owes its effective balance in increments, plus one.

The other steps of the epoch keep the queue and every exit epoch that is set.

A deposit adds a validator with no exit epoch, so it raises only the cost owed.

That cost is at most the sum of the effective balances in increments, plus the registry size.

So the ceiling rises by at most that amount in each epoch.

The churn carried for exits stays at most the larger of its value before and a bound on one churn.

Before Electra, the registry updates leave each exit epoch at most a ceiling plus the registry size.

The other steps keep every exit epoch that is set, so the ceiling rises by at most that size.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The end of the exit queue, and each exit epoch that is set, are at most a bound. -/
def ExitsAtMost (electra : .pectra ≤ fork) (bound : Nat) (state : BeaconState preset fork) :
    Prop :=
  (state.earliestExitEpoch electra).toNat ≤ bound ∧
    ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ bound

/-- A larger bound holds whenever a smaller one does. -/
theorem ExitsAtMost.mono {electra : .pectra ≤ fork} {low high : Nat}
    (bounded : ExitsAtMost electra low state) (le : low ≤ high) :
    ExitsAtMost electra high state :=
  ⟨Nat.le_trans bounded.1 le, fun validator member set =>
    Nat.le_trans (bounded.2 validator member set) le⟩

/-- The cost owed by the exits not yet started is at most a sum.

That sum is the effective balances in increments, plus the registry size. -/
theorem exitCost_le (state : BeaconState preset fork) :
    exitCost preset state ≤
      effectiveBalanceSum state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        state.validators.data.size := by
  unfold exitCost effectiveBalanceSum
  have floors : ∀ values : List Nat,
      (values.map (· / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)).sum ≤
        values.sum / preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    intro values
    induction values with
    | nil => simp
    | cons head tail step =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.le_trans (Nat.add_le_add_left step _) Nat.div_add_div_le_add_div
  refine Nat.le_trans (((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _) ?_
  rw [List.sum_map_add, ← Array.length_toList]
  simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_one]
  refine Nat.add_le_add_right ?_ _
  have := floors (state.validators.data.toList.map (·.effectiveBalance.toNat))
  rwa [List.map_map] at this

private abbrev ConsolidationKept (s t : BeaconState preset fork) : Prop :=
  t.earliestConsolidationEpoch = s.earliestConsolidationEpoch

private theorem consolidationKept_setValidatorAt {s t : BeaconState preset fork} {index : Nat}
    {v : Validator} (ok : s.setValidatorAt index v = .ok t) : ConsolidationKept s t := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

private theorem consolidationKept_setBalance {s t : BeaconState preset fork}
    {index : ValidatorIndex} {balance : Gwei} (ok : s.setBalance index balance = .ok t) :
    ConsolidationKept s t := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  rfl

private theorem consolidationKept_exitQueue {config : Config} {s t : BeaconState preset fork}
    {amount : Gwei} {epoch : Epoch} (ok : exitQueue config s amount = .ok (t, epoch)) :
    ConsolidationKept s t := by
  unfold exitQueue at ok
  split at ok
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := ok
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, rfl, _⟩ := ok
    rfl

private theorem consolidationKept_exit {config : Config} {s t : BeaconState preset fork}
    {index : ValidatorIndex} (ok : initiateValidatorExit config s index = .ok t) :
    ConsolidationKept s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · rfl
  · exact (consolidationKept_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])).trans
      (consolidationKept_exitQueue queue)

private theorem consolidationKept_addValidator {s t : BeaconState preset fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry s pubkey credentials amount = .ok t) :
    ConsolidationKept s t := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
      pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rfl
  · split at computed <;> cases computed
    rfl

/-- Every write that an epoch step makes keeps the end of the consolidation queue. -/
private theorem consolidationLaws : EpochFrameLaws (fork := fork) (preset := preset)
    ConsolidationKept where
  refl _ := rfl
  trans one two := two.trans one
  setValidatorAt set _ _ _ _ _ := consolidationKept_setValidatorAt set
  increaseBalance ok := by
    obtain ⟨_, set⟩ := increaseBalance_ok ok
    exact consolidationKept_setBalance set
  decreaseBalance ok := by
    obtain ⟨_, set⟩ := decreaseBalance_ok ok
    exact consolidationKept_setBalance set
  initiateValidatorExit := consolidationKept_exit
  addValidatorToRegistry added _ := consolidationKept_addValidator added
  eth1DataVotes _ _ := rfl
  inactivityScores _ _ := rfl
  slashings _ _ := rfl
  randaoMixes _ _ := rfl
  historicalRoots _ _ := rfl
  historicalSummaries _ _ := rfl
  participationRecords _ := rfl
  pendingDeposits _ _ _ := rfl
  pendingConsolidations _ _ := rfl
  syncCommittees _ _ _ := rfl
  proposerLookahead _ _ := rfl
  ptcWindow _ _ := rfl

/-- No step of an epoch moves the end of the consolidation queue. -/
theorem processEpoch_earliestConsolidationEpoch {config : Config} {checks : SignatureChecks}
    (computed : processEpoch config checks state = .ok after) :
    after.earliestConsolidationEpoch = state.earliestConsolidationEpoch := by
  refine (processEpoch_trace computed).transport ConsolidationKept (fun _ => rfl)
    (fun one two => two.trans one) fun stage _ _ _ ok => ?_
  by_cases ordinary : stage ≠ .justification ∧ stage ≠ .payments ∧ stage ≠ .participation ∧
      stage ≠ .pendingDeposits
  · exact consolidationLaws.toEpochStepLaws.epochEdge ordinary ok
  have edge := action_cases.mp ok
  cases stage <;> simp only [Edge] at edge
  case justification =>
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok edge
    · rfl
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      rw [← rest]
  case payments =>
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
    · exact edge ▸ rfl
  case participation =>
    split at edge
    · subst edge
      rfl
    · rename_i early
      obtain ⟨u, computed, _, _, restored⟩ :=
        processParticipationRecordUpdates_eq (state := _) (Nat.lt_of_not_le early)
      obtain rfl := Except.ok.inj (computed.symm.trans edge)
      exact congrArg (·.earliestConsolidationEpoch) restored
  case pendingDeposits =>
    split at edge
    · exact consolidationLaws.processPendingDeposits edge
    · exact edge ▸ rfl
  all_goals exact absurd ⟨nofun, nofun, nofun, nofun⟩ ordinary

/-- Each exit epoch that a later state sets is one set before. -/
private def ExitEpochsKept (state after : BeaconState preset fork) : Prop :=
  ∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
    ∃ old ∈ state.validators.data, old.exitEpoch = validator.exitEpoch

private theorem ExitEpochsKept.refl (state : BeaconState preset fork) :
    ExitEpochsKept state state :=
  fun validator member _ => ⟨validator, member, rfl⟩

private theorem ExitEpochsKept.trans {first second third : BeaconState preset fork}
    (one : ExitEpochsKept first second) (two : ExitEpochsKept second third) :
    ExitEpochsKept first third := fun validator member set => by
  obtain ⟨middle, middleMember, same⟩ := two validator member set
  obtain ⟨old, oldMember, same'⟩ := one middle middleMember (same ▸ set)
  exact ⟨old, oldMember, same'.trans same⟩

/-- A later state keeps the exit queue, and each exit epoch that it sets is one set before. -/
private def ExitsKept (state after : BeaconState preset fork) : Prop :=
  after.earliestExitEpoch = state.earliestExitEpoch ∧
    after.exitBalanceToConsume = state.exitBalanceToConsume ∧ ExitEpochsKept state after

private theorem ExitsKept.refl (state : BeaconState preset fork) : ExitsKept state state :=
  ⟨rfl, rfl, .refl state⟩

private theorem ExitsKept.trans {first second third : BeaconState preset fork}
    (one : ExitsKept first second) (two : ExitsKept second third) : ExitsKept first third :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, one.2.2.trans two.2.2⟩

/-- A ceiling on the exit queue carries over to a later state that keeps the relation. -/
private theorem ExitsAtMost.of_kept {electra : .pectra ≤ fork} {bound : Nat}
    (kept : ExitsKept state after) (bounded : ExitsAtMost electra bound state) :
    ExitsAtMost electra bound after := by
  refine ⟨by rw [kept.1]; exact bounded.1, fun validator member set => ?_⟩
  obtain ⟨old, oldMember, same⟩ := kept.2.2 validator member set
  rw [← same] at set ⊢
  exact bounded.2 old oldMember set

/-- A validator that a pending deposit adds has no exit epoch. -/
private theorem ExitEpochsKept.of_applyPendingDeposit {config : Config}
    {checks : SignatureChecks} {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    ExitEpochsKept state after := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact .refl _
  · obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    exact .refl _
  · intro validator member set
    rw [addValidatorToRegistry_validators_eq_push added, Array.mem_push] at member
    rcases member with old | rfl
    · exact ⟨validator, old, rfl⟩
    · exact absurd rfl set

/-- An update of one effective balance keeps every exit epoch. -/
private theorem ExitEpochsKept.of_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : ExitEpochsKept state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, found, _, _, _, _, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have read : state.validators.data[index] = old := by
    simpa [getValidatorAt, inside] using found
  intro validator member _
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set member with kept | rfl
  · exact ⟨validator, kept, rfl⟩
  · exact ⟨old, read ▸ Array.getElem_mem inside, rfl⟩

/-- Every epoch stage other than the registry updates keeps the exit queue.

Each exit epoch it sets was set before. -/
private theorem ExitsKept.of_edge {config : Config} {checks : SignatureChecks}
    {stage : EpochStage} {s t : BeaconState preset fork} (edge : Edge config checks stage s t)
    (other : stage ≠ .registry) : ExitsKept s t := by
  obtain ⟨epoch, carry⟩ := edge.exitQueue other
  refine ⟨epoch, carry, ?_⟩
  by_cases plain : stage ≠ .pendingDeposits ∧ stage ≠ .effectiveBalances
  · rw [ExitEpochsKept, edge.validators_eq ⟨other, plain⟩]
    exact ExitEpochsKept.refl s
  cases stage
  case pendingDeposits =>
    simp only [Edge] at edge
    split at edge
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, folded, rfl⟩ :=
        processPendingDeposits_applied edge
      have kept := foldlM_ok_invariant (g := applyPendingDeposit config checks)
        (ExitEpochsKept s) (fun _ _ _ prior step => prior.trans (.of_applyPendingDeposit step))
        (.refl s) folded
      exact kept
    · subst edge
      exact .refl _
  case effectiveBalances =>
    simp only [Edge] at edge
    unfold processEffectiveBalanceUpdates at edge
    exact foldlM_ok_invariant (ExitEpochsKept s)
      (fun _ _ _ prior step => prior.trans (.of_updateEffectiveBalance step)) (.refl s) edge
  all_goals exact absurd ⟨nofun, nofun⟩ plain

/-- From Electra, one epoch keeps a ceiling on the exit queue, raised by the cost owed.

The epoch must succeed.

The increment must be positive.

The least churn and the largest exit churn must each be at least one increment.

The other hypotheses bound the registry and the exit queue before the epoch.

They are the bounds that the registry updates need.

After the epoch, the end of the exit queue and each exit epoch that is set are at most a sum.

That sum is the ceiling plus the cost of the exits not yet started before the epoch.

The churn carried for exits is at most the larger of the one before and one churn bound.

To apply this again at the next epoch, the ceiling must grow by one more epoch. -/
theorem processEpoch_exits_of_electra {config : Config} {checks : SignatureChecks}
    (electra : .pectra ≤ fork) (computed : processEpoch config checks state = .ok after)
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    {ceiling : Nat}
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (bounded : ExitsAtMost electra ceiling state)
    (room : ceiling + exitCost preset state + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat <
      2 ^ 64 - 1)
    (carried : (state.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config state <
      2 ^ 64) :
    ExitsAtMost electra (ceiling + exitCost preset state) after ∧
      (after.exitBalanceToConsume electra).toNat ≤
        max (state.exitBalanceToConsume electra).toNat (exitChurnCeiling config state) := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity, .rewards] ++ (.registry :: [.slashings,
    .eth1Reset, .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances,
    .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow])) _ _ at trace
  obtain ⟨before, head, rest⟩ := append_iff.mp trace
  cases rest with
  | cons registryOk tail =>
    -- The steps before the registry updates keep the validators, the slot and the exit queue.
    obtain ⟨validators, slot, epoch, carry⟩ := head.transport
      (fun (first second : BeaconState preset fork) =>
        second.validators = first.validators ∧ second.slot = first.slot ∧
          second.earliestExitEpoch = first.earliestExitEpoch ∧
          second.exitBalanceToConsume = first.exitBalanceToConsume)
      (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
      (fun one two => ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
        two.2.2.2.trans one.2.2.2⟩)
      fun stage member _ _ ok => by
        have edge := action_cases.mp ok
        have queue := edge.exitQueue (by rintro rfl; simp at member)
        refine ⟨edge.validators_eq ⟨by rintro rfl; simp at member,
          by rintro rfl; simp at member, by rintro rfl; simp at member⟩, ?_, queue.1, queue.2⟩
        by_cases rewards : stage = .rewards
        · subst rewards
          rw [processRewardsAndPenalties_frame edge]
        · exact (edge.records ⟨rewards, by rintro rfl; simp at member,
            by rintro rfl; simp at member, by rintro rfl; simp at member,
            by rintro rfl; simp at member, by rintro rfl; simp at member⟩).2.2.2.2
    have costSame : exitCost preset before = exitCost preset state := by
      unfold exitCost
      rw [validators]
    have sumSame : effectiveBalanceSum before = effectiveBalanceSum state := by
      unfold effectiveBalanceSum
      rw [validators]
    have churnSame : exitChurnCeiling config before = exitChurnCeiling config state := by
      unfold exitChurnCeiling
      rw [sumSame]
    have epochSame : getCurrentEpoch before = getCurrentEpoch state := by
      simp only [getCurrentEpoch, slot]
    -- The registry updates move the exit queue by at most the cost owed.
    obtain ⟨registered, registeredOk, queued, exits, carried', -⟩ :=
      processRegistryUpdates_total_of_electra (config := config) before electra
        (by unfold BeaconState.RegistryWithinLimit; rw [validators]; exact within)
        (by rw [sumSame]; exact summed) increment minimum maximum ceiling
        (by rw [epochSame]; exact first) (by rw [epoch]; exact bounded.1)
        (by rw [validators]; exact bounded.2) (by rw [costSame]; exact room)
        (by rw [churnSame, carry]; exact carried)
    obtain rfl : registered = _ :=
      Except.ok.inj (registeredOk.symm.trans (action_cases.mp registryOk))
    rw [costSame] at queued exits
    rw [churnSame, carry] at carried'
    have middle : ExitsAtMost electra (ceiling + exitCost preset state) registered :=
      ⟨by omega, fun validator member set => by have := exits validator member set; omega⟩
    -- The steps after the registry updates keep the exit queue and each exit epoch that is set.
    have kept := tail.transport ExitsKept ExitsKept.refl (fun one two => one.trans two)
      fun stage member _ _ ok =>
        ExitsKept.of_edge (action_cases.mp ok) (by rintro rfl; simp at member)
    refine ⟨middle.of_kept kept, ?_⟩
    rw [kept.2.1]
    exact carried'

/-- Before Electra, one epoch keeps a ceiling on the exit epochs, raised by the registry size.

The epoch must succeed.

The ceiling must be at least the first epoch at which a new exit can take effect.

Each exit epoch that is set must be at most the ceiling.

The ceiling plus the registry size and the withdrawal delay must stay below 2^64.

They are the bounds that the registry updates need.

After the epoch, each exit epoch that is set is at most the ceiling plus the registry size.

At the next epoch, take this ceiling plus one, since the current epoch has risen by one. -/
theorem processEpoch_exits_of_lt_electra {config : Config} {checks : SignatureChecks}
    (before : fork < .pectra) (computed : processEpoch config checks state = .ok after)
    {ceiling : Nat}
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (room : ceiling + state.validators.data.size +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64) :
    ∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling + state.validators.data.size := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity, .rewards] ++ (.registry :: [.slashings,
    .eth1Reset, .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances,
    .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow])) _ _ at trace
  obtain ⟨middle, head, rest⟩ := append_iff.mp trace
  cases rest with
  | cons registryOk tail =>
    -- The steps before the registry updates keep the validators and the slot.
    obtain ⟨validators, slot⟩ := head.transport
      (fun (first second : BeaconState preset fork) =>
        second.validators = first.validators ∧ second.slot = first.slot)
      (fun _ => ⟨rfl, rfl⟩)
      (fun one two => ⟨two.1.trans one.1, two.2.trans one.2⟩)
      fun stage member _ _ ok => by
        have edge := action_cases.mp ok
        refine ⟨edge.validators_eq ⟨by rintro rfl; simp at member,
          by rintro rfl; simp at member, by rintro rfl; simp at member⟩, ?_⟩
        by_cases rewards : stage = .rewards
        · subst rewards
          rw [processRewardsAndPenalties_frame edge]
        · exact (edge.records ⟨rewards, by rintro rfl; simp at member,
            by rintro rfl; simp at member, by rintro rfl; simp at member,
            by rintro rfl; simp at member, by rintro rfl; simp at member⟩).2.2.2.2
    have sizeSame : middle.validators.data.size = state.validators.data.size := by
      rw [validators]
    have epochSame : getCurrentEpoch middle = getCurrentEpoch state := by
      simp only [getCurrentEpoch, slot]
    -- The registry updates set each exit epoch to at most the ceiling plus the registry size.
    obtain ⟨registered, registeredOk, bounded⟩ :=
      processRegistryUpdates_total_of_lt_electra (config := config) middle before ceiling
        (by rw [epochSame]; exact first) (by rw [validators]; exact exits)
        (by rw [sizeSame]; exact room)
    obtain rfl : registered = _ :=
      Except.ok.inj (registeredOk.symm.trans (action_cases.mp registryOk))
    rw [sizeSame] at bounded
    -- The steps after the registry updates set no new exit epoch.
    have kept := tail.transport ExitsKept ExitsKept.refl (fun one two => one.trans two)
      fun stage member _ _ ok =>
        ExitsKept.of_edge (action_cases.mp ok) (by rintro rfl; simp at member)
    intro validator member set
    obtain ⟨old, oldMember, same⟩ := kept.2.2 validator member set
    rw [← same] at set ⊢
    exact bounded old oldMember set

end EthLib.Consensus
