module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.Transition.SyncAggregate

/-!
# Funding across a block

Before Gloas and from Electra, a block conserves the funded stake and the deposit carry.

The exception is the credits recorded by its replay.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem funding_block_change {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (life : RegistryLifecycle s t)
    (size : t.validators.data.size = s.validators.data.size) (matched : BalancesMatch t)
    (slot : t.slot = s.slot) (effective : EffectiveKept s t)
    (pending : ∀ i, (t.pendingConsolidations electra).data.toList.any
      (fun c => c.sourceIndex.toNat == i) = true →
      (s.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == i) = true ∨
      ∃ v, s.validators.data[i]? = some v ∧
        (isActiveValidator v (getCurrentEpoch s) = true ∨ getCurrentEpoch s < v.activationEpoch)) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + balanceCredits s t := by
  rw [← funding_potential_eq t electra, ← funding_potential_eq s electra]
  have bound := funding_potential_change (t.pendingConsolidations electra).data.toList
    (s.pendingConsolidations electra).data.toList
    (fun i => actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)
    size life (by simp [getCurrentEpoch, slot]) pending (fun i => by
      by_cases inside : i < s.validators.data.size
      · rw [effective i inside]; omega
      · have one : s.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
        have two : t.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
        simp [effectiveAt, one, two]; omega)
  apply bound.trans
  apply Nat.add_le_add_left
  unfold balanceCredits
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i member
    change t.balances.data.size = t.validators.data.size at matched
    simp only [Finset.mem_range] at member ⊢
    omega
  · intros; exact Nat.zero_le _

private theorem funding_block_kept {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (life : RegistryLifecycle s t)
    (size : t.validators.data.size = s.validators.data.size) (matched : BalancesMatch t)
    (slot : t.slot = s.slot) (effective : EffectiveKept s t)
    (queue : SamePendingQueue s t) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ + balanceCredits s t := by
  apply funding_block_change electra life size matched slot effective
  intro i pending
  exact Or.inl (by simpa only [show t.pendingConsolidations = s.pendingConsolidations from
    queue] using pending)

-- A validated request adds only an already active source to pending support.
private theorem funding_request_support {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    ∀ i, (t.pendingConsolidations electra).data.toList.any
      (fun c => c.sourceIndex.toNat == i) = true →
      (s.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == i) = true ∨
      ∃ v, s.validators.data[i]? = some v ∧
        (isActiveValidator v (getCurrentEpoch s) = true ∨
          getCurrentEpoch s < v.activationEpoch) := by
  have kept (queue : SamePendingQueue s t) : ∀ i,
      (t.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == i) = true →
      (s.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == i) = true ∨
      ∃ v, s.validators.data[i]? = some v ∧
        (isActiveValidator v (getCurrentEpoch s) = true ∨ getCurrentEpoch s < v.activationEpoch) :=
    fun _ h => Or.inl (by simpa only [show t.pendingConsolidations = s.pendingConsolidations
      from queue] using h)
  have queued {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
      (found : s.validators.data[sourceIndex.toNat]? = some source)
      (active : isActiveValidator source (getCurrentEpoch s) = true)
      (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) : ∀ i,
      (t.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == i) = true →
      (s.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == i) = true ∨
      ∃ v, s.validators.data[i]? = some v ∧
        (isActiveValidator v (getCurrentEpoch s) = true ∨
          getCurrentEpoch s < v.activationEpoch) := by
    simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨⟨churned, epoch⟩, churnOk, _, _, written, set, pending, appended, rfl⟩ := ok
    have queue : churned.pendingConsolidations = s.pendingConsolidations := by
      simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churnOk
      obtain ⟨_, _, _, _, _, _, final⟩ := churnOk
      cases final; rfl
    obtain ⟨_, rfl⟩ := setValidator_ok set
    have push := appendWithinLimit_data appended
    intro i member
    rw [push] at member
    simp only [Array.toList_push, List.any_append, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_eq_true, beq_iff_eq] at member
    rcases member with old | eq
    · exact Or.inl (by simpa only [BeaconState.putValidator, queue] using old)
    · exact Or.inr ⟨source, eq ▸ found, Or.inl active⟩
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact kept (SamePendingQueue.refl _))
    | exact kept (SamePendingQueue.compounding (liftAccessor_ok.mp ok))
    | exact queued (getElem?_toNat_of_ofNatChecked (by assumption))
        (by clear ok; simp_all) ok

private theorem funding_block_deposit {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  rw [← funding_potential_eq t electra, ← funding_potential_eq s electra]
  rw [SamePendingQueue.deposit electra ok]
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_fork_cases applied with ⟨_, rfl | ⟨_, _, rfl | added, rfl⟩⟩ | ⟨early, _⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · have bound := funding_registration (s.pendingConsolidations electra).data.toList
      (s := {s with eth1DepositIndex := fun _ => next}) matched added
    convert bound using 1 <;>
      simp [funding_potential, getCurrentEpoch, effectiveAt, actualBalanceAt] <;> rfl
  · exact absurd electra (Nat.not_le_of_lt early)

private def funding_block_cost (event : BalanceEvent preset) : Nat :=
  if event.source = .deposits ∨ event.source = .consolidations then 0 else event.credits

private theorem funding_block_cost_le {events : List (BalanceEvent preset)}
    (bounded : EventsBounded events) :
    (events.map funding_block_cost).sum ≤ (events.map fundingCredit).sum := by
  induction events with
  | nil => simp
  | cons e rest ih =>
    have bound := (bounded e (by simp)).1
    have one : funding_block_cost e ≤ fundingCredit e := by
      cases source : e.source <;> simp_all [funding_block_cost, fundingCredit]
    simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add one
      (ih (fun x h => bounded x (by simp [h])))

private theorem funding_block_same {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (matched : BalancesMatch t)
    (life : RegistryLifecycle s t) (size : t.validators.data.size = s.validators.data.size)
    (slot : t.slot = s.slot) (effective : EffectiveKept s t)
    (queue : SamePendingQueue s t) (balances : t.balances = s.balances) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  simpa only [balanceCredits, actualBalanceAt, balances, Nat.sub_self,
    Finset.sum_const_zero, Nat.add_zero] using
    funding_block_kept electra life size matched slot effective queue

private def FundingReplay {fork : Fork} (s : BeaconState preset fork)
    (post : BalanceReplay preset fork) : Prop :=
  BalancesMatch post.1 ∧ fundedStake ⟨fork, post.1⟩ ≤
    fundedStake ⟨fork, s⟩ + (post.2.map funding_block_cost).sum

private theorem funding_block_record {fork : Fork} {s : BeaconState preset fork}
    {pre post : BalanceReplay preset fork} {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    (preserves : ∀ a b, action a = .ok b → BalancesMatch a → BalancesMatch b)
    (bound : ∀ a b, BalancesMatch a → action a = .ok b →
      fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩ +
        if source = .deposits ∨ source = .consolidations then 0 else balanceCredits a b)
    (initial : FundingReplay s pre)
    (ok : recordBalance source limits action pre = .ok post) : FundingReplay s post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, after, actionOk, rfl⟩ := ok
  refine ⟨preserves _ _ actionOk initial.1, ?_⟩
  have one := bound _ _ initial.1 actionOk
  have prior := initial.2
  simpa only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero, funding_block_cost, BalanceEvent.credits,
    Nat.add_assoc, balanceCredits] using one.trans (Nat.add_le_add_right prior _)

private theorem funding_block_carry {fork : Fork} {s : BeaconState preset fork}
    {pre post : BalanceReplay preset fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    (preserves : ∀ a b, action a = .ok b → BalancesMatch a → BalancesMatch b)
    (bound : ∀ a b, BalancesMatch a → action a = .ok b →
      fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩)
    (initial : FundingReplay s pre) (ok : carryBalance action pre = .ok post) :
    FundingReplay s post := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, actionOk, rfl⟩ := ok
  exact ⟨preserves _ _ actionOk initial.1, (bound _ _ initial.1 actionOk).trans initial.2⟩

private theorem funding_block_replay {fork : Fork} {s : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (matched : BalancesMatch s) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork) {post : BalanceReplay preset fork}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : FundingReplay s post := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have record {pre post : BalanceReplay preset fork} {source : BalanceSource}
      {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
      (notDeposit : source ≠ .deposits) (notTransfer : source ≠ .consolidations)
      (frame : ∀ a b, action a = .ok b → Frame a b)
      (life : ∀ a b, action a = .ok b → RegistryLifecycle a b)
      (size : ∀ a b, action a = .ok b → b.validators.data.size = a.validators.data.size)
      (effective : ∀ a b, action a = .ok b → EffectiveKept a b)
      (queue : ∀ a b, action a = .ok b → SamePendingQueue a b)
      (initial : FundingReplay s pre)
      (ok : recordBalance source limits action pre = .ok post) : FundingReplay s post := by
    apply funding_block_record (fun a b ok => (frame a b ok).balancesMatch) _ initial ok
    intro a b matched ok
    simp only [notDeposit, notTransfer, or_self, ↓reduceIte]
    exact funding_block_kept electra (life a b ok) (size a b ok)
      ((frame a b ok).balancesMatch matched) (frame a b ok).slot
      (effective a b ok) (queue a b ok)
  have carry {pre post : BalanceReplay preset fork}
      {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
      (frame : ∀ a b, action a = .ok b → Frame a b)
      (life : ∀ a b, action a = .ok b → RegistryLifecycle a b)
      (size : ∀ a b, action a = .ok b → b.validators.data.size = a.validators.data.size)
      (effective : ∀ a b, action a = .ok b → EffectiveKept a b)
      (queue : ∀ a b, action a = .ok b → SamePendingQueue a b)
      (balances : ∀ a b, action a = .ok b → b.balances = a.balances)
      (initial : FundingReplay s pre) (ok : carryBalance action pre = .ok post) :
      FundingReplay s post := by
    apply funding_block_carry (fun a b ok => (frame a b ok).balancesMatch) _ initial ok
    intro a b matched ok
    exact funding_block_same electra ((frame a b ok).balancesMatch matched)
      (life a b ok) (size a b ok) (frame a b ok).slot
      (effective a b ok) (queue a b ok) (balances a b ok)
  unfold blockBalanceReplay at ok
  simp only [bellatrix, electra, altair, ↓reduceDIte, bind_ok_iff] at ok
  obtain ⟨headed, headerOk, executed, executionOk, randao, randaoOk, voted, votedOk,
    expected, _, _, _, proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk,
    deposited, depositOk, exited, exitOk, changed, changedOk, deposits, depositRequestOk,
    withdrawals, withdrawalOk, requested, consolidations, synced⟩ := ok
  have headedBound : FundingReplay s headed := by
    apply carry (fun _ _ ok => (frame_processBlockHeader ok).toFrame)
      (fun _ _ ok => registryLifecycle_processBlockHeader ok)
      (fun _ _ ok => (sameSizes_processBlockHeader ok).1)
      (fun _ _ ok => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok; exact effectiveKept_refl _)
      (fun _ _ ok => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok; rfl)
      (fun _ _ ok => by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok; rfl)
      ⟨matched, by simp⟩ headerOk
  have executedBound := record (by decide) (by decide)
    (fun _ _ ok => (frame_processBlockExecution ok).toFrame)
    (fun _ _ ok => .of_data (congrArg (·.data) (processBlockExecution_validators ok)))
    (fun _ _ ok => congrArg (·.data.size) (processBlockExecution_validators ok))
    (fun _ _ ok => effectiveKept_data (congrArg (·.data) (processBlockExecution_validators ok)))
    (fun _ _ ok => SamePendingQueue.blockExecution early ok) headedBound executionOk
  have randaoBound : FundingReplay s randao := by
    apply carry (fun _ _ ok => (frame_processRandao ok).toFrame)
      (fun _ _ ok => registryLifecycle_processRandao ok)
      (fun _ _ ok => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
        processRandao_eq ok; rfl)
      (fun _ _ ok => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
        processRandao_eq ok; exact effectiveKept_refl _)
      (fun _ _ ok => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
        processRandao_eq ok; rfl)
      (fun _ _ ok => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
        processRandao_eq ok; rfl) executedBound randaoOk
  have votedBound : FundingReplay s voted := by
    apply carry (fun _ _ ok => (frame_processEth1Data ok).toFrame)
      (fun _ _ ok => registryLifecycle_processEth1Data ok)
      (fun _ _ ok => by obtain ⟨_, _, eq⟩ := processEth1Data_eq ok; rw [← eq])
      (fun _ _ ok => by
        obtain ⟨_, _, eq⟩ := processEth1Data_eq ok
        rw [← eq]; exact effectiveKept_refl _)
      (fun _ _ ok => by obtain ⟨_, _, eq⟩ := processEth1Data_eq ok; rw [← eq]; rfl)
      (fun _ _ ok => by obtain ⟨_, _, eq⟩ := processEth1Data_eq ok; rw [← eq])
      randaoBound votedOk
  have proposedBound := foldlM_ok_invariant (FundingReplay s)
    (fun _ sl _ h ok => record (by decide) (by decide)
      (fun _ _ ok => (frame_processProposerSlashing ok).toFrame)
      (fun _ _ ok => registryLifecycle_processProposerSlashing ok)
      (fun _ _ ok => (sameSizes_processProposerSlashing ok).1)
      (fun _ _ ok => effectiveKept_proposerSlashing ok)
      (fun _ _ ok => SamePendingQueue.proposer ok) h ok) votedBound proposedOk
  have attestedBound := foldlM_ok_invariant (FundingReplay s)
    (fun _ sl _ h ok => record (by decide) (by decide)
      (fun _ _ ok => (frame_processAttesterSlashing ok).toFrame)
      (fun _ _ ok => registryLifecycle_processAttesterSlashing ok)
      (fun _ _ ok => (sameSizes_processAttesterSlashing ok).1)
      (fun _ _ ok => effectiveKept_attesterSlashing ok)
      (fun _ _ ok => SamePendingQueue.attester ok) h ok) proposedBound attestedOk
  have rewardedBound := foldlM_ok_invariant (FundingReplay s)
    (fun _ att _ h ok => record (by decide) (by decide)
      (fun _ _ ok => frame_processAttestation ok)
      (fun _ _ ok => registryLifecycle_processAttestation ok)
      (fun _ _ ok => (sameSizes_processAttestation ok).1)
      (fun _ _ ok => effectiveKept_data (by rw [(processAttestation_registry ok).1]))
      (fun _ _ ok => SamePendingQueue.attestation electra ok) h ok) attestedBound rewardedOk
  have depositedBound := foldlM_ok_invariant (FundingReplay s)
    (fun _ dep _ h ok => funding_block_record
      (fun _ _ ok => balancesMatch_processDeposit ok)
      (fun _ _ h ok => by simpa using funding_block_deposit electra h ok) h ok)
    rewardedBound depositOk
  have exitOne {a b : BeaconState preset fork} {signed : SignedVoluntaryExit}
      (h : BalancesMatch a) (ok : processVoluntaryExit config checks a signed = .ok b) :
      BalancesMatch b ∧ fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩ := by
    exact ⟨(frame_processVoluntaryExit ok).balancesMatch h,
      funding_block_same electra ((frame_processVoluntaryExit ok).balancesMatch h)
        (registryLifecycle_processVoluntaryExit ok) (sameSizes_processVoluntaryExit ok).1
        (frame_processVoluntaryExit ok).slot (effectiveKept_voluntaryExit ok)
        (SamePendingQueue.voluntary ok) (coverage_voluntary ok)⟩
  have exitedBound := funding_block_carry
    (fun a _ ok h => (foldlM_ok_invariant (fun b => BalancesMatch b ∧
      fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩)
      (fun _ _ _ prior ok => ⟨(exitOne prior.1 ok).1,
        (exitOne prior.1 ok).2.trans prior.2⟩) ⟨h, Nat.le_refl _⟩
      (by simpa only [← Array.foldlM_toList] using ok)).1)
    (fun a _ h ok => (foldlM_ok_invariant (fun b => BalancesMatch b ∧
      fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩)
      (fun _ _ _ prior ok => ⟨(exitOne prior.1 ok).1,
        (exitOne prior.1 ok).2.trans prior.2⟩) ⟨h, Nat.le_refl _⟩
      (by simpa only [← Array.foldlM_toList] using ok)).2) depositedBound exitOk
  have blsOne {a b : BeaconState preset fork} {signed : SignedBLSToExecutionChange}
      (h : BalancesMatch a) (ok : processBlsToExecutionChange config checks a signed = .ok b) :
      BalancesMatch b ∧ fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩ := by
    exact ⟨(frame_processBlsToExecutionChange ok).balancesMatch h,
      funding_block_same electra ((frame_processBlsToExecutionChange ok).balancesMatch h)
        (registryLifecycle_processBlsToExecutionChange ok)
        (sameSizes_processBlsToExecutionChange ok).1
        (frame_processBlsToExecutionChange ok).slot (effectiveKept_blsChange ok)
        (SamePendingQueue.bls ok) (coverage_bls ok)⟩
  have changedBound : FundingReplay s changed := by
    apply funding_block_carry _ _ exitedBound changedOk
    all_goals intro a b
    all_goals
      intro h₁ h₂
      first
      | have action := h₁; have matched := h₂
        unfold processBlsToExecutionChanges at action
        split at action
        · exact (foldlM_ok_invariant BalancesMatch
            (fun _ _ _ h ok => (blsOne h ok).1) matched
            (by simpa only [← Array.foldlM_toList] using action))
        · cases action; exact matched
      | have matched := h₁; have action := h₂
        unfold processBlsToExecutionChanges at action
        split at action
        · exact (foldlM_ok_invariant (fun b => BalancesMatch b ∧
            fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩)
            (fun _ _ _ prior ok => ⟨(blsOne prior.1 ok).1,
              (blsOne prior.1 ok).2.trans prior.2⟩) ⟨matched, Nat.le_refl _⟩
            (by simpa only [← Array.foldlM_toList] using action)).2
        · cases action; exact Nat.le_refl _
  have requestOne {a b : BeaconState preset fork} {request : DepositRequest}
      (ok : processDepositRequest a electra request = .ok b) :
      b.validators = a.validators ∧ b.balances = a.balances := by
    obtain ⟨_, recorded⟩ := recordDepositRequestsStart_eq (state := a) (index := request.index)
    simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
      bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact ⟨rfl, rfl⟩
  have depositsBound : FundingReplay s deposits := by
    apply funding_block_carry _ _ changedBound depositRequestOk
    · intro a b ok h
      exact (foldlM_ok_invariant BalancesMatch
        (fun _ _ _ h ok => (frame_processDepositRequest ok).balancesMatch h) h
        (by simpa only [← Array.foldlM_toList] using ok))
    · intro a b h ok
      exact (foldlM_ok_invariant (fun b => BalancesMatch b ∧
        fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩)
        (fun _ _ _ prior ok => ⟨(frame_processDepositRequest ok).balancesMatch prior.1,
          (funding_block_same electra ((frame_processDepositRequest ok).balancesMatch prior.1)
            (registryLifecycle_processDepositRequest ok)
            (congrArg (·.data.size) (requestOne ok).1) (frame_processDepositRequest ok).slot
            (effectiveKept_data (congrArg (·.data) (requestOne ok).1))
            (SamePendingQueue.depositRequest ok) (requestOne ok).2).trans prior.2⟩)
        ⟨h, Nat.le_refl _⟩ (by simpa only [← Array.foldlM_toList] using ok)).2
  have withdrawalsBound : FundingReplay s withdrawals := by
    apply funding_block_carry _ _ depositsBound withdrawalOk
    · intro a b ok h
      exact foldlM_ok_invariant BalancesMatch
        (fun _ _ _ h ok => (frame_processWithdrawalRequest ok).balancesMatch h) h
        (by simpa only [← Array.foldlM_toList] using ok)
    · intro a b h ok
      exact (foldlM_ok_invariant (fun b => BalancesMatch b ∧
        fundedStake ⟨fork, b⟩ ≤ fundedStake ⟨fork, a⟩)
        (fun _ _ _ prior ok => ⟨(frame_processWithdrawalRequest ok).balancesMatch prior.1,
          (funding_block_same electra ((frame_processWithdrawalRequest ok).balancesMatch prior.1)
            (registryLifecycle_processWithdrawalRequest ok)
            (sameSizes_processWithdrawalRequest ok).1
            (frame_processWithdrawalRequest ok).slot (effectiveKept_withdrawalRequest ok)
            (SamePendingQueue.withdrawalRequest ok)
            (coverage_withdrawal_request ok)).trans prior.2⟩)
        ⟨h, Nat.le_refl _⟩ (by simpa only [← Array.foldlM_toList] using ok)).2
  have requestedBound := foldlM_ok_invariant (FundingReplay s)
    (fun _ request _ h ok => funding_block_record
      (fun _ _ ok => (frame_processConsolidationRequest ok).balancesMatch)
      (fun a b h ok => by
        simpa using funding_block_change electra (registryLifecycle_processConsolidationRequest ok)
          (sameSizes_processConsolidationRequest ok).1
          ((frame_processConsolidationRequest ok).balancesMatch h)
          (frame_processConsolidationRequest ok).slot (effectiveKept_consolidationRequest ok)
          (funding_request_support ok)) h ok) withdrawalsBound consolidations
  exact record (by decide) (by decide)
    (fun _ _ ok => (frame_processSyncAggregate ok).toFrame)
    (fun _ _ ok => by obtain ⟨_, rfl⟩ := processSyncAggregate_eq ok; exact .of_data rfl)
    (fun _ _ ok => (sameSizes_processSyncAggregate ok).1)
    (fun _ _ ok => by obtain ⟨_, rfl⟩ := processSyncAggregate_eq ok; exact effectiveKept_data)
    (fun _ _ ok => by obtain ⟨_, rfl⟩ := processSyncAggregate_eq ok; rfl) requestedBound synced

/-- A block preserves funding except for its recorded external credits.

Validated consolidation requests retain support without issuing additional funding. -/
theorem funding_block {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (matched : BalancesMatch s)
    (engine : ExecutionEngine preset fork) (block : BeaconBlock preset fork)
    (ok : processBlock config checks engine s block = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok (t, events)) :
    fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ ≤
      fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ + (events.map fundingCredit).sum := by
  have bound := (funding_block_replay electra early matched engine block replayed).2
  change fundedStake ⟨fork, t⟩ ≤
    fundedStake ⟨fork, s⟩ + (events.map funding_block_cost).sum at bound
  have costs := funding_block_cost_le
    (blockBalanceReplay_bounded early engine block matched replayed)
  change (events.map funding_block_cost).sum ≤ (events.map fundingCredit).sum at costs
  have carry := depositCarry_processBlock early ok
  have same : funding_carry ⟨fork, t⟩ = funding_carry ⟨fork, s⟩ := by
    simp only [funding_carry, electra, ↓reduceDIte, carry]
  rw [same]
  omega

end

end EthLib.Consensus.DirectSafety
