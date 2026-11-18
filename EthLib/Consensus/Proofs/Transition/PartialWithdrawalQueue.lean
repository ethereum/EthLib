module

public import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# The departure queues and the queue of pending partial withdrawals

The two departure queues hold the exit and the consolidation capacity of the validator set.

With the queue of pending partial withdrawals, they are what the balance queues of Electra write.

Most steps of a transition leave all of them unchanged.

Payments consume the front of the queue of partial withdrawals.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The two departure queues and the queue of partial withdrawals, without pending transfers. -/
def departureQueues {fork : Fork} (electra : .pectra ≤ fork)
    (s : BeaconState preset fork) :
    Epoch × Gwei × Epoch × Gwei × Array PendingPartialWithdrawal :=
  (s.earliestExitEpoch electra, s.exitBalanceToConsume electra,
    s.earliestConsolidationEpoch electra, s.consolidationBalanceToConsume electra,
    (s.pendingPartialWithdrawals electra).data)

/-- Two states hold the same queue of pending partial withdrawals, from Electra. -/
def PartialsSame {fork : Fork} (state after : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork,
    after.pendingPartialWithdrawals electra = state.pendingPartialWithdrawals electra

/-- A state holds the same queue as itself. -/
theorem PartialsSame.refl {fork : Fork} (state : BeaconState preset fork) :
    PartialsSame state state :=
  fun _ => rfl

/-- Holding the same queue is transitive. -/
theorem PartialsSame.trans {fork : Fork} {first second third : BeaconState preset fork}
    (one : PartialsSame first second) (two : PartialsSame second third) :
    PartialsSame first third :=
  fun electra => (two electra).trans (one electra)

/-- A fold whose steps keep the queue keeps it. -/
theorem PartialsSame.foldlM {fork : Fork} {state after : BeaconState preset fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → PartialsSame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : PartialsSame state after :=
  foldlM_ok_invariant (PartialsSame state)
    (fun _ _ _ before ok => before.trans (frame _ _ _ ok)) (PartialsSame.refl state) computed

/-- Equal queue fields among the departure queues give the same queue of partial withdrawals. -/
theorem pendingPartialWithdrawals_eq_of_queues {fork : Fork}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    (frame : (departureQueues electra after).2.2.2.2 = (departureQueues electra state).2.2.2.2) :
    after.pendingPartialWithdrawals electra = state.pendingPartialWithdrawals electra := by
  simp only [departureQueues] at frame
  revert frame
  generalize after.pendingPartialWithdrawals electra = a
  generalize state.pendingPartialWithdrawals electra = b
  cases a; cases b
  simp

/-- Equal queue fields among the departure queues at every Electra proof keep the queue. -/
theorem PartialsSame.of_queues {fork : Fork} {state after : BeaconState preset fork}
    (frame : ∀ electra : .pectra ≤ fork,
      (departureQueues electra after).2.2.2.2 = (departureQueues electra state).2.2.2.2) :
    PartialsSame state after :=
  fun electra => pendingPartialWithdrawals_eq_of_queues (frame electra)

/-- Equal departure queues give the same queue of partial withdrawals. -/
theorem PartialsSame.of_frame {fork : Fork} {state after : BeaconState preset fork}
    (frame : ∀ electra : .pectra ≤ fork,
      departureQueues electra after = departureQueues electra state) :
    PartialsSame state after :=
  .of_queues fun electra => congrArg (·.2.2.2.2) (frame electra)

/-- Setting a validator at a position keeps both departure queues. -/
theorem departureQueues_setValidatorAt {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {position : Nat} {validator : Validator}
    (ok : s.setValidatorAt position validator = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

/-- Setting a validator keeps both departure queues. -/
theorem departureQueues_setValidator {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {validator : Validator}
    (ok : s.setValidator index validator = .ok t) :
    departureQueues electra t = departureQueues electra s :=
  departureQueues_setValidatorAt electra (by rwa [← setValidator_eq_setValidatorAt])

/-- Raising a balance keeps both departure queues. -/
theorem departureQueues_increase {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s index amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- Lowering a balance keeps both departure queues. -/
theorem departureQueues_decrease {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s index amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

/-- Applying reward deltas keeps both departure queues. -/
theorem allDeltas_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deltas : Array Gwei × Array Gwei}
    (ok : applyAllDeltas s deltas = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro a index b kept stepped
  simp only [applyDeltas, liftAccessor_ok, bind_ok_iff] at stepped
  obtain ⟨_, _, raised, increase, decrease⟩ := stepped
  exact (departureQueues_decrease electra decrease).trans
    ((departureQueues_increase electra increase).trans kept)

/-- Epoch rewards and penalties preserve departure capacity and queue epochs. -/
theorem rewards_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processRewardsAndPenalties config s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  unfold processRewardsAndPenalties at ok
  split at ok
  · cases ok; rfl
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, folded⟩ := ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl folded
  intro a deltas b kept stepped
  exact (allDeltas_departureQueues electra stepped).trans kept

/-- Epoch slashing penalties debit balances without spending departure capacity. -/
theorem slashingPenalties_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processSlashings s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [processSlashings, electra, ↓reduceIte, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, folded⟩ := ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl folded
  intro a index b kept stepped
  unfold applySlashingPenaltyElectra at stepped
  simp only [bind_ok_iff] at stepped
  obtain ⟨_, _, stepped⟩ := stepped
  split at stepped
  · simp only [bind_ok_iff] at stepped
    obtain ⟨_, _, stepped⟩ := stepped
    split at stepped
    · simp only [bind_ok_iff] at stepped
      obtain ⟨_, _, _, _, decreased⟩ := stepped
      exact (departureQueues_decrease electra (liftAccessor_ok.mp decreased)).trans kept
    · cases stepped; exact kept
  · cases stepped; exact kept

/-- Adding a validator keeps both departure queues. -/
theorem addValidator_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  simp only [addValidatorToRegistry, altair, ↓reduceDIte,
    addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
  rfl

/-- Applying a deposit keeps both departure queues. -/
theorem applyDeposit_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (ok : applyDeposit config checks s key credentials amount signature = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  rcases applyDeposit_cases ok with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨early, _⟩
  · rfl
  · rfl
  · exact (addValidator_departureQueues electra added :)
  · exact absurd electra (Nat.not_le_of_lt early)

/-- Block deposits preserve departure capacity even when they append a validator. -/
theorem deposit_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, _, _, _, credited⟩ := processDeposit_ok ok
  exact (applyDeposit_departureQueues electra credited :)

/-- Execution deposit requests append pending deposits without changing departure capacity. -/
theorem depositRequest_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
  unfold recordDepositRequestsStart
  split <;> (try split) <;> rfl

/-- Attestation processing preserves departure queues before Gloas. -/
theorem attestation_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processAttestation, altair, ↓reduceDIte] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok, notGloas, ↓reduceDIte,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, raised, rfl⟩ := ok
  rw [departureQueues_increase electra raised]
  unfold setEpochParticipation
  split <;> rfl

/-- Changing withdrawal credentials leaves both departure queues unchanged. -/
theorem credentials_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- Applying a pending deposit keeps both departure queues. -/
theorem pendingDeposit_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · rfl
  · exact departureQueues_increase electra raised
  · exact addValidator_departureQueues electra added

/-- A pass over pending deposits keeps both departure queues. -/
theorem passPendingDeposits_departureQueues {fork : Fork}
    (electra : .pectra ≤ fork) {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {s : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available s processed count postponed
        deposits = .ok pass → departureQueues electra pass.1.state = departureQueues electra s :=
  fun ok =>
    passPendingDeposits_of (fun s t => departureQueues electra t = departureQueues electra s)
      (fun _ => rfl) (fun one two => two.trans one)
      (fun credited => pendingDeposit_departureQueues electra credited) ok

/-- Crediting pending deposits preserves both departure queues. -/
theorem pendingDeposits_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact passPendingDeposits_departureQueues electra ‹_›

/-- Debiting withdrawals keeps both departure queues. -/
theorem applyWithdrawals_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {withdrawals : Array Withdrawal}
    (ok : applyWithdrawals s withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold applyWithdrawals at ok
  rw [← Array.foldlM_toList] at ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro a withdrawal b kept stepped
  simp only [applyWithdrawal, notGloas, false_and, ↓reduceDIte] at stepped
  exact (departureQueues_decrease electra stepped).trans kept

/-- Moving the next withdrawal index keeps both departure queues. -/
theorem withdrawalIndex_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {withdrawals : Array Withdrawal}
    (ok : updateNextWithdrawalIndex s withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold updateNextWithdrawalIndex at ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    rfl
  · cases ok; rfl

/-- Moving the next withdrawal validator keeps both departure queues. -/
theorem withdrawalValidatorIndex_departureQueues {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    {capella : .shapella ≤ fork} {withdrawals : Array Withdrawal}
    (ok : updateNextWithdrawalValidatorIndex s capella withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · cases ok
  · cases ok; rfl

/-- Paying withdrawals removes balances and the queued partial withdrawals that were read.

It resets neither departure queue. -/
theorem withdrawals_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) :
    ∃ expected, getExpectedWithdrawals s capella = .ok expected ∧
      departureQueues electra t = departureQueues electra
        (updatePendingPartialWithdrawals s electra expected.processedPartialWithdrawalsCount) := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, expectedOk, _, _, applied⟩ := ok
  simp only [applyExpectedWithdrawals, notGloas, electra, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at applied
  obtain ⟨withdrawn, paid, indexed, moved, swept⟩ := applied
  refine ⟨expected, expectedOk, (withdrawalValidatorIndex_departureQueues electra swept).trans ?_⟩
  have kept := (withdrawalIndex_departureQueues electra moved).trans
    (applyWithdrawals_departureQueues electra early paid)
  simp only [departureQueues, Prod.mk.injEq] at kept
  obtain ⟨one, two, three, four, five⟩ := kept
  simp only [departureQueues, updatePendingPartialWithdrawals, Prod.mk.injEq]
  exact ⟨one, two, three, four, by rw [five]⟩

/-- From Electra and before Gloas, the execution part of a block keeps both departure queues.

It removes the queued partial withdrawals that its withdrawals read.

The payload step is read here: the shared block lemma gives only its frame and validators. -/
theorem blockExecution_departureQueues {fork : Fork}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ expected, getExpectedWithdrawals s (Nat.le_trans (by decide) electra) = .ok expected ∧
      departureQueues electra t = departureQueues electra
        (updatePendingPartialWithdrawals s electra expected.processedPartialWithdrawalsCount) := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  simp only [processBlockExecution, notGloas, capella, ↓reduceDIte, bind_ok_iff] at ok
  obtain ⟨middle, withdrawn, payload⟩ := ok
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
  obtain ⟨expected, expectedOk, frame⟩ := withdrawals_departureQueues electra early withdrawn
  exact ⟨expected, expectedOk, frame⟩

/-- The head of a block moves only the partial withdrawals among the departure queues. -/
theorem blockHead_departureQueues {fork : Fork} (electra : .pectra ≤ fork)
    {s headed executed revealed voted : BeaconState preset fork}
    {block : BeaconBlock preset fork} {before : fork < .hegota} {taken : Nat}
    (headedOk : processBlockHeader s block = .ok headed)
    (executedFrame : departureQueues electra executed =
      departureQueues electra (updatePendingPartialWithdrawals headed electra taken))
    (revealedOk : processRandao config checks executed block.body = .ok revealed)
    (votedOk : processEth1Data before revealed block.body = .ok voted) :
    departureQueues electra voted =
      departureQueues electra (updatePendingPartialWithdrawals s electra taken) := by
  have voteFrame := congrArg (departureQueues electra) (processEth1Data_eq votedOk).2.2
  change departureQueues electra voted = departureQueues electra revealed at voteFrame
  rw [voteFrame]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
  change departureQueues electra executed = _
  rw [executedFrame]
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
  rfl

/-- A slashing changes the departure queues only in its initial exit scheduling call. -/
theorem slashValidator_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    ∃ exited, initiateValidatorExit config s index = .ok exited ∧
      departureQueues electra t = departureQueues electra exited := by
  obtain ⟨exited, _, _, _, _, _, _, _, _, _, _, _, exitedOk, _, _, markedOk, _, _, _,
    lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at done
  subst done
  refine ⟨exited, exitedOk, ?_⟩
  rw [departureQueues_increase electra final, departureQueues_increase electra raised,
    departureQueues_decrease electra lowered]
  obtain ⟨_, rfl⟩ := setValidator_ok markedOk
  rfl

/-- A pass over pending consolidations keeps both departure queues. -/
theorem passPendingConsolidations_departureQueues {fork : Fork}
    (electra : .pectra ≤ fork) {epoch : Epoch} :
    ∀ {items : List PendingConsolidation} {s : BeaconState preset fork} {result},
      passPendingConsolidations epoch s items = .ok result →
      departureQueues electra result.1 = departureQueues electra s
  | [], _, _, ok => by cases ok; rfl
  | item :: rest, s, result, ok => by
    unfold passPendingConsolidations at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i recur
      cases ok
      exact (passPendingConsolidations_departureQueues electra recur :)
    split at ok
    · cases ok; rfl
    split at ok
    · cases ok
    split at ok
    · cases ok
    rename_i lowered loweredOk
    split at ok
    · cases ok
    rename_i raised raisedOk
    split at ok
    · cases ok
    rename_i recur
    cases ok
    exact (passPendingConsolidations_departureQueues electra recur).trans
      ((departureQueues_increase electra (liftAccessor_ok.mp raisedOk)).trans
        (departureQueues_decrease electra (liftAccessor_ok.mp loweredOk)))

/-- Queueing the excess balance keeps both departure queues. -/
theorem queueExcess_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rfl
  · cases ok; rfl

/-- Switching credentials cannot reset departure capacity. -/
theorem switchToCompounding_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, _, set, queued⟩ := ok
  rw [queueExcess_departureQueues electra queued]
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- Effective-balance changes happen after scheduling and leave its queue fields unchanged. -/
theorem effectiveBalances_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processEffectiveBalanceUpdates s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro before index after kept updated
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at updated
  obtain ⟨_, _, _, _, _, _, set⟩ := updated
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact kept

/-- Settling checkpoints keeps both departure queues. -/
theorem justification_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processJustificationAndFinalization s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]
    rfl

/-- The pending partial withdrawals that a payment read are the ones it removes from the front. -/
theorem updatePendingPartialWithdrawals_toList {fork : Fork} (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (count : ℕ) :
    ((updatePendingPartialWithdrawals state electra count).pendingPartialWithdrawals
      electra).data.toList = (state.pendingPartialWithdrawals electra).data.toList.drop count := by
  simp only [updatePendingPartialWithdrawals, Array.toList_extract, List.extract_eq_take_drop]
  exact List.take_of_length_le (by simp)

/-- The partials that the expected withdrawals read are the ones the plan counts. -/
theorem getExpectedWithdrawals_partials {fork : Fork} {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : getExpectedWithdrawals state capella = .ok expected) :
    ∃ (partials : Array Withdrawal) (next : WithdrawalIndex),
      getPendingPartialWithdrawals state electra (state.nextWithdrawalIndex capella) #[] =
        .ok (partials, next, expected.processedPartialWithdrawalsCount) := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold getExpectedWithdrawals at ok
  simp only [notGloas, electra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, rfl, ⟨partials, next, count⟩, partialsOk, _, rfl, _, _, rfl⟩ := ok
  exact ⟨partials, next, partialsOk⟩

end EthLib.Consensus
