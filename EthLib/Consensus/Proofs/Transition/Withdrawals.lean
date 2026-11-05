module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.Withdrawals

/-!
# Proofs: withdrawals and changes of BLS credentials

A payload passes the withdrawal step only with exactly the withdrawals that the state expects.

The withdrawal step and a change of credentials keep the sizes of the registry and the balances.

A change of credentials checks the key and the signature of the change.

It then gives the validator credentials that name the address of the change.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## Credentials that name an address -/

/-- The new credentials start with the execution address prefix. -/
theorem executionCredentials_prefix (address : ExecutionAddress) :
    (executionCredentials address)[0] = ETH1_ADDRESS_WITHDRAWAL_PREFIX[0] := by
  simp [executionCredentials]

/-- The address that the new credentials name is the address they were built from. -/
theorem credentialAddress_executionCredentials (address : ExecutionAddress) :
    credentialAddress (executionCredentials address) = address := by
  ext i hi
  simp [credentialAddress, executionCredentials]

/-- A validator with the new credentials has an execution address. -/
theorem hasEth1WithdrawalCredential_executionCredentials (validator : Validator)
    (address : ExecutionAddress) :
    hasEth1WithdrawalCredential
      { validator with withdrawalCredentials := executionCredentials address } = true := by
  simp [hasEth1WithdrawalCredential, executionCredentials_prefix]

/-! ## Changes of BLS credentials -/

/-- What a change of BLS credentials checks, and the state it gives.

The validator had BLS credentials that commit to the key of the change.

The key signed the change.

The validator now has the credentials that name the address of the change. -/
theorem processBlsToExecutionChange_ok {state after : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    ∃ validator : Validator, getValidator state signed.message.validatorIndex = .ok validator ∧
      validator.withdrawalCredentials[0] = BLS_WITHDRAWAL_PREFIX[0] ∧
      (∀ i : Fin 31, validator.withdrawalCredentials[i.val + 1] =
        (sha256Bytes32 ⟨signed.message.fromBlsPubkey.toArray⟩)[i.val + 1]) ∧
      (∃ (domain : Domain) (signingRoot : Root),
        computeDomain config DOMAIN_BLS_TO_EXECUTION_CHANGE
          (genesisValidatorsRoot := state.genesisValidatorsRoot) = .ok domain ∧
        computeSigningRoot signed.message domain = .ok signingRoot ∧
        checks.verify (packBytes signed.message.fromBlsPubkey) (packBytes signingRoot)
          (packBytes signed.signature) = true) ∧
      after = state.setValidator signed.message.validatorIndex.toNat
        { validator with
          withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } := by
  unfold processBlsToExecutionChange at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, blsPrefix, _, keyHash, domain, domainOk, signingRoot, rootOk, _,
    signature, rfl⟩ := computed
  exact ⟨validator, found, blsPrefix, keyHash, ⟨domain, signingRoot, domainOk, rootOk, signature⟩,
    rfl⟩

/-- After a change of BLS credentials, the validator has an execution address. -/
theorem processBlsToExecutionChange_credentials {state after : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    ∃ validator : Validator, getValidator after signed.message.validatorIndex = .ok validator ∧
      hasEth1WithdrawalCredential validator = true ∧
      credentialAddress validator.withdrawalCredentials = signed.message.toExecutionAddress := by
  obtain ⟨validator, found, _, _, _, rfl⟩ := processBlsToExecutionChange_ok computed
  exact ⟨_, getValidator_setValidator_self found _,
    hasEth1WithdrawalCredential_executionCredentials _ _,
    credentialAddress_executionCredentials _⟩

/-- A change of BLS credentials keeps the sizes. -/
theorem sameSizes_processBlsToExecutionChange {state after : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, _, _, _, rfl⟩ := processBlsToExecutionChange_ok computed
  exact sameSizes_setValidator _ _ _

/-! ## The withdrawals that a state expects -/

/-- Withdrawals whose indices count up by one from a start. -/
def ConsecutiveFrom (start : Nat) (withdrawals : Array Withdrawal) : Prop :=
  ∀ (i : Nat) (h : i < withdrawals.size), withdrawals[i].index.toNat = start + i

theorem consecutiveFrom_empty (start : Nat) : ConsecutiveFrom start #[] :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem ConsecutiveFrom.append {start : Nat} {first second : Array Withdrawal}
    (one : ConsecutiveFrom start first) (two : ConsecutiveFrom (start + first.size) second) :
    ConsecutiveFrom start (first ++ second) := by
  intro i h
  by_cases inFirst : i < first.size
  · rw [Array.getElem_append_left inFirst]
    exact one i inFirst
  · rw [Array.getElem_append_right (Nat.le_of_not_lt inFirst)]
    rw [Array.size_append] at h
    rw [two (i - first.size) (by omega)]
    omega

/-- What a loop of the withdrawals keeps.

The prior withdrawals and those of the loop stay within a limit.

The withdrawals of the loop count up from a start, and the next index follows the last. -/
def LoopRun (limit : Nat) (prior : Array Withdrawal) (start : Nat) (withdrawals : Array Withdrawal)
    (next : WithdrawalIndex) : Prop :=
  prior.size + withdrawals.size ≤ limit ∧ ConsecutiveFrom start withdrawals ∧
    next.toNat = start + withdrawals.size

theorem loopRun_start {limit : Nat} {prior : Array Withdrawal} {next : WithdrawalIndex}
    (fits : prior.size ≤ limit) : LoopRun limit prior next.toNat #[] next :=
  ⟨by simpa using fits, consecutiveFrom_empty _, by simp⟩

/-- A withdrawal appended below the limit keeps what a loop keeps. -/
theorem appendWithdrawal_run {limit start : Nat} {prior withdrawals after : Array Withdrawal}
    {next after' : WithdrawalIndex} {index : ValidatorIndex} {address : ExecutionAddress}
    {amount : Gwei} (run : LoopRun limit prior start withdrawals next)
    (room : ¬ limit ≤ prior.size + withdrawals.size)
    (computed : appendWithdrawal withdrawals next index address amount = .ok (after, after')) :
    LoopRun limit prior start after after' := by
  simp only [appendWithdrawal, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff,
    pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨following, ⟨_, followingNat⟩, rfl, rfl⟩ := computed
  obtain ⟨_, consecutive, nextNat⟩ := run
  have one : (1 : UInt64).toNat = 1 := rfl
  refine ⟨by simp; omega, ?_, by simp; omega⟩
  intro i h
  simp only [Array.size_push] at h
  by_cases old : i < withdrawals.size
  · rw [Array.getElem_push_lt old]
    exact consecutive i old
  · have : i = withdrawals.size := by omega
    subst this
    simp [nextNat]

theorem getBuilderWithdrawals_loop_run {prior : Array Withdrawal} {limit : UInt64} {start : Nat} :
    ∀ (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    LoopRun limit.toNat prior start withdrawals next →
    getBuilderWithdrawals.loop prior limit queue withdrawals next processed = .ok result →
    LoopRun limit.toNat prior start result.1 result.2.1
  | [], _, _, _, _, run, computed => by
    simp only [getBuilderWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact run
  | _ :: rest, _, _, _, _, run, computed => by
    simp only [getBuilderWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact run
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
      exact getBuilderWithdrawals_loop_run rest _ _ _ (appendWithdrawal_run run ‹_› appendedOk)
        rest'

theorem getBuildersSweepWithdrawals_loop_run {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {prior : Array Withdrawal} {epoch : Epoch} {count : Nat}
    {limit : UInt64} {start : Nat} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    LoopRun limit.toNat prior start withdrawals next →
    getBuildersSweepWithdrawals.loop state gloas prior epoch count limit visits withdrawals next
      index processed = .ok result →
    LoopRun limit.toNat prior start result.1 result.2.1
  | 0, _, _, _, _, _, run, computed => by
    simp only [getBuildersSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact run
  | visits + 1, _, _, _, _, _, run, computed => by
    simp only [getBuildersSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact run
    · rename_i room
      simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
        exact getBuildersSweepWithdrawals_loop_run visits _ _ _ _
          (appendWithdrawal_run run room appendedOk) rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
        obtain ⟨_, _, rest⟩ := computed
        exact getBuildersSweepWithdrawals_loop_run visits _ _ _ _ run rest

theorem getPendingPartialWithdrawals_loop_run {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {limit start : Nat} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    LoopRun limit prior start withdrawals next →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    LoopRun limit prior start result.1 result.2.1
  | [], _, _, _, _, run, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact run
  | _ :: rest, _, _, _, _, run, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact run
    · rename_i stop
      have room := fun h => stop (.inr h)
      simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
        exact getPendingPartialWithdrawals_loop_run rest _ _ _
          (appendWithdrawal_run run room appendedOk) rest'
      · exact getPendingPartialWithdrawals_loop_run rest _ _ _ run computed

theorem getValidatorsSweepWithdrawals_loop_run {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {count limit start : Nat} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    LoopRun limit prior start withdrawals next →
    getValidatorsSweepWithdrawals.loop state prior epoch count limit visits withdrawals next index
      processed = .ok result →
    LoopRun limit prior start result.1 result.2.1
  | 0, _, _, _, _, _, run, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact run
  | visits + 1, _, _, _, _, _, run, computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact run
    · rename_i room
      simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
        exact getValidatorsSweepWithdrawals_loop_run visits _ _ _ _
          (appendWithdrawal_run run room appendedOk) rest
      · split at computed
        · simp only [bind_ok_iff, liftAccessor_ok] at computed
          obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
          exact getValidatorsSweepWithdrawals_loop_run visits _ _ _ _
            (appendWithdrawal_run run room appendedOk) rest
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left']
            at computed
          obtain ⟨_, _, rest⟩ := computed
          exact getValidatorsSweepWithdrawals_loop_run visits _ _ _ _ run rest

/-- The limit of a loop that leaves one place in the payload. -/
theorem room_of_subChecked {limit : UInt64}
    (computed : liftAccessor (liftArith (subChecked preset.MAX_WITHDRAWALS_PER_PAYLOAD 1)) =
      .ok limit) : limit.toNat + 1 = preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat := by
  simp only [liftAccessor_ok, liftArith, mapError_ok_iff, subChecked_ok_iff] at computed
  simp at computed
  omega

theorem LoopRun.weaken {limit limit' start : Nat} {prior withdrawals : Array Withdrawal}
    {next : WithdrawalIndex} (run : LoopRun limit prior start withdrawals next)
    (le : limit ≤ limit') : LoopRun limit' prior start withdrawals next :=
  ⟨Nat.le_trans run.1 le, run.2⟩

theorem getBuilderWithdrawals_run {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {start : WithdrawalIndex} {prior withdrawals : Array Withdrawal}
    {next : WithdrawalIndex} {processed : Nat}
    (computed :
      getBuilderWithdrawals state gloas start prior = .ok (withdrawals, next, processed)) :
    LoopRun preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat prior start.toNat withdrawals next := by
  unfold getBuilderWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨limit, limitOk, _, fits, loopOk⟩ := computed
  have room := room_of_subChecked limitOk
  exact (getBuilderWithdrawals_loop_run _ _ _ _ (loopRun_start fits) loopOk).weaken (by omega)

theorem getBuildersSweepWithdrawals_run {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {start : WithdrawalIndex} {prior withdrawals : Array Withdrawal}
    {next : WithdrawalIndex} {processed : Nat}
    (computed : getBuildersSweepWithdrawals state gloas start prior =
      .ok (withdrawals, next, processed)) :
    LoopRun preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat prior start.toNat withdrawals next := by
  unfold getBuildersSweepWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨limit, limitOk, _, fits, loopOk⟩ := computed
  have room := room_of_subChecked limitOk
  exact (getBuildersSweepWithdrawals_loop_run _ _ _ _ _ (loopRun_start fits) loopOk).weaken
    (by omega)

theorem getPendingPartialWithdrawals_run {state : BeaconState preset fork}
    {electra : .pectra ≤ fork} {start : WithdrawalIndex} {prior withdrawals : Array Withdrawal}
    {next : WithdrawalIndex} {processed : Nat}
    (computed : getPendingPartialWithdrawals state electra start prior =
      .ok (withdrawals, next, processed)) :
    LoopRun preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat prior start.toNat withdrawals next := by
  unfold getPendingPartialWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨limit, limitOk, _, fits, loopOk⟩ := computed
  have room := room_of_subChecked limitOk
  exact (getPendingPartialWithdrawals_loop_run _ _ _ _ (loopRun_start fits) loopOk).weaken
    (by omega)

theorem getValidatorsSweepWithdrawals_run {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} {start : WithdrawalIndex} {prior withdrawals : Array Withdrawal}
    {next : WithdrawalIndex} {processed : Nat}
    (computed : getValidatorsSweepWithdrawals state capella start prior =
      .ok (withdrawals, next, processed)) :
    LoopRun preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat prior start.toNat withdrawals next := by
  unfold getValidatorsSweepWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, fits, loopOk⟩ := computed
  exact getValidatorsSweepWithdrawals_loop_run _ _ _ _ _ (loopRun_start (Nat.le_of_lt fits))
    loopOk

/-- A part of the expected withdrawals counts up from its start, and the next index follows. -/
theorem part_run {limit : Nat} {prior withdrawals : Array Withdrawal}
    {start next : WithdrawalIndex} (run : LoopRun limit prior start.toNat withdrawals next) :
    ConsecutiveFrom start.toNat withdrawals ∧ next.toNat = start.toNat + withdrawals.size :=
  run.2

/-- The parts of the expected withdrawals, in order, with the sizes of the last part. -/
theorem getExpectedWithdrawals_run {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    expected.withdrawals.size ≤ preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat ∧
      ConsecutiveFrom (state.nextWithdrawalIndex capella).toNat expected.withdrawals := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, _⟩, buildersOk, ⟨partials, index2, _⟩, partialsOk,
    ⟨buildersSweep, index3, _⟩, buildersSweepOk, ⟨sweep, index4, _⟩, sweepOk, rfl⟩ := computed
  have one : ConsecutiveFrom (state.nextWithdrawalIndex capella).toNat builders ∧
      index1.toNat = (state.nextWithdrawalIndex capella).toNat + builders.size := by
    split at buildersOk
    · exact part_run (getBuilderWithdrawals_run buildersOk)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at buildersOk
      obtain ⟨rfl, rfl, rfl⟩ := buildersOk
      exact ⟨consecutiveFrom_empty _, by simp⟩
  have two : ConsecutiveFrom index1.toNat partials ∧
      index2.toNat = index1.toNat + partials.size := by
    split at partialsOk
    · exact part_run (getPendingPartialWithdrawals_run partialsOk)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at partialsOk
      obtain ⟨rfl, rfl, rfl⟩ := partialsOk
      exact ⟨consecutiveFrom_empty _, by simp⟩
  have three : ConsecutiveFrom index2.toNat buildersSweep ∧
      index3.toNat = index2.toNat + buildersSweep.size := by
    split at buildersSweepOk
    · exact part_run (getBuildersSweepWithdrawals_run buildersSweepOk)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at buildersSweepOk
      obtain ⟨rfl, rfl, rfl⟩ := buildersSweepOk
      exact ⟨consecutiveFrom_empty _, by simp⟩
  have four := getValidatorsSweepWithdrawals_run sweepOk
  refine ⟨by have := four.1; simp only [Array.size_append] at this ⊢; omega, ?_⟩
  refine ((one.1.append ?_).append ?_).append ?_
  · rw [← one.2]
    exact two.1
  · rw [Array.size_append, ← Nat.add_assoc, ← one.2, ← two.2]
    exact three.1
  · rw [Array.size_append, Array.size_append, ← Nat.add_assoc, ← Nat.add_assoc, ← one.2,
      ← two.2, ← three.2]
    exact four.2.1

/-- The state expects at most the most withdrawals per payload. -/
theorem getExpectedWithdrawals_size {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    expected.withdrawals.size ≤ preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat :=
  (getExpectedWithdrawals_run computed).1

/-- The expected withdrawals count up by one from the next withdrawal index of the state. -/
theorem getExpectedWithdrawals_index {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) (i : Nat)
    (h : i < expected.withdrawals.size) :
    expected.withdrawals[i].index.toNat = (state.nextWithdrawalIndex capella).toNat + i :=
  (getExpectedWithdrawals_run computed).2 i h

/-! ## Processing the withdrawals -/

/-- Applying one withdrawal keeps the sizes. -/
theorem sameSizes_applyWithdrawal {state after : BeaconState preset fork}
    {withdrawal : Withdrawal} (computed : applyWithdrawal state withdrawal = .ok after) :
    SameSizes state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  · exact sameSizes_decreaseBalance computed

/-- Applying withdrawals keeps the sizes. -/
theorem sameSizes_applyWithdrawals {state after : BeaconState preset fork}
    {withdrawals : Array Withdrawal} (computed : applyWithdrawals state withdrawals = .ok after) :
    SameSizes state after := by
  unfold applyWithdrawals at computed
  rw [← Array.foldlM_toList] at computed
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ holds ok => holds.trans (sameSizes_applyWithdrawal ok)) (SameSizes.refl state)
    computed

/-- Moving the next withdrawal index keeps the sizes and the recorded withdrawals. -/
theorem updateNextWithdrawalIndex_frame {state after : BeaconState preset fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) :
    SameSizes state after ∧
      after.payloadExpectedWithdrawals = state.payloadExpectedWithdrawals := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · cases computed
    exact ⟨SameSizes.refl state, rfl⟩

/-- Moving the start of the next sweep keeps the sizes and the recorded withdrawals. -/
theorem updateNextWithdrawalValidatorIndex_frame {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    SameSizes state after ∧
      after.payloadExpectedWithdrawals = state.payloadExpectedWithdrawals := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- Moving the start of the next sweep of builders keeps the sizes and the recorded withdrawals.
-/
theorem updateNextWithdrawalBuilderIndex_frame {state after : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    SameSizes state after ∧
      after.payloadExpectedWithdrawals = state.payloadExpectedWithdrawals := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact ⟨SameSizes.refl state, rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- Applying the expected withdrawals keeps the sizes.

From Gloas the state then records exactly the withdrawals applied. -/
theorem applyExpectedWithdrawals_frame {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    SameSizes state after ∧ ∀ gloas : .glamsterdam ≤ fork,
      (after.payloadExpectedWithdrawals gloas).data = expected.withdrawals := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, swept, sweptOk, last⟩ := computed
  have one := sameSizes_applyWithdrawals appliedOk
  have two := updateNextWithdrawalIndex_frame indexedOk
  have four := updateNextWithdrawalValidatorIndex_frame last
  have three : SameSizes indexed swept ∧ ∀ gloas : .glamsterdam ≤ fork,
      (swept.payloadExpectedWithdrawals gloas).data = expected.withdrawals := by
    split at sweptOk
    · have frame := updateNextWithdrawalBuilderIndex_frame sweptOk
      refine ⟨SameSizes.trans ?_ frame.1, fun _ => ?_⟩
      · split <;> exact ⟨rfl, rfl⟩
      · rw [frame.2]
        split <;> rfl
    · rename_i before
      simp only [pure, Except.pure, Except.ok.injEq] at sweptOk
      subst sweptOk
      refine ⟨?_, fun gloas => absurd gloas before⟩
      split <;> exact ⟨rfl, rfl⟩
  refine ⟨one.trans (two.1.trans (three.1.trans four.1)), fun gloas => ?_⟩
  rw [four.2]
  exact three.2 gloas

/-- From Gloas, a block whose parent has no payload changes nothing. -/
theorem processWithdrawals_of_parentEmpty {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} (payload : Until .glamsterdam fork (ExecutionPayload preset fork))
    (gloas : .glamsterdam ≤ fork) (empty : isParentBlockFull state gloas = false) :
    processWithdrawals state capella payload = .ok state := by
  unfold processWithdrawals
  split
  · simp only [empty, Bool.false_eq_true, ↓reduceIte]
    rfl
  · contradiction

/-- Before Gloas, a payload passes the withdrawal step only with the expected withdrawals.

The step then applies them. -/
theorem processWithdrawals_expected {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (before : fork < .glamsterdam)
    (computed : processWithdrawals state capella payload = .ok after) :
    ∃ expected : ExpectedWithdrawals, getExpectedWithdrawals state capella = .ok expected ∧
      ((payload before).withdrawals capella).data = expected.withdrawals ∧
      applyExpectedWithdrawals state capella expected = .ok after := by
  unfold processWithdrawals at computed
  split at computed
  · exact absurd ‹.glamsterdam ≤ fork› (Nat.not_le_of_lt before)
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨expected, found, _, carried, applied⟩ := computed
    exact ⟨expected, found, carried, applied⟩

/-- From Gloas, after a parent with its payload, the step applies the expected withdrawals.

The state then records them for the next payload. -/
theorem processWithdrawals_recorded {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (gloas : .glamsterdam ≤ fork) (full : isParentBlockFull state gloas = true)
    (computed : processWithdrawals state capella payload = .ok after) :
    ∃ expected : ExpectedWithdrawals, getExpectedWithdrawals state capella = .ok expected ∧
      applyExpectedWithdrawals state capella expected = .ok after ∧
      (after.payloadExpectedWithdrawals gloas).data = expected.withdrawals := by
  unfold processWithdrawals at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨expected, found, applied⟩ := computed
    exact ⟨expected, found, applied, (applyExpectedWithdrawals_frame applied).2 gloas⟩
  · contradiction

/-- The withdrawal step keeps the sizes. -/
theorem sameSizes_processWithdrawals {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    SameSizes state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact (applyExpectedWithdrawals_frame applied).1
    · cases computed
      exact SameSizes.refl state
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact (applyExpectedWithdrawals_frame applied).1

end EthLib.Consensus
