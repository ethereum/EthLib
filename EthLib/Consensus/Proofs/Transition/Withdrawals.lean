module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.Withdrawals

/-!
# Proofs: withdrawals and changes of BLS credentials

A payload passes the withdrawal step only with exactly the withdrawals that the state expects.

The withdrawal step and a change of credentials keep the sizes of the registry and the balances.

A change of credentials checks the key and the signature of the change.

It then gives the validator credentials that name the address of the change.

A validator can withdraw its whole balance exactly when its credentials, epoch and balance allow it.

A full payload starts the next sweep after its last withdrawal, before the wrap at the registry.

Otherwise the next sweep starts one sweep after the start of the last one.
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
        (Cryptography.Hash.Sha256.hash32 ⟨signed.message.fromBlsPubkey.toArray⟩)[i.val + 1]) ∧
      (∃ (domain : Domain) (signingRoot : Root),
        computeDomain config DOMAIN_BLS_TO_EXECUTION_CHANGE
          (genesisValidatorsRoot := state.genesisValidatorsRoot) = .ok domain ∧
        computeSigningRoot signed.message domain = .ok signingRoot ∧
        checks.verify (packBytes signed.message.fromBlsPubkey) (packBytes signingRoot)
          (packBytes signed.signature) = true) ∧
      state.setValidator signed.message.validatorIndex
        { validator with
          withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } =
        .ok after := by
  unfold processBlsToExecutionChange at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨validator, found, _, blsPrefix, _, keyHash, domain, domainOk, signingRoot, rootOk, _,
    signature, set⟩ := computed
  exact ⟨validator, found, blsPrefix, keyHash, ⟨domain, signingRoot, domainOk, rootOk, signature⟩,
    set⟩

/-- After a change of BLS credentials, the validator has an execution address. -/
theorem processBlsToExecutionChange_credentials {state after : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    ∃ validator : Validator, getValidator after signed.message.validatorIndex = .ok validator ∧
      hasEth1WithdrawalCredential validator = true ∧
      credentialAddress validator.withdrawalCredentials = signed.message.toExecutionAddress := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact ⟨_, getValidator_setValidator_self set,
    hasEth1WithdrawalCredential_executionCredentials _ _,
    credentialAddress_executionCredentials _⟩

/-- A change of BLS credentials keeps the sizes. -/
theorem sameSizes_processBlsToExecutionChange {state after : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact sameSizes_setValidator set

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

/-- The expected withdrawals number at most the most per payload.

Their indices count up by one from the next withdrawal index of the state. -/
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
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
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

/-! ## The balances that the withdrawals lower -/

/-- The total amount that some withdrawals take from one validator. -/
def withdrawnFrom (withdrawals : Array Withdrawal) (index : ValidatorIndex) : Nat :=
  ((withdrawals.toList.filter fun withdrawal => withdrawal.validatorIndex = index).map
    fun withdrawal => withdrawal.amount.toNat).sum

/-- A withdrawal appended at the end adds its amount to the total of its validator only. -/
theorem withdrawnFrom_push (withdrawals : Array Withdrawal) (withdrawal : Withdrawal)
    (index : ValidatorIndex) :
    withdrawnFrom (withdrawals.push withdrawal) index = withdrawnFrom withdrawals index +
      if withdrawal.validatorIndex = index then withdrawal.amount.toNat else 0 := by
  unfold withdrawnFrom
  simp [Array.toList_push, List.filter_append]
  by_cases h : withdrawal.validatorIndex = index <;> simp [h]

/-- The balance left after some withdrawals, plus what they take, is the balance. -/
theorem getBalanceAfterWithdrawals_ok {state : BeaconState preset fork} {index : ValidatorIndex}
    {withdrawals : Array Withdrawal} {left : Gwei}
    (computed : getBalanceAfterWithdrawals state index withdrawals = .ok left) :
    ∃ balance, state.balances.data[index.toNat]? = some balance ∧
      withdrawnFrom withdrawals index + left.toNat = balance.toNat := by
  unfold getBalanceAfterWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨balance, found, withdrawn, folded, last⟩ := computed
  rw [← Array.foldlM_toList] at folded
  have sum : ∀ (l : List Withdrawal) (start total : Gwei),
      l.foldlM (fun sum withdrawal => if withdrawal.validatorIndex = index then
        liftArith (addChecked sum withdrawal.amount) else pure sum) start = .ok total →
      total.toNat = start.toNat +
        ((l.filter fun w => w.validatorIndex = index).map fun w => w.amount.toNat).sum := by
    intro l
    induction l with
    | nil =>
      intro start total h
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      simp [h]
    | cons w rest ih =>
      intro start total h
      rw [List.foldlM_cons, bind_ok_iff] at h
      obtain ⟨mid, step, h⟩ := h
      have := ih _ _ h
      by_cases same : w.validatorIndex = index
      · simp only [same, ↓reduceIte, liftArith, mapError_ok_iff, addChecked_ok_iff] at step
        simp [same]
        omega
      · simp only [same, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at step
        subst step
        simp [same]
        omega
  have total := sum _ _ _ folded
  unfold getBalance at found
  split at found
  · rename_i read
    simp only [Except.ok.injEq] at found
    subst found
    simp only [liftArith, mapError_ok_iff, subChecked_ok_iff] at last
    refine ⟨_, read, ?_⟩
    unfold withdrawnFrom
    simp at total
    omega
  · cases found

/-- An amount within the balance left keeps the total of a validator within its balance. -/
theorem appendWithdrawal_withdrawnFrom {state : BeaconState preset fork} {index : ValidatorIndex}
    {balance : Gwei} (found : state.balances.data[index.toNat]? = some balance)
    {prior withdrawals after : Array Withdrawal} {next next' : WithdrawalIndex}
    {target : ValidatorIndex} {address : ExecutionAddress} {amount left : Gwei}
    (bounded : withdrawnFrom (prior ++ withdrawals) index ≤ balance.toNat)
    (leftOk : getBalanceAfterWithdrawals state target (prior ++ withdrawals) = .ok left)
    (small : amount.toNat ≤ left.toNat)
    (computed : appendWithdrawal withdrawals next target address amount = .ok (after, next')) :
    withdrawnFrom (prior ++ after) index ≤ balance.toNat := by
  simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at computed
  obtain ⟨_, _, rfl, rfl⟩ := computed
  rw [Array.append_push, withdrawnFrom_push]
  split
  · rename_i same
    subst same
    obtain ⟨_, read, sum⟩ := getBalanceAfterWithdrawals_ok leftOk
    rw [found, Option.some.injEq] at read
    subst read
    dsimp only
    omega
  · simpa using bounded

/-- A difference that does not wrap is at most the first operand. -/
theorem toNat_sub_le_self {a b : UInt64} (le : b ≤ a) : (a - b).toNat ≤ a.toNat := by
  rw [UInt64.toNat_sub_of_le _ _ le]
  omega

/-- The minimum of a difference that does not wrap and any value is at most the first operand. -/
theorem toNat_min_sub_le_self {a b c : UInt64} (lt : b < a) : (min (a - b) c).toNat ≤ a.toNat := by
  have := toNat_sub_le_self (UInt64.le_of_lt lt)
  rw [UInt64.min_def]
  split
  · exact this
  · have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp ‹_›)
    omega

/-- The loop of the queued partial withdrawals keeps the total of a validator within its balance. -/
theorem getPendingPartialWithdrawals_loop_withdrawnFrom {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} {index : ValidatorIndex}
    {balance : Gwei} (found : state.balances.data[index.toNat]? = some balance) :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    withdrawnFrom (prior ++ withdrawals) index ≤ balance.toNat →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    withdrawnFrom (prior ++ result.1) index ≤ balance.toNat
  | [], _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact bounded
  | pending :: rest, _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact bounded
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, left, leftOk, computed⟩ := computed
      split at computed
      · rename_i eligible
        simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
        simp only [isEligibleForPartialWithdrawals, Bool.and_eq_true, decide_eq_true_eq]
          at eligible
        exact getPendingPartialWithdrawals_loop_withdrawnFrom found rest _ _ _
          (appendWithdrawal_withdrawnFrom found bounded (liftAccessor_ok.mp leftOk)
            (toNat_min_sub_le_self eligible.2)
            appendedOk) rest'
      · exact getPendingPartialWithdrawals_loop_withdrawnFrom found rest _ _ _ bounded computed

/-- The loop of the sweep keeps the total of a validator within its balance. -/
theorem getValidatorsSweepWithdrawals_loop_withdrawnFrom {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {count limit : Nat} {index : ValidatorIndex}
    {balance : Gwei} (found : state.balances.data[index.toNat]? = some balance) :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (target : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    withdrawnFrom (prior ++ withdrawals) index ≤ balance.toNat →
    getValidatorsSweepWithdrawals.loop state prior epoch count limit visits withdrawals next target
      processed = .ok result →
    withdrawnFrom (prior ++ result.1) index ≤ balance.toNat
  | 0, _, _, _, _, _, bounded, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact bounded
  | visits + 1, _, _, _, _, _, bounded, computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact bounded
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, left, leftOk, computed⟩ := computed
      have leftOk := liftAccessor_ok.mp leftOk
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
        exact getValidatorsSweepWithdrawals_loop_withdrawnFrom found visits _ _ _ _
          (appendWithdrawal_withdrawnFrom found bounded leftOk (Nat.le_refl _) appendedOk) rest
      · split at computed
        · rename_i excess
          simp only [isPartiallyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq]
            at excess
          simp only [bind_ok_iff, liftAccessor_ok] at computed
          obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
          exact getValidatorsSweepWithdrawals_loop_withdrawnFrom found visits _ _ _ _
            (appendWithdrawal_withdrawnFrom found bounded leftOk
              (toNat_sub_le_self (UInt64.le_of_lt excess.2)) appendedOk) rest
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left']
            at computed
          obtain ⟨_, _, rest⟩ := computed
          exact getValidatorsSweepWithdrawals_loop_withdrawnFrom found visits _ _ _ _ bounded rest

/-- A withdrawal at the front adds its amount to the total of its validator only. -/
theorem withdrawnFrom_cons (withdrawal : Withdrawal) (rest : List Withdrawal)
    (index : ValidatorIndex) :
    withdrawnFrom (withdrawal :: rest).toArray index =
      (if withdrawal.validatorIndex = index then withdrawal.amount.toNat else 0) +
        withdrawnFrom rest.toArray index := by
  unfold withdrawnFrom
  by_cases h : withdrawal.validatorIndex = index <;> simp [h]

/-- Before Gloas, withdrawals within a balance lower it by exactly their total. -/
theorem applyWithdrawals_balance {index : ValidatorIndex} (before : fork < .glamsterdam) :
    ∀ (withdrawals : List Withdrawal) (state after : BeaconState preset fork) (balance : Gwei),
    withdrawals.foldlM applyWithdrawal state = .ok after →
    state.balances.data[index.toNat]? = some balance →
    withdrawnFrom withdrawals.toArray index ≤ balance.toNat →
    (after.balances.data[index.toNat]?).map UInt64.toNat =
      some (balance.toNat - withdrawnFrom withdrawals.toArray index)
  | [], state, after, balance, computed, found, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp [found, withdrawnFrom]
  | withdrawal :: rest, state, after, balance, computed, found, bounded => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, computed⟩ := computed
    have noGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    unfold applyWithdrawal at step
    simp only [noGloas, false_and, ↓reduceDIte] at step
    simp only [decreaseBalance, bind_ok_iff] at step
    obtain ⟨old, oldOk, set⟩ := step
    obtain ⟨inside, rfl⟩ := setBalance_ok set
    rw [withdrawnFrom_cons] at bounded ⊢
    by_cases same : withdrawal.validatorIndex = index
    · simp only [same, ↓reduceIte] at bounded ⊢
      subst same
      simp only [getBalance, found, Except.ok.injEq] at oldOk
      subst oldOk
      have inRange := (Array.getElem?_eq_some_iff.mp found).1
      rw [applyWithdrawals_balance before rest _ after (saturatingSub balance withdrawal.amount)
        computed (by simp [BeaconState.putBalance, inRange])
        (by rw [toNat_saturatingSub]; omega), toNat_saturatingSub]
      congr 1
      omega
    · simp only [same, ↓reduceIte, Nat.zero_add] at bounded ⊢
      have apart : withdrawal.validatorIndex.toNat ≠ index.toNat :=
        fun h => same (UInt64.toNat_inj.mp h)
      exact applyWithdrawals_balance before rest _ after balance computed
        (by simp [BeaconState.putBalance, apart, found]) bounded

/-- Before Gloas, only the withdrawals themselves change the balances. -/
theorem applyExpectedWithdrawals_balances {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals} (before : fork < .glamsterdam)
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    ∃ applied, applyWithdrawals state expected.withdrawals = .ok applied ∧
      after.balances = applied.balances := by
  have noGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  unfold applyExpectedWithdrawals at computed
  simp only [noGloas, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, swept, sweptOk, last⟩ := computed
  refine ⟨applied, appliedOk, ?_⟩
  have one : indexed.balances = applied.balances := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      rfl
    · cases indexedOk
      rfl
  have two : swept.balances = indexed.balances := by
    simp only [pure, Except.pure, Except.ok.injEq] at sweptOk
    subst sweptOk
    split <;> rfl
  unfold updateNextWithdrawalValidatorIndex at last
  simp only [bind_ok_iff] at last
  obtain ⟨_, _, last⟩ := last
  split at last
  · cases last
  · cases last
    rw [← one, ← two]

/-- Before Gloas, the expected withdrawals take from a validator at most its balance. -/
theorem getExpectedWithdrawals_withdrawnFrom {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals} (before : fork < .glamsterdam)
    (computed : getExpectedWithdrawals state capella = .ok expected) {index : ValidatorIndex}
    {balance : Gwei} (found : state.balances.data[index.toNat]? = some balance) :
    withdrawnFrom expected.withdrawals index ≤ balance.toNat := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, _⟩, buildersOk, ⟨partials, index2, _⟩, partialsOk,
    ⟨buildersSweep, index3, _⟩, buildersSweepOk, ⟨sweep, index4, _⟩, sweepOk, rfl⟩ := computed
  have noGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [noGloas, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at buildersOk buildersSweepOk
  obtain ⟨rfl, rfl, _⟩ := buildersOk
  obtain ⟨rfl, rfl, _⟩ := buildersSweepOk
  have two : withdrawnFrom (#[] ++ partials) index ≤ balance.toNat := by
    split at partialsOk
    · unfold getPendingPartialWithdrawals at partialsOk
      simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
      obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
      exact getPendingPartialWithdrawals_loop_withdrawnFrom found _ _ _ _
        (by simp [withdrawnFrom]) loopOk
    · simp only [Except.ok.injEq, Prod.mk.injEq] at partialsOk
      obtain ⟨rfl, rfl, rfl⟩ := partialsOk
      simp [withdrawnFrom]
  unfold getValidatorsSweepWithdrawals at sweepOk
  simp only [bind_ok_iff, ensure_ok_iff] at sweepOk
  obtain ⟨_, _, loopOk⟩ := sweepOk
  exact getValidatorsSweepWithdrawals_loop_withdrawnFrom found _ _ _ _ _ (by simpa using two)
    loopOk

/-- Before Gloas, the payload of a withdrawal step never takes more than a balance. -/
theorem processWithdrawals_withdrawnFrom {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (before : fork < .glamsterdam)
    (computed : processWithdrawals state capella payload = .ok after) {index : ValidatorIndex}
    {balance : Gwei} (found : state.balances.data[index.toNat]? = some balance) :
    withdrawnFrom ((payload before).withdrawals capella).data index ≤ balance.toNat := by
  obtain ⟨expected, expectedOk, carried, -⟩ := processWithdrawals_expected before computed
  rw [carried]
  exact getExpectedWithdrawals_withdrawnFrom before expectedOk found

/-- Before Gloas, the withdrawal step lowers each balance by exactly what the payload takes from it.

The subtraction does not stop at zero, since the payload never takes more than the balance. -/
theorem processWithdrawals_balance {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (before : fork < .glamsterdam)
    (computed : processWithdrawals state capella payload = .ok after) {index : ValidatorIndex}
    {balance : Gwei} (found : state.balances.data[index.toNat]? = some balance) :
    (after.balances.data[index.toNat]?).map UInt64.toNat =
      some (balance.toNat - withdrawnFrom ((payload before).withdrawals capella).data index) := by
  obtain ⟨expected, expectedOk, carried, appliedOk⟩ := processWithdrawals_expected before computed
  have bounded := getExpectedWithdrawals_withdrawnFrom before expectedOk found
  obtain ⟨applied, appliedOk, same⟩ := applyExpectedWithdrawals_balances before appliedOk
  unfold applyWithdrawals at appliedOk
  rw [← Array.foldlM_toList] at appliedOk
  have lowered := applyWithdrawals_balance before _ _ _ _ appliedOk found
    (by simpa using bounded)
  rw [carried, same]
  simpa using lowered

/-! ## The next sweep -/

/-- A full payload starts the next sweep after the validator of its last withdrawal.

The index is that before the sweep wraps around the registry.

An overflow of the index is an error. -/
theorem nextSweepStart_of_full {state : BeaconState preset fork} {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal} {last : Withdrawal} (final : withdrawals.back? = some last)
    (full : withdrawals.size = preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat) :
    nextSweepStart state capella withdrawals = liftArith (addChecked last.validatorIndex 1) := by
  simp [nextSweepStart, final, full]

/-- A payload that is not full starts the next sweep one sweep after the start of this one.

The index is that before the sweep wraps around the registry.

An overflow of the index is an error. -/
theorem nextSweepStart_of_ne {state : BeaconState preset fork} {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (notFull : withdrawals.size ≠ preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat) :
    nextSweepStart state capella withdrawals = liftArith
      (addChecked (state.nextWithdrawalValidatorIndex capella)
        preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP) := by
  unfold nextSweepStart
  split
  · simp [notFull]
  · rfl

/-! ## Full withdrawals -/

/-- A validator can withdraw its whole balance exactly under three conditions.

Its credentials name an address, it is withdrawable by the epoch, and its balance is not zero. -/
theorem isFullyWithdrawableValidator_eq_true_iff {fork : Base.Fork} {validator : Validator}
    {balance : Gwei} {epoch : Epoch} :
    isFullyWithdrawableValidator fork validator balance epoch = true ↔
      hasWithdrawalAddress fork validator = true ∧ validator.withdrawableEpoch ≤ epoch ∧
        0 < balance := by
  simp [isFullyWithdrawableValidator, and_assoc]

/-! ## The latest block header -/

/-- The sweep of validators does not read the latest block header. -/
theorem getValidatorsSweepWithdrawals_loop_latestBlockHeader {state : BeaconState preset fork}
    {header : BeaconBlockHeader} {prior : Array Withdrawal} {epoch : Epoch} {count limit : Nat} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat),
    getValidatorsSweepWithdrawals.loop { state with latestBlockHeader := header } prior epoch count
        limit visits withdrawals next index processed =
      getValidatorsSweepWithdrawals.loop state prior epoch count limit visits withdrawals next index
        processed
  | 0, _, _, _, _ => rfl
  | visits + 1, withdrawals, next, index, processed => by
    simp only [getValidatorsSweepWithdrawals.loop,
      getValidatorsSweepWithdrawals_loop_latestBlockHeader visits]
    rfl

/-- The queued partial withdrawals do not read the latest block header. -/
theorem getPendingPartialWithdrawals_loop_latestBlockHeader {state : BeaconState preset fork}
    {header : BeaconBlockHeader} {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat),
    getPendingPartialWithdrawals.loop { state with latestBlockHeader := header } prior epoch limit
        queue withdrawals next processed =
      getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed
  | [], _, _, _ => rfl
  | pending :: rest, withdrawals, next, processed => by
    simp only [getPendingPartialWithdrawals.loop,
      getPendingPartialWithdrawals_loop_latestBlockHeader rest]
    rfl

/-- Before Gloas, the withdrawals that a state expects do not read its latest block header. -/
theorem getExpectedWithdrawals_latestBlockHeader {state : BeaconState preset fork}
    {header : BeaconBlockHeader} {capella : .shapella ≤ fork} (before : fork < .glamsterdam) :
    getExpectedWithdrawals { state with latestBlockHeader := header } capella =
      getExpectedWithdrawals state capella := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getExpectedWithdrawals, notGloas, ↓reduceDIte, getPendingPartialWithdrawals,
    getValidatorsSweepWithdrawals, getPendingPartialWithdrawals_loop_latestBlockHeader,
    getValidatorsSweepWithdrawals_loop_latestBlockHeader]
  rfl

end EthLib.Consensus
