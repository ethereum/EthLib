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

/-! ## Processing the withdrawals -/

/-- Applying withdrawals keeps the sizes. -/
theorem sameSizes_applyWithdrawals {state after : BeaconState preset fork}
    {withdrawals : Array Withdrawal} (computed : applyWithdrawals state withdrawals = .ok after) :
    SameSizes state after := by
  unfold applyWithdrawals at computed
  rw [← Array.foldlM_toList] at computed
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ holds ok => holds.trans (sameSizes_decreaseBalance ok)) (SameSizes.refl state)
    computed

/-- Moving the next withdrawal index keeps the sizes. -/
theorem sameSizes_updateNextWithdrawalIndex {state after : BeaconState preset fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) :
    SameSizes state after := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  · cases computed
    exact SameSizes.refl state

/-- Moving the start of the next sweep keeps the sizes. -/
theorem sameSizes_updateNextWithdrawalValidatorIndex {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    SameSizes state after := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    exact ⟨rfl, rfl⟩

/-- A payload passes the withdrawal step only before Gloas.

It must then carry exactly the withdrawals that the state expects. -/
theorem processWithdrawals_expected {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : ExecutionPayload preset fork}
    (computed : processWithdrawals state capella payload = .ok after) :
    fork < .glamsterdam ∧ ∃ expected : ExpectedWithdrawals,
      getExpectedWithdrawals state capella = .ok expected ∧
      (payload.withdrawals capella).data = expected.withdrawals := by
  unfold processWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨expected, found, _, carried, _⟩ := computed
  refine ⟨?_, expected, found, carried⟩
  unfold getExpectedWithdrawals at found
  split at found
  · cases found
  · exact Nat.lt_of_not_le ‹_›

/-- The withdrawal step keeps the sizes. -/
theorem sameSizes_processWithdrawals {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : ExecutionPayload preset fork}
    (computed : processWithdrawals state capella payload = .ok after) :
    SameSizes state after := by
  unfold processWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, applied, appliedOk, indexed, indexedOk, swept⟩ := computed
  have one := sameSizes_applyWithdrawals appliedOk
  have two := one.trans (sameSizes_updateNextWithdrawalIndex indexedOk)
  refine two.trans ?_
  split at swept
  · exact (show SameSizes indexed (updatePendingPartialWithdrawals indexed ‹_› _) from
      ⟨rfl, rfl⟩).trans (sameSizes_updateNextWithdrawalValidatorIndex swept)
  · exact sameSizes_updateNextWithdrawalValidatorIndex swept

end EthLib.Consensus
