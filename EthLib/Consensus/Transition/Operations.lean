module

public import EthLib.Consensus.Transition.Block
public import EthLib.Consensus.Transition.BuilderRequests
public import EthLib.Consensus.Transition.Withdrawals
public import EthLib.Serialization.Ssz.Merkle.Branch

/-!
# `Consensus.Transition.Operations`

The operations of a block: slashings, attestations, deposits and voluntary exits.

From Capella a block also changes BLS credentials to addresses.

A block runs them in that order, each kind in the order of the block.

Before Altair an attestation joins the pending attestations of its target epoch.

A deposit must lie in the deposit tree that the chain has agreed on, at the next deposit index.

A deposit to a new key adds a validator if its signature is valid, and else changes nothing.

A deposit to a known key adds to the balance of that validator.

A voluntary exit starts the exit of an active validator that has been active for long enough.

Where a later fork changes a rule, the step fails as not yet specified there.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-! ## Attestations -/

/-- Before Electra, the bits of an attestation fit the bits of a pending attestation. -/
theorem aggregationBits_size_le (attestation : Attestation preset fork)
    (before : fork < .pectra) :
    attestation.aggregationBits.bits.size ≤ preset.MAX_VALIDATORS_PER_COMMITTEE.toNat := by
  have bound := attestation.aggregationBits.bound (Nat.lt_trans before (by decide))
  have notElectra : ¬Fork.pectra ≤ fork := fun le =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simpa [maxAttesters, notElectra] using bound

/-- Before Altair: the state with a pending attestation appended to those of an epoch.

The epoch is the current one when the flag is set, and the previous one otherwise.

A list at its limit is an error. -/
def recordPendingAttestation (state : BeaconState preset fork) (before : fork < .altair)
    (current : Bool) (pending : PendingAttestation preset) :
    Except TransitionError (BeaconState preset fork) :=
  let list := if current then state.currentEpochAttestations before
    else state.previousEpochAttestations before
  if fits : list.data.size < preset.MAX_ATTESTATIONS.toNat * preset.SLOTS_PER_EPOCH.toNat then
    let list : SszList (PendingAttestation preset) _ :=
      ⟨list.data.push pending, by simp only [Array.size_push]; omega⟩
    if current then .ok { state with currentEpochAttestations := fun _ => list }
    else .ok { state with previousEpochAttestations := fun _ => list }
  else .error .tooManyPendingAttestations

/-- The state after an attestation.

Its target must be the current or the previous epoch, and the epoch of its slot.

It must be included at least the least inclusion delay after its slot, and at most one epoch after.

It must name a committee of its slot, with one bit for each member.

Its source must be the justified checkpoint that the state holds for its target epoch.

It then joins the pending attestations of that epoch, with its delay and the current proposer.

Its signature must be the aggregate signature of the members whose bit is set.

A 64-bit overflow is an error.

From Altair the rule records participation flags instead, which EthLib does not yet have. -/
def processAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (attestation : Attestation preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    have before : fork < .altair := Nat.lt_of_not_le altair
    let data := attestation.data
    let currentEpoch := getCurrentEpoch state
    ensure (data.target.epoch = getPreviousEpoch state ∨ data.target.epoch = currentEpoch)
      (.attestationTargetNotRecent data.target.epoch currentEpoch)
    ensure (data.target.epoch = computeEpochAtSlot preset data.slot)
      (.attestationTargetNotSlotEpoch data.target.epoch (computeEpochAtSlot preset data.slot))
    let earliest ←
      liftAccessor (liftArith (addChecked data.slot preset.MIN_ATTESTATION_INCLUSION_DELAY))
    ensure (earliest ≤ state.slot) (.attestationTooEarly data.slot state.slot)
    let latest ← liftAccessor (liftArith (addChecked data.slot preset.SLOTS_PER_EPOCH))
    ensure (state.slot ≤ latest) (.attestationTooLate data.slot state.slot)
    let count := getCommitteeCountPerSlot state data.target.epoch
    ensure (data.index < count) (.committeeIndexOutOfRange data.index count)
    let committee ← liftAccessor (getBeaconCommittee state data.slot data.index)
    let bits := attestation.aggregationBits.bits
    ensure (bits.size = committee.size) (.aggregationBitsLength bits.size committee.size)
    let proposer ← liftAccessor (getBeaconProposerIndex state)
    let pending : PendingAttestation preset :=
      ⟨⟨bits, aggregationBits_size_le attestation (Nat.lt_trans before (by decide))⟩, data,
        state.slot - data.slot, proposer⟩
    let current := data.target.epoch == currentEpoch
    let justified :=
      if current then state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint
    ensure (data.source = justified) .wrongAttestationSource
    let updated ← recordPendingAttestation state before current pending
    let indexed ← liftAccessor (getIndexedAttestation updated attestation)
    let valid ← isValidIndexedAttestation config checks updated indexed
    ensure (valid = true) .invalidAttestation
    return updated

/-! ## Deposits -/

/-- The validator that a deposit creates, before Electra.

Its effective balance is the amount rounded down to a whole increment, and at most the largest.

It is not slashed, not yet eligible for activation, and has no exit. -/
def getValidatorFromDeposit (preset : Preset) (pubkey : BLSPubkey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) : Validator where
  pubkey
  withdrawalCredentials
  effectiveBalance :=
    min (amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT) preset.MAX_EFFECTIVE_BALANCE
  slashed := false
  activationEligibilityEpoch := FAR_FUTURE_EPOCH
  activationEpoch := FAR_FUTURE_EPOCH
  exitEpoch := FAR_FUTURE_EPOCH
  withdrawableEpoch := FAR_FUTURE_EPOCH

/-- The state with a new validator at the end of the registry, and its balance.

A registry at its limit is an error.

From Altair a new validator also gets participation flags and an inactivity score.

EthLib does not yet have that rule. -/
def addValidatorToRegistry (state : BeaconState preset fork) (pubkey : BLSPubkey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else
    if fits : state.validators.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat ∧
        state.balances.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat then
      .ok { state with
        validators :=
          ⟨state.validators.data.push
              (getValidatorFromDeposit preset pubkey withdrawalCredentials amount),
            fun _ => by simp only [Array.size_push]; omega⟩
        balances :=
          ⟨state.balances.data.push amount, fun _ => by simp only [Array.size_push]; omega⟩ }
    else .error .registryFull

/-- The state after the deposit of an amount to a key.

A key that no validator has gets a new validator, if the deposit carries its signature.

A deposit to a new key with an invalid signature changes nothing.

A key that a validator has adds the amount to the balance of the first such validator.

Electra queues deposits instead, which EthLib does not yet have. -/
def applyDeposit (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (pubkey : BLSPubkey) (withdrawalCredentials : Bytes32) (amount : Gwei)
    (signature : BLSSignature) : Except TransitionError (BeaconState preset fork) :=
  if .pectra ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else
    match state.validators.data.findIdx? (·.pubkey == pubkey) with
    | none => do
      if ← isValidDepositSignature config checks pubkey withdrawalCredentials amount signature then
        addValidatorToRegistry state pubkey withdrawalCredentials amount
      else return state
    | some index => liftAccessor (increaseBalance state index.toUInt64 amount)

/-- The state after a deposit of a block.

Its Merkle branch must lead from the deposit to the deposit root, at the next deposit index.

The branch has one node more than the depth of the tree, for the number of deposits in the root.

The next deposit index then grows by one, and the deposit applies.

The step exists only before Heze, which removes deposits from blocks. -/
def processDeposit (config : Config) (checks : SignatureChecks) (before : fork < .hegota)
    (state : BeaconState preset fork) (deposit : Deposit) :
    Except TransitionError (BeaconState preset fork) := do
  let leaf ← liftSsz (hashTreeRoot deposit.data)
  let index := state.eth1DepositIndex before
  ensure (isValidMerkleBranch leaf deposit.proof.toList (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
    index.toNat (state.eth1Data before).depositRoot = true) .invalidDepositProof
  let next ← liftAccessor (liftArith (addChecked index 1))
  applyDeposit config checks { state with eth1DepositIndex := fun _ => next } deposit.data.pubkey
    deposit.data.withdrawalCredentials deposit.data.amount deposit.data.signature

/-! ## Voluntary exits -/

/-- The state after a voluntary exit.

Its validator must be active, and must not have started to exit.

It must have been active for long enough.

The exit must not be for a later epoch than the current one.

The validator must sign the exit, under the fork version of the epoch of the exit.

The validator then starts to exit.

Deneb fixes the version of the signature, as [EIP-7044] specifies, which EthLib does not yet have.

[EIP-7044]: https://eips.ethereum.org/EIPS/eip-7044#specification
-/
def processVoluntaryExit (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedVoluntaryExit) :
    Except TransitionError (BeaconState preset fork) :=
  if .dencun ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    let exit := signed.message
    let validator ← liftAccessor (getValidator state exit.validatorIndex)
    let epoch := getCurrentEpoch state
    ensure (isActiveValidator validator epoch = true)
      (.exitingValidatorNotActive exit.validatorIndex)
    ensure (validator.exitEpoch = FAR_FUTURE_EPOCH) (.exitAlreadyInitiated exit.validatorIndex)
    ensure (exit.epoch ≤ epoch) (.exitNotYetValid exit.epoch epoch)
    let eligible ←
      liftAccessor (liftArith (addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD))
    ensure (eligible ≤ epoch) (.exitTooSoon exit.validatorIndex)
    let domain ← liftAccessor (getDomain config state DOMAIN_VOLUNTARY_EXIT (some exit.epoch))
    let signingRoot ← liftSsz (computeSigningRoot exit domain)
    ensure (checks.verify (packBytes validator.pubkey) (packBytes signingRoot)
      (packBytes signed.signature) = true) .invalidExitSignature
    liftAccessor (initiateValidatorExit config state exit.validatorIndex)

/-! ## All the operations of a block -/

/-- The state after the operations of a block.

The block must hold every deposit that the state has not processed, up to the most per block.

The proposer slashings run first, then the attester slashings, attestations, deposits and exits.

From Capella the changes of BLS credentials run last.

A 64-bit underflow is an error.

Electra changes the deposits and adds the requests, which EthLib does not yet have. -/
def processOperations (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (body : BeaconBlockBody preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if electra : .pectra ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le electra) (by decide)
    let outstanding ← liftAccessor (liftArith
      (subChecked (state.eth1Data before).depositCount (state.eth1DepositIndex before)))
    let expected := (min preset.MAX_DEPOSITS outstanding).toNat
    let deposits := (body.deposits before).data
    ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
    let state ← body.proposerSlashings.data.foldlM (processProposerSlashing config checks) state
    let state ← body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) state
    let state ← body.attestations.data.foldlM (processAttestation config checks) state
    let state ← deposits.foldlM (processDeposit config checks before) state
    let state ← body.voluntaryExits.data.foldlM (processVoluntaryExit config checks) state
    if capella : .shapella ≤ fork then
      (body.blsToExecutionChanges capella).data.foldlM (processBlsToExecutionChange config checks)
        state
    else return state

end EthLib.Consensus
