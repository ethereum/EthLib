module

public import EthLib.Consensus.Gossip.Seen
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.Gossip.Operations`

Gossip validation of the operations that a block may include.

They are attester slashings, proposer slashings and voluntary exits.

From Capella they also include changes of BLS withdrawal credentials.

Each topic runs its checks in a fixed order, and the first check that fails gives the outcome.

The checks that read the chain read the state after the head.

An operation that a block could not include is rejected.

A duplicate of a valid operation is ignored, as is an operation that the clock does not yet allow.

A valid operation records its key among the messages seen.

Some steps of the rule can fail, such as a root, or an addition out of range.

Such a failure is an error rather than an outcome.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-! ## Signatures -/

/-- Whether the proposer key signed a block header, in the epoch of its slot. -/
def isValidHeaderSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (pubkey : BLSPubkey) (signed : SignedBeaconBlockHeader) :
    Except ForkChoiceError Bool := do
  -- The domain of `DOMAIN_BEACON_PROPOSER` at the epoch of the slot of the header.
  let domain ← (getDomain config state DOMAIN_BEACON_PROPOSER
    (some (computeEpochAtSlot preset signed.message.slot))).mapError .accessor
  -- The key signed the signing root of the header under that domain.
  let signingRoot ← (computeSigningRoot signed.message domain).mapError .ssz
  return checks.verify pubkey (packBytes signingRoot) signed.signature

/-- Whether the validator key signed a voluntary exit, under the domain of exits. -/
def isValidVoluntaryExitSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (pubkey : BLSPubkey) (signed : SignedVoluntaryExit) :
    Except ForkChoiceError Bool := do
  -- The domain of exits for the epoch of the exit.
  --
  -- From Deneb it is the domain at the Capella fork version, whatever the epoch, as EIP-7044 says.
  let domain ← (voluntaryExitDomain config state signed.message.epoch).mapError .transition
  -- The key signed the signing root of the exit under that domain.
  let signingRoot ← (computeSigningRoot signed.message domain).mapError .ssz
  return checks.verify pubkey (packBytes signingRoot) signed.signature

/-- Whether the BLS key in a change of credentials signed it, on the chain of the state.

The domain uses the genesis fork version, so that a change stays valid at every fork. -/
def isValidBlsToExecutionChangeSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBLSToExecutionChange) :
    Except ForkChoiceError Bool := do
  -- The domain of `DOMAIN_BLS_TO_EXECUTION_CHANGE` at the genesis fork version.
  --
  -- Its validators root is the genesis validators root of the state.
  let domain ← (computeDomain config DOMAIN_BLS_TO_EXECUTION_CHANGE
    (genesisValidatorsRoot := state.genesisValidatorsRoot)).mapError .ssz
  -- The BLS key of the change signed the signing root of the change under that domain.
  let signingRoot ← (computeSigningRoot signed.message domain).mapError .ssz
  return checks.verify signed.message.fromBlsPubkey (packBytes signingRoot)
    signed.signature

/-! ## Attester slashings -/

/-- The validators that both attestations of a slashing name, each once, in the first order. -/
def slashableIndices (slashing : AttesterSlashing preset fork) : List ValidatorIndex :=
  -- The indices of the first attestation that the second also holds, each once.
  let second := slashing.attestation2.attestingIndices.data.toList
  (slashing.attestation1.attestingIndices.data.toList.filter (second.contains ·)).eraseDups

/-- Whether every index of an attestation names a validator of the state. -/
def indicesInRange (state : BeaconState preset fork)
    (attestation : IndexedAttestation preset fork) : Bool :=
  -- Every index is below the count of validators.
  attestation.attestingIndices.data.toList.all (·.toNat < state.validators.data.size)

/-- Whether a validator of the state is slashable in its current epoch. -/
def isSlashableIndex (state : BeaconState preset fork) (index : ValidatorIndex) : Bool :=
  match state.validators.data[index.toNat]? with
  -- The validator of the index is slashable at the current epoch.
  | some validator => isSlashableValidator validator (getCurrentEpoch state)
  -- An index that names no validator is not slashable.
  | none => false

/-- The checks of an attester slashing on its topic. -/
def validateAttesterSlashing (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (slashing : AttesterSlashing preset fork) :
    Except ForkChoiceError ValidationResult :=
  -- The validators that both attestations name.
  let slashable := slashableIndices slashing
  -- IGNORE unless one of them is not yet among the validators of valid attester slashings.
  (ignoreUnless (slashable.any (!seen.attesterSlashingIndices.contains ·))
    "all attester slashing indices already seen").andThenM fun _ =>
  -- REJECT unless the two data are slashable together: a double vote or a surround vote.
  (rejectUnless (isSlashableAttestationData slashing.attestation1.data
    slashing.attestation2.data) "attestation data is not slashable").andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless every index of the first attestation names a validator of that state.
  (rejectUnless (indicesInRange state slashing.attestation1)
    "validator index out of range in indexed attestation 1").andThenM fun _ => do
  -- REJECT unless the first attestation is valid in that state, its signature included.
  let valid1 ← (isValidIndexedAttestation config checks state slashing.attestation1).mapError
    .transition
  (rejectUnless valid1 "invalid indexed attestation 1").andThenM fun _ =>
  -- REJECT unless every index of the second attestation names a validator of that state.
  (rejectUnless (indicesInRange state slashing.attestation2)
    "validator index out of range in indexed attestation 2").andThenM fun _ => do
  -- REJECT unless the second attestation is valid in that state, its signature included.
  let valid2 ← (isValidIndexedAttestation config checks state slashing.attestation2).mapError
    .transition
  (rejectUnless valid2 "invalid indexed attestation 2").andThenM fun _ =>
  -- REJECT unless one validator that both name is slashable at the current epoch.
  return rejectUnless (slashable.any (isSlashableIndex state))
    "no slashable validators in intersection"

/-- The keys after a valid attester slashing: every validator that both attestations name. -/
def Seen.recordAttesterSlashing (seen : Seen) (slashing : AttesterSlashing preset fork) : Seen :=
  -- Every validator that both attestations name joins the keys.
  { seen with
    attesterSlashingIndices := seen.attesterSlashingIndices.insertMany (slashableIndices slashing) }

/-! ## Proposer slashings -/

/-- The checks of a proposer slashing on its topic. -/
def validateProposerSlashing (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (slashing : ProposerSlashing) :
    Except ForkChoiceError ValidationResult :=
  let header1 := slashing.signedHeader1.message
  let header2 := slashing.signedHeader2.message
  let index := header1.proposerIndex
  -- IGNORE when a valid proposer slashing of the proposer was already seen.
  (ignoreUnless (!seen.proposerSlashingIndices.contains index)
    "already seen proposer slashing for this proposer").andThenM fun _ =>
  -- REJECT unless the two headers have the same slot.
  (rejectUnless (header1.slot == header2.slot) "header slots do not match").andThenM fun _ =>
  -- REJECT unless they have the same proposer.
  (rejectUnless (header1.proposerIndex == header2.proposerIndex)
    "header proposer indices do not match").andThenM fun _ =>
  -- REJECT unless the two headers differ.
  (rejectUnless (header1 != header2) "headers are not different").andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the proposer index names a validator of that state.
  match state.validators.data[index.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer =>
  -- REJECT unless the proposer is slashable at the current epoch.
  (rejectUnless (isSlashableValidator proposer (getCurrentEpoch state))
    "proposer is not slashable").andThenM fun _ => do
  -- REJECT unless the proposer signed the first header.
  let valid1 ← isValidHeaderSignature config checks state proposer.pubkey slashing.signedHeader1
  (rejectUnless valid1 "invalid proposer slashing signature").andThenM fun _ => do
  -- REJECT unless the proposer signed the second header.
  let valid2 ← isValidHeaderSignature config checks state proposer.pubkey slashing.signedHeader2
  return rejectUnless valid2 "invalid proposer slashing signature"

/-- The keys after a valid proposer slashing: its proposer. -/
def Seen.recordProposerSlashing (seen : Seen) (slashing : ProposerSlashing) : Seen :=
  -- The proposer joins the keys.
  { seen with
    proposerSlashingIndices :=
      seen.proposerSlashingIndices.insert slashing.signedHeader1.message.proposerIndex }

/-! ## Voluntary exits -/

/-- The checks of a voluntary exit on its topic, at a time in milliseconds. -/
def validateVoluntaryExit (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (signed : SignedVoluntaryExit) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let exit := signed.message
  let index := exit.validatorIndex
  -- IGNORE when a valid exit of the validator was already seen.
  (ignoreUnless (!seen.voluntaryExitIndices.contains index)
    "already seen voluntary exit for this validator").andThenM fun _ => do
  -- IGNORE when the epoch of the exit is after the current epoch, by the clock.
  let future ← store.isFutureEpoch config exit.epoch currentTimeMs
  (ignoreUnless (!future) "voluntary exit epoch is in the future").andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the validator index names a validator of that state.
  match state.validators.data[index.toNat]? with
  | none => return .reject "validator index out of range"
  | some validator =>
  -- Let `e` be the current epoch of that state.
  let epoch := getCurrentEpoch state
  -- IGNORE when the validator has already initiated its exit.
  --
  -- Its exit epoch is then not `FAR_FUTURE_EPOCH`.
  (ignoreUnless (validator.exitEpoch == FAR_FUTURE_EPOCH)
    "validator has already initiated exit").andThenM fun _ =>
  -- REJECT unless the validator is active at `e`.
  (rejectUnless (isActiveValidator validator epoch) "validator is not active").andThenM fun _ => do
  -- REJECT unless `e` is at least its activation epoch plus `SHARD_COMMITTEE_PERIOD`.
  let eligible ←
    (addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD).mapError .arith
  (rejectUnless (eligible ≤ epoch) "validator has not been active long enough").andThenM
    fun _ => do
  -- IGNORE when the validator has a pending partial withdrawal, from Electra.
  --
  -- The block would reject the exit.
  let pending ← (pendingBalanceToWithdraw state index).mapError .accessor
  (ignoreUnless (pending == 0) "validator has pending partial withdrawals").andThenM fun _ => do
  -- REJECT unless the validator signed the exit.
  let valid ← isValidVoluntaryExitSignature config checks state validator.pubkey signed
  return rejectUnless valid "invalid voluntary exit signature"

/-- The keys after a valid voluntary exit: its validator. -/
def Seen.recordVoluntaryExit (seen : Seen) (signed : SignedVoluntaryExit) : Seen :=
  -- The validator joins the keys.
  { seen with
    voluntaryExitIndices := seen.voluntaryExitIndices.insert signed.message.validatorIndex }

/-! ## Changes of BLS credentials -/

/-- Whether withdrawal credentials start with the BLS prefix. -/
def blsCredentialsPrefixed (credentials : Bytes32) : Bool :=
  -- The first byte is the byte of `BLS_WITHDRAWAL_PREFIX`.
  credentials[0] == BLS_WITHDRAWAL_PREFIX[0]

/-- Whether the last 31 bytes of withdrawal credentials are those of the SHA-256 hash of a key. -/
def blsCredentialsMatch (credentials : Bytes32) (pubkey : BLSPubkey) : Bool :=
  -- Let `h` be the SHA-256 hash of the 48 bytes of the key.
  let keyHash := Cryptography.Hash.Sha256.hash32 ⟨pubkey.toArray⟩
  -- Byte `i` of the credentials is byte `i` of `h`, for `1 ≤ i ≤ 31`.
  decide (∀ i : Fin 31, credentials[i.val + 1] = keyHash[i.val + 1])

/-- From Capella: the checks of a change of BLS credentials on its topic, at a time in ms. -/
def validateBlsToExecutionChange (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (signed : SignedBLSToExecutionChange) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let change := signed.message
  let index := change.validatorIndex
  -- IGNORE when a valid change for the validator was already seen.
  (ignoreUnless (!seen.blsToExecutionChangeIndices.contains index)
    "already seen BLS to execution change for this validator").andThenM fun _ => do
  -- IGNORE when `CAPELLA_FORK_EPOCH` is after the current epoch, by the clock.
  let early ← store.isFutureEpoch config config.CAPELLA_FORK_EPOCH currentTimeMs
  (ignoreUnless (!early) "current epoch is pre-capella").andThenM fun _ => do
  -- The checks that follow read the state after the head.
  let state ← store.headState config
  -- REJECT unless the validator index names a validator of that state.
  match state.validators.data[index.toNat]? with
  | none => return .reject "validator index out of range"
  | some validator =>
  -- REJECT unless the withdrawal credentials of the validator start with the BLS prefix.
  (rejectUnless (blsCredentialsPrefixed validator.withdrawalCredentials)
    "validator does not have BLS withdrawal credentials").andThenM fun _ =>
  -- REJECT unless their last 31 bytes are those of the SHA-256 hash of the key of the change.
  (rejectUnless (blsCredentialsMatch validator.withdrawalCredentials change.fromBlsPubkey)
    "pubkey does not match validator withdrawal credentials").andThenM fun _ => do
  -- REJECT unless that key signed the change.
  let valid ← isValidBlsToExecutionChangeSignature config checks state signed
  return rejectUnless valid "invalid BLS to execution change signature"

/-- The keys after a valid change of BLS credentials: its validator. -/
def Seen.recordBlsToExecutionChange (seen : Seen) (signed : SignedBLSToExecutionChange) : Seen :=
  -- The validator joins the keys.
  { seen with
    blsToExecutionChangeIndices :=
      seen.blsToExecutionChangeIndices.insert signed.message.validatorIndex }

end EthLib.Consensus
