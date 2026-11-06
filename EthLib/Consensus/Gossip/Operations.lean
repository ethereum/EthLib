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
  let domain ← (getDomain config state DOMAIN_BEACON_PROPOSER
    (some (computeEpochAtSlot preset signed.message.slot))).mapError .accessor
  let signingRoot ← (computeSigningRoot signed.message domain).mapError .ssz
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature)

/-- Whether the validator key signed a voluntary exit, under the domain of exits. -/
def isValidVoluntaryExitSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (pubkey : BLSPubkey) (signed : SignedVoluntaryExit) :
    Except ForkChoiceError Bool := do
  let domain ← (voluntaryExitDomain config state signed.message.epoch).mapError .transition
  let signingRoot ← (computeSigningRoot signed.message domain).mapError .ssz
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature)

/-- Whether the BLS key in a change of credentials signed it, on the chain of the state.

The domain uses the genesis fork version, so that a change stays valid at every fork. -/
def isValidBlsToExecutionChangeSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBLSToExecutionChange) :
    Except ForkChoiceError Bool := do
  let domain ← (computeDomain config DOMAIN_BLS_TO_EXECUTION_CHANGE
    (genesisValidatorsRoot := state.genesisValidatorsRoot)).mapError .ssz
  let signingRoot ← (computeSigningRoot signed.message domain).mapError .ssz
  return checks.verify (packBytes signed.message.fromBlsPubkey) (packBytes signingRoot)
    (packBytes signed.signature)

/-! ## Attester slashings -/

/-- The validators that both attestations of a slashing name, each once, in the first order. -/
def slashableIndices (slashing : AttesterSlashing preset fork) : List ValidatorIndex :=
  let second := slashing.attestation2.attestingIndices.data.toList
  (slashing.attestation1.attestingIndices.data.toList.filter (second.contains ·)).eraseDups

/-- Whether every index of an attestation names a validator of the state. -/
def indicesInRange (state : BeaconState preset fork)
    (attestation : IndexedAttestation preset fork) : Bool :=
  attestation.attestingIndices.data.toList.all (·.toNat < state.validators.data.size)

/-- Whether a validator of the state is slashable in its current epoch.

An index that names no validator is not slashable. -/
def isSlashableIndex (state : BeaconState preset fork) (index : ValidatorIndex) : Bool :=
  match state.validators.data[index.toNat]? with
  | some validator => isSlashableValidator validator (getCurrentEpoch state)
  | none => false

/-- The checks of an attester slashing on its topic.

The slashing must name a validator that no valid slashing has named yet, else it is ignored.

Its attestations must be slashable together and each valid in the head state.

One validator that both name must be slashable. -/
def validateAttesterSlashing (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (slashing : AttesterSlashing preset fork) :
    Except ForkChoiceError ValidationResult :=
  let slashable := slashableIndices slashing
  (ignoreUnless (slashable.any (!seen.attesterSlashingIndices.contains ·))
    "all attester slashing indices already seen").andThenM fun _ =>
  (rejectUnless (isSlashableAttestationData slashing.attestation1.data
    slashing.attestation2.data) "attestation data is not slashable").andThenM fun _ => do
  let state ← store.headState config
  (rejectUnless (indicesInRange state slashing.attestation1)
    "validator index out of range in indexed attestation 1").andThenM fun _ => do
  let valid1 ← (isValidIndexedAttestation config checks state slashing.attestation1).mapError
    .transition
  (rejectUnless valid1 "invalid indexed attestation 1").andThenM fun _ =>
  (rejectUnless (indicesInRange state slashing.attestation2)
    "validator index out of range in indexed attestation 2").andThenM fun _ => do
  let valid2 ← (isValidIndexedAttestation config checks state slashing.attestation2).mapError
    .transition
  (rejectUnless valid2 "invalid indexed attestation 2").andThenM fun _ =>
  return rejectUnless (slashable.any (isSlashableIndex state))
    "no slashable validators in intersection"

/-- The keys after a valid attester slashing: every validator that both attestations name. -/
def Seen.recordAttesterSlashing (seen : Seen) (slashing : AttesterSlashing preset fork) : Seen :=
  { seen with
    attesterSlashingIndices := seen.attesterSlashingIndices.insertMany (slashableIndices slashing) }

/-! ## Proposer slashings -/

/-- The checks of a proposer slashing on its topic.

The first valid slashing of a proposer passes, and a later one is ignored.

Its two headers must differ, with one slot and one proposer.

The proposer must be slashable in the head state, and must have signed both headers. -/
def validateProposerSlashing (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (slashing : ProposerSlashing) :
    Except ForkChoiceError ValidationResult :=
  let header1 := slashing.signedHeader1.message
  let header2 := slashing.signedHeader2.message
  let index := header1.proposerIndex
  (ignoreUnless (!seen.proposerSlashingIndices.contains index)
    "already seen proposer slashing for this proposer").andThenM fun _ =>
  (rejectUnless (header1.slot == header2.slot) "header slots do not match").andThenM fun _ =>
  (rejectUnless (header1.proposerIndex == header2.proposerIndex)
    "header proposer indices do not match").andThenM fun _ =>
  (rejectUnless (header1 != header2) "headers are not different").andThenM fun _ => do
  let state ← store.headState config
  match state.validators.data[index.toNat]? with
  | none => return .reject "proposer index out of range"
  | some proposer =>
  (rejectUnless (isSlashableValidator proposer (getCurrentEpoch state))
    "proposer is not slashable").andThenM fun _ => do
  let valid1 ← isValidHeaderSignature config checks state proposer.pubkey slashing.signedHeader1
  (rejectUnless valid1 "invalid proposer slashing signature").andThenM fun _ => do
  let valid2 ← isValidHeaderSignature config checks state proposer.pubkey slashing.signedHeader2
  return rejectUnless valid2 "invalid proposer slashing signature"

/-- The keys after a valid proposer slashing: its proposer. -/
def Seen.recordProposerSlashing (seen : Seen) (slashing : ProposerSlashing) : Seen :=
  { seen with
    proposerSlashingIndices :=
      seen.proposerSlashingIndices.insert slashing.signedHeader1.message.proposerIndex }

/-! ## Voluntary exits -/

/-- The checks of a voluntary exit on its topic, at a time in milliseconds.

The first valid exit of a validator passes, and a later one is ignored.

An exit for an epoch after the current one is ignored, as is the exit of an exiting validator.

The validator must be active in the head state, for long enough, and must have signed the exit. -/
def validateVoluntaryExit (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (signed : SignedVoluntaryExit) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let exit := signed.message
  let index := exit.validatorIndex
  (ignoreUnless (!seen.voluntaryExitIndices.contains index)
    "already seen voluntary exit for this validator").andThenM fun _ => do
  let future ← store.isFutureEpoch config exit.epoch currentTimeMs
  (ignoreUnless (!future) "voluntary exit epoch is in the future").andThenM fun _ => do
  let state ← store.headState config
  match state.validators.data[index.toNat]? with
  | none => return .reject "validator index out of range"
  | some validator =>
  let epoch := getCurrentEpoch state
  (ignoreUnless (validator.exitEpoch == FAR_FUTURE_EPOCH)
    "validator has already initiated exit").andThenM fun _ =>
  (rejectUnless (isActiveValidator validator epoch) "validator is not active").andThenM fun _ => do
  let eligible ←
    (addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD).mapError .arith
  (rejectUnless (eligible ≤ epoch) "validator has not been active long enough").andThenM
    fun _ => do
  let valid ← isValidVoluntaryExitSignature config checks state validator.pubkey signed
  return rejectUnless valid "invalid voluntary exit signature"

/-- The keys after a valid voluntary exit: its validator. -/
def Seen.recordVoluntaryExit (seen : Seen) (signed : SignedVoluntaryExit) : Seen :=
  { seen with
    voluntaryExitIndices := seen.voluntaryExitIndices.insert signed.message.validatorIndex }

/-! ## Changes of BLS credentials -/

/-- Whether withdrawal credentials start with the BLS prefix. -/
def blsCredentialsPrefixed (credentials : Bytes32) : Bool :=
  credentials[0] == BLS_WITHDRAWAL_PREFIX[0]

/-- Whether the last 31 bytes of withdrawal credentials are those of the SHA-256 hash of a key. -/
def blsCredentialsMatch (credentials : Bytes32) (pubkey : BLSPubkey) : Bool :=
  let keyHash := sha256Bytes32 ⟨pubkey.toArray⟩
  decide (∀ i : Fin 31, credentials[i.val + 1] = keyHash[i.val + 1])

/-- From Capella: the checks of a change of BLS credentials on its topic, at a time in ms.

The first valid change for a validator passes, and a later one is ignored.

A change before the first epoch of Capella, by the clock, is ignored.

The validator must have BLS credentials that commit to the key of the change.

That key must have signed the change. -/
def validateBlsToExecutionChange (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (signed : SignedBLSToExecutionChange) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let change := signed.message
  let index := change.validatorIndex
  (ignoreUnless (!seen.blsToExecutionChangeIndices.contains index)
    "already seen BLS to execution change for this validator").andThenM fun _ => do
  let early ← store.isFutureEpoch config config.CAPELLA_FORK_EPOCH currentTimeMs
  (ignoreUnless (!early) "current epoch is pre-capella").andThenM fun _ => do
  let state ← store.headState config
  match state.validators.data[index.toNat]? with
  | none => return .reject "validator index out of range"
  | some validator =>
  (rejectUnless (blsCredentialsPrefixed validator.withdrawalCredentials)
    "validator does not have BLS withdrawal credentials").andThenM fun _ =>
  (rejectUnless (blsCredentialsMatch validator.withdrawalCredentials change.fromBlsPubkey)
    "pubkey does not match validator withdrawal credentials").andThenM fun _ => do
  let valid ← isValidBlsToExecutionChangeSignature config checks state signed
  return rejectUnless valid "invalid BLS to execution change signature"

/-- The keys after a valid change of BLS credentials: its validator. -/
def Seen.recordBlsToExecutionChange (seen : Seen) (signed : SignedBLSToExecutionChange) : Seen :=
  { seen with
    blsToExecutionChangeIndices :=
      seen.blsToExecutionChangeIndices.insert signed.message.validatorIndex }

end EthLib.Consensus
