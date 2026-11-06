module

public import EthLib.Base.Except
public import EthLib.Consensus.Mutators
public import EthLib.Cryptography.Bls.Signatures

/-!
# `Consensus.Transition.Basic`

What every step of the beacon state transition shares: its errors and its signature checks.

A step fails on a failed assertion of the rule, and on any error of the state accessors.

The signature checks are an argument, so a test can run a step without checking signatures.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- An error of the beacon state transition. -/
inductive TransitionError where
  /-- A state accessor or mutator fails. -/
  | accessor (error : AccessorError)
  /-- A root has no value. -/
  | ssz (error : Err)
  /-- The block is not at the slot of the state. -/
  | slotMismatch (blockSlot stateSlot : Slot)
  /-- The block is not after the latest block. -/
  | notNewer (blockSlot latestSlot : Slot)
  /-- The block names a proposer other than that of its slot. -/
  | wrongProposer (proposer expected : ValidatorIndex)
  /-- The parent root of the block is not the root of the latest block header. -/
  | wrongParent
  /-- The proposer of the block is slashed. -/
  | proposerSlashed (proposer : ValidatorIndex)
  /-- The RANDAO reveal is not the proposer's signature of the epoch. -/
  | invalidRandaoReveal
  /-- The votes on the deposit contract exceed their list limit. -/
  | tooManyEth1Votes
  /-- The two headers of a proposer slashing are for different slots. -/
  | headerSlotsDiffer
  /-- The two headers of a proposer slashing name different proposers. -/
  | headerProposersDiffer
  /-- The two headers of a proposer slashing are equal. -/
  | sameHeaders
  /-- The validator may not be slashed in the current epoch. -/
  | notSlashable (index : ValidatorIndex)
  /-- A header of a proposer slashing is not signed by its proposer. -/
  | invalidHeaderSignature
  /-- The two attestations of an attester slashing are not a double or a surround vote. -/
  | notSlashableData
  /-- An attestation of an attester slashing is not a valid indexed attestation. -/
  | invalidIndexedAttestation
  /-- No validator in both attestations of an attester slashing may be slashed. -/
  | noneSlashed
  /-- From Gloas: a payload attestation is not for the parent of the block. -/
  | payloadAttestationNotForParent
  /-- From Gloas: a payload attestation is not for the slot before that of the state. -/
  | payloadAttestationWrongSlot (slot stateSlot : Slot)
  /-- From Gloas: a payload attestation is not a valid indexed payload attestation. -/
  | invalidPayloadAttestation
  /-- From Gloas: a self-built bid has a nonzero value or a signature. -/
  | selfBuildBidPaid
  /-- From Gloas: the builder of a bid is not active. -/
  | builderNotActive (builder : BuilderIndex)
  /-- From Gloas: the builder of a bid does not build payloads. -/
  | notPayloadBuilder (builder : BuilderIndex)
  /-- From Gloas: the builder of a bid cannot pay its value. -/
  | bidNotCovered (builder : BuilderIndex)
  /-- From Gloas: a bid is not signed by its builder. -/
  | invalidBidSignature
  /-- From Deneb: a block, or from Gloas its bid, commits to more blobs than a block may hold. -/
  | tooManyBlobCommitments
  /-- From Gloas: a bid is not for the slot of the state. -/
  | bidWrongSlot (bidSlot stateSlot : Slot)
  /-- From Gloas: a bid is for the genesis slot. -/
  | bidAtGenesis
  /-- From Gloas: the parent hash of a bid is not the hash of the latest payload. -/
  | bidWrongParentHash
  /-- From Gloas: the payload hash of a bid is its parent hash. -/
  | bidRepeatsParentHash
  /-- From Gloas: the parent block root of a bid is not that of the previous slot. -/
  | bidWrongParentRoot
  /-- From Gloas: the RANDAO mix of a bid is not that of the current epoch. -/
  | bidWrongRandao
  /-- From Heze: at the upgrade, the state has not processed every deposit of the contract. -/
  | depositIndicesDiffer (eth1DepositIndex depositRequestsStartIndex : UInt64)
  /-- The target of an attestation is neither the current nor the previous epoch. -/
  | attestationTargetNotRecent (target currentEpoch : Epoch)
  /-- The target of an attestation is not the epoch of its slot. -/
  | attestationTargetNotSlotEpoch (target slotEpoch : Epoch)
  /-- An attestation is included before the least inclusion delay has passed. -/
  | attestationTooEarly (slot stateSlot : Slot)
  /-- An attestation is included more than one epoch of slots after its slot. -/
  | attestationTooLate (slot stateSlot : Slot)
  /-- An attestation names a committee past the committees of its slot. -/
  | committeeIndexOutOfRange (index count : UInt64)
  /-- An attestation does not have one bit for each member of its committee. -/
  | aggregationBitsLength (bits committee : Nat)
  /-- The source of an attestation is not the justified checkpoint of its target epoch. -/
  | wrongAttestationSource
  /-- The pending attestations of an epoch are at their list limit. -/
  | tooManyPendingAttestations
  /-- The indexed form of an attestation is not a valid indexed attestation. -/
  | invalidAttestation
  /-- A block does not hold the number of deposits that the state expects. -/
  | wrongDepositCount (count expected : Nat)
  /-- The Merkle branch of a deposit does not lead to the deposit root. -/
  | invalidDepositProof
  /-- The registry of validators is at its list limit. -/
  | registryFull
  /-- The validator of a voluntary exit is not active. -/
  | exitingValidatorNotActive (index : ValidatorIndex)
  /-- The validator of a voluntary exit has already started to exit. -/
  | exitAlreadyInitiated (index : ValidatorIndex)
  /-- A voluntary exit is for an epoch after the current epoch. -/
  | exitNotYetValid (epoch currentEpoch : Epoch)
  /-- The validator of a voluntary exit has not been active for long enough. -/
  | exitTooSoon (index : ValidatorIndex)
  /-- A voluntary exit is not signed by its validator. -/
  | invalidExitSignature
  /-- A pending attestation was included with no delay, which no reward can divide by. -/
  | zeroInclusionDelay
  /-- From Capella: the withdrawals before those of a reading leave it no place. -/
  | priorWithdrawalsAtLimit (count limit : Nat)
  /-- From Capella: a payload does not carry the withdrawals that the state expects. -/
  | wrongWithdrawals
  /-- From Capella: a change of BLS credentials is for a validator without BLS credentials. -/
  | notBlsCredentials (index : ValidatorIndex)
  /-- From Capella: the credentials of a validator do not commit to the key of a change. -/
  | wrongBlsKey (index : ValidatorIndex)
  /-- From Capella: a change of BLS credentials is not signed by its key. -/
  | invalidBlsChangeSignature
  /-- The historical roots are at their list limit. -/
  | historicalRootsFull
  /-- The target slot is not after the slot of the state. -/
  | slotNotAfter (slot stateSlot : Slot)
  /-- A block does not carry the signature of its proposer. -/
  | invalidBlockSignature
  /-- The state root of a block is not the root of the state after it. -/
  | wrongStateRoot
  /-- From Bellatrix: the parent hash of a payload is not the block hash of the latest payload. -/
  | wrongPayloadParentHash
  /-- From Bellatrix: a payload does not read the RANDAO mix of the current epoch. -/
  | wrongPayloadRandao
  /-- From Bellatrix: the time of a payload is not the time of the slot of the state. -/
  | wrongPayloadTimestamp (timestamp expected : UInt64)
  /-- From Bellatrix: the execution layer rejects a payload. -/
  | invalidExecutionPayload
  /-- From Capella: the historical summaries are at their list limit. -/
  | historicalSummariesFull
  /-- From Altair: the sync aggregate is not the signature of its members on the parent block. -/
  | invalidSyncAggregate
  /-- From Altair: a key of the sync committee does not decode, as the check of its sum needs. -/
  | invalidSyncCommitteeKey
  /-- From Altair: no validator holds the key of a member of the sync committee. -/
  | unknownSyncCommitteeMember
  /-- A block is of another fork than the state at its slot. -/
  | blockForkMismatch (block state : Fork)
  /-- From Electra: an attestation has a committee index other than zero. -/
  | attestationIndexNotZero (index : CommitteeIndex)
  /-- From Electra: a committee of an attestation has no attester. -/
  | noCommitteeAttester (index : CommitteeIndex)
  /-- From Electra: the validator of a voluntary exit has a pending partial withdrawal. -/
  | exitPendingWithdrawal (index : ValidatorIndex)
  /-- From Gloas: the parent payload is empty, but the block carries requests for it. -/
  | parentRequestsNotEmpty
  /-- From Gloas: the requests of the block are not those that the parent bid commits to. -/
  | wrongParentRequestsRoot
  /-- From Gloas: a list holds more entries than the most allowed. -/
  | tooManyOperations (count limit : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def TransitionError.code : TransitionError → UInt32
  | .accessor _ => 1
  | .ssz _ => 2
  | .slotMismatch .. => 3
  | .notNewer .. => 4
  | .wrongProposer .. => 5
  | .wrongParent => 6
  | .proposerSlashed _ => 7
  | .invalidRandaoReveal => 8
  | .tooManyEth1Votes => 9
  | .headerSlotsDiffer => 10
  | .headerProposersDiffer => 11
  | .sameHeaders => 12
  | .notSlashable _ => 13
  | .invalidHeaderSignature => 14
  | .notSlashableData => 15
  | .invalidIndexedAttestation => 16
  | .noneSlashed => 17
  | .payloadAttestationNotForParent => 18
  | .payloadAttestationWrongSlot .. => 19
  | .invalidPayloadAttestation => 20
  | .selfBuildBidPaid => 21
  | .builderNotActive _ => 22
  | .notPayloadBuilder _ => 23
  | .bidNotCovered _ => 24
  | .invalidBidSignature => 25
  | .tooManyBlobCommitments => 26
  | .bidWrongSlot .. => 27
  | .bidAtGenesis => 28
  | .bidWrongParentHash => 29
  | .bidRepeatsParentHash => 30
  | .bidWrongParentRoot => 31
  | .bidWrongRandao => 32
  | .depositIndicesDiffer .. => 33
  | .attestationTargetNotRecent .. => 34
  | .attestationTargetNotSlotEpoch .. => 35
  | .attestationTooEarly .. => 36
  | .attestationTooLate .. => 37
  | .committeeIndexOutOfRange .. => 38
  | .aggregationBitsLength .. => 39
  | .wrongAttestationSource => 40
  | .tooManyPendingAttestations => 41
  | .invalidAttestation => 42
  | .wrongDepositCount .. => 43
  | .invalidDepositProof => 44
  | .registryFull => 45
  | .exitingValidatorNotActive _ => 46
  | .exitAlreadyInitiated _ => 47
  | .exitNotYetValid .. => 48
  | .exitTooSoon _ => 49
  | .invalidExitSignature => 50
  | .zeroInclusionDelay => 51
  | .priorWithdrawalsAtLimit .. => 61
  | .wrongWithdrawals => 62
  | .notBlsCredentials _ => 63
  | .wrongBlsKey _ => 64
  | .invalidBlsChangeSignature => 65
  | .historicalRootsFull => 52
  | .slotNotAfter .. => 53
  | .invalidBlockSignature => 54
  | .wrongStateRoot => 55
  | .wrongPayloadParentHash => 66
  | .wrongPayloadRandao => 67
  | .wrongPayloadTimestamp .. => 68
  | .invalidExecutionPayload => 69
  | .historicalSummariesFull => 70
  | .invalidSyncAggregate => 71
  | .invalidSyncCommitteeKey => 72
  | .unknownSyncCommitteeMember => 73
  | .blockForkMismatch .. => 74
  | .attestationIndexNotZero _ => 75
  | .noCommitteeAttester _ => 76
  | .exitPendingWithdrawal _ => 77
  | .parentRequestsNotEmpty => 78
  | .wrongParentRequestsRoot => 79
  | .tooManyOperations .. => 80

/-- An error of a state accessor, as an error of the transition. -/
def liftAccessor {α : Type} (result : Except AccessorError α) : Except TransitionError α :=
  result.mapError .accessor

/-- An error of a root, as an error of the transition. -/
def liftSsz {α : Type} (result : Except Err α) : Except TransitionError α :=
  result.mapError .ssz

/-- The BLS signature checks that the transition runs.

Each takes the public keys, the message and the signature, all as bytes. -/
structure SignatureChecks where
  /-- The check of one signature by one key. -/
  verify : ByteArray → ByteArray → ByteArray → Bool
  /-- The check of one signature by several keys on one message. -/
  fastAggregateVerify : Array ByteArray → ByteArray → ByteArray → Bool

/-- The checks of the BLS signature scheme, which the transition runs on a real chain. -/
def SignatureChecks.bls : SignatureChecks where
  verify := Cryptography.Bls.Signatures.verify
  fastAggregateVerify := Cryptography.Bls.Signatures.fastAggregateVerify

/-- Checks that accept every signature.

The consensus test vectors use them for the cases that carry placeholder signatures. -/
def SignatureChecks.acceptAll : SignatureChecks where
  verify _ _ _ := true
  fastAggregateVerify _ _ _ := true

end EthLib.Consensus
