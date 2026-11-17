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

open scoped HexRepr

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
  /-- The parent root of the block is not the root of the latest block header.

  It holds the parent root of the block, then the root of the latest block header. -/
  | wrongParent (parentRoot expected : Root)
  /-- The proposer of the block is slashed. -/
  | proposerSlashed (proposer : ValidatorIndex)
  /-- The RANDAO reveal is not the proposer's signature of the epoch.

  It holds the index of the proposer and the current epoch, which the reveal signs. -/
  | invalidRandaoReveal (proposer : ValidatorIndex) (epoch : Epoch)
  /-- The votes on the deposit contract exceed their list limit.

  It holds the number of votes with the vote of the block, then the limit. -/
  | tooManyEth1Votes (count limit : Nat)
  /-- The two headers of a proposer slashing are for different slots.

  It holds the slot of the first header, then that of the second. -/
  | headerSlotsDiffer (slot1 slot2 : Slot)
  /-- The two headers of a proposer slashing name different proposers.

  It holds the proposer of the first header, then that of the second. -/
  | headerProposersDiffer (proposer1 proposer2 : ValidatorIndex)
  /-- The two headers of a proposer slashing are equal.

  It holds the slot and the proposer of the headers. -/
  | sameHeaders (slot : Slot) (proposer : ValidatorIndex)
  /-- The validator may not be slashed in the current epoch. -/
  | notSlashable (index : ValidatorIndex)
  /-- A header of a proposer slashing is not signed by its proposer.

  It holds the proposer of the header and the signing root that the signature fails on. -/
  | invalidHeaderSignature (proposer : ValidatorIndex) (signingRoot : Root)
  /-- The two attestations of an attester slashing are not a double or a surround vote.

  It holds the source and target epochs of the first attestation, then those of the second. -/
  | notSlashableData (source1 target1 source2 target2 : Epoch)
  /-- An attestation of an attester slashing is not a valid indexed attestation.

  It holds the position of the attestation in the slashing, 1 or 2. -/
  | invalidIndexedAttestation (position : Nat)
  /-- No validator in both attestations of an attester slashing may be slashed.

  It holds the number of validators in both attestations. -/
  | noneSlashed (candidates : Nat)
  /-- From Gloas: a payload attestation is not for the parent of the block.

  It holds the block root of the attestation, then the parent root of the latest block header. -/
  | payloadAttestationNotForParent (root expected : Root)
  /-- From Gloas: a payload attestation is not for the slot before that of the state. -/
  | payloadAttestationWrongSlot (slot stateSlot : Slot)
  /-- From Gloas: a payload attestation is not a valid indexed payload attestation.

  It holds the slot of the attestation and the number of validators that its indexed form names. -/
  | invalidPayloadAttestation (slot : Slot) (attesters : Nat)
  /-- From Gloas: a self-built bid has a nonzero value or a signature.

  It holds the value of the bid.

  A value of zero means that the bid carries a signature. -/
  | selfBuildBidPaid (value : Gwei)
  /-- From Gloas: the builder of a bid is not active. -/
  | builderNotActive (builder : BuilderIndex)
  /-- From Gloas: the builder of a bid does not build payloads. -/
  | notPayloadBuilder (builder : BuilderIndex)
  /-- From Gloas: the builder of a bid cannot pay its value. -/
  | bidNotCovered (builder : BuilderIndex)
  /-- From Gloas: a bid is not signed by its builder.

  It holds the builder and the slot of the bid. -/
  | invalidBidSignature (builder : BuilderIndex) (slot : Slot)
  /-- From Deneb: a block, or from Gloas its bid, commits to more blobs than a block may hold.

  It holds the number of commitments, then the most allowed. -/
  | tooManyBlobCommitments (count limit : Nat)
  /-- From Gloas: a bid is not for the slot of the state. -/
  | bidWrongSlot (bidSlot stateSlot : Slot)
  /-- From Gloas: a bid is for the genesis slot. -/
  | bidAtGenesis
  /-- From Gloas: the parent hash of a bid is not the hash of the latest payload.

  It holds the parent hash of the bid, then the latest block hash of the state. -/
  | bidWrongParentHash (parentHash expected : Hash32)
  /-- From Gloas: the payload hash of a bid is its parent hash.

  It holds that hash. -/
  | bidRepeatsParentHash (blockHash : Hash32)
  /-- From Gloas: the parent block root of a bid is not that of the previous slot.

  It holds the parent block root of the bid, then the block root of the previous slot. -/
  | bidWrongParentRoot (parentRoot expected : Root)
  /-- From Gloas: the RANDAO mix of a bid is not that of the current epoch.

  It holds the mix of the bid, then the mix of the current epoch. -/
  | bidWrongRandao (prevRandao expected : Bytes32)
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
  /-- The source of an attestation is not the justified checkpoint of its target epoch.

  It holds the epoch and root of the source, then those of the justified checkpoint. -/
  | wrongAttestationSource (sourceEpoch : Epoch) (sourceRoot : Root) (justifiedEpoch : Epoch)
      (justifiedRoot : Root)
  /-- The pending attestations of an epoch are at their list limit.

  It holds the number of pending attestations, then the limit. -/
  | tooManyPendingAttestations (count limit : Nat)
  /-- The indexed form of an attestation is not a valid indexed attestation.

  It holds the slot of the attestation and the number of validators that its indexed form names. -/
  | invalidAttestation (slot : Slot) (attesters : Nat)
  /-- A block does not hold the number of deposits that the state expects. -/
  | wrongDepositCount (count expected : Nat)
  /-- The Merkle branch of a deposit does not lead to the deposit root.

  It holds the deposit index, the root of the deposit data, and the deposit root of the state. -/
  | invalidDepositProof (index : UInt64) (leaf depositRoot : Root)
  /-- The registry of validators is at its list limit.

  It holds the limit. -/
  | registryFull (limit : Nat)
  /-- The validator of a voluntary exit is not active. -/
  | exitingValidatorNotActive (index : ValidatorIndex)
  /-- The validator of a voluntary exit has already started to exit. -/
  | exitAlreadyInitiated (index : ValidatorIndex)
  /-- A voluntary exit is for an epoch after the current epoch. -/
  | exitNotYetValid (epoch currentEpoch : Epoch)
  /-- The validator of a voluntary exit has not been active for long enough. -/
  | exitTooSoon (index : ValidatorIndex)
  /-- A voluntary exit is not signed by its validator.

  It holds the index of the validator and the signing root that the signature fails on. -/
  | invalidExitSignature (index : ValidatorIndex) (signingRoot : Root)
  /-- A pending attestation was included with no delay, which no reward can divide by. -/
  | zeroInclusionDelay
  /-- From Capella: the withdrawals before those of a reading leave it no place. -/
  | priorWithdrawalsAtLimit (count limit : Nat)
  /-- From Capella: a payload does not carry the withdrawals that the state expects.

  It holds the first position at which the two lists differ, then the length of each list.

  The payload's list comes first. -/
  | wrongWithdrawals (position count expected : Nat)
  /-- From Capella: a change of BLS credentials is for a validator without BLS credentials. -/
  | notBlsCredentials (index : ValidatorIndex)
  /-- From Capella: the credentials of a validator do not commit to the key of a change. -/
  | wrongBlsKey (index : ValidatorIndex)
  /-- From Capella: a change of BLS credentials is not signed by its key.

  It holds the index of the validator and the signing root that the signature fails on. -/
  | invalidBlsChangeSignature (index : ValidatorIndex) (signingRoot : Root)
  /-- The historical roots are at their list limit.

  It holds the limit. -/
  | historicalRootsFull (limit : Nat)
  /-- The target slot is not after the slot of the state. -/
  | slotNotAfter (slot stateSlot : Slot)
  /-- A block does not carry the signature of its proposer.

  It holds the proposer that the block names and the slot of the block. -/
  | invalidBlockSignature (proposer : ValidatorIndex) (slot : Slot)
  /-- The state root of a block is not the root of the state after it.

  It holds the state root of the block, then the root of the state after it. -/
  | wrongStateRoot (stateRoot expected : Root)
  /-- From Bellatrix: the parent hash of a payload is not the block hash of the latest payload.

  It holds the parent hash of the payload, then the block hash of the latest payload. -/
  | wrongPayloadParentHash (parentHash expected : Hash32)
  /-- From Bellatrix: a payload does not read the RANDAO mix of the current epoch.

  It holds the mix of the payload, then the mix that it must read. -/
  | wrongPayloadRandao (prevRandao expected : Bytes32)
  /-- From Bellatrix: the time of a payload is not the time of the slot of the state. -/
  | wrongPayloadTimestamp (timestamp expected : UInt64)
  /-- From Bellatrix: the execution layer rejects a payload.

  It holds the block hash of the payload. -/
  | invalidExecutionPayload (blockHash : Hash32)
  /-- From Capella: the historical summaries are at their list limit.

  It holds the limit. -/
  | historicalSummariesFull (limit : Nat)
  /-- From Altair: the sync aggregate is not the signature of its members on the parent block.

  It holds the slot of the signed block root, the number of signers, and the signing root. -/
  | invalidSyncAggregate (slot : Slot) (participants : Nat) (signingRoot : Root)
  /-- From Altair: a key of the sync committee does not decode, as the check of its sum needs.

  It holds the key that fails to decode or fails key validation. -/
  | invalidSyncCommitteeKey (pubkey : Cryptography.Bls.BLSPubkey)
  /-- From Altair: no validator holds the key of a member of the sync committee.

  It holds that key. -/
  | unknownSyncCommitteeMember (pubkey : Cryptography.Bls.BLSPubkey)
  /-- A block is of another fork than the state at its slot. -/
  | blockForkMismatch (block state : Fork)
  /-- From Electra: an attestation has a committee index other than zero. -/
  | attestationIndexNotZero (index : CommitteeIndex)
  /-- From Electra: a committee of an attestation has no attester. -/
  | noCommitteeAttester (index : CommitteeIndex)
  /-- From Electra: the validator of a voluntary exit has a pending partial withdrawal. -/
  | exitPendingWithdrawal (index : ValidatorIndex)
  /-- From Gloas: the parent payload is empty, but the block carries requests for it.

  It holds the total number of requests, over all five types. -/
  | parentRequestsNotEmpty (count : Nat)
  /-- From Gloas: the requests of the block are not those that the parent bid commits to.

  It holds the root of the requests, then the root in the parent bid. -/
  | wrongParentRequestsRoot (root expected : Root)
  /-- From Gloas: a list holds more entries than the most allowed. -/
  | tooManyOperations (count limit : Nat)
  /-- From Gloas: an attestation has an index other than zero or one. -/
  | attestationIndexAboveOne (index : CommitteeIndex)
  /-- From Gloas: an envelope does not carry the signature of its signer.

  It holds the builder and the beacon block root that the envelope names. -/
  | invalidEnvelopeSignature (builder : BuilderIndex) (blockRoot : Root)
  /-- From Gloas: an envelope names another beacon block than the latest one of the state.

  It holds the block root of the envelope, then the root of the latest block. -/
  | envelopeWrongBlockRoot (blockRoot expected : Root)
  /-- From Gloas: an envelope names another parent than that of the latest beacon block.

  It holds the parent root of the envelope, then that of the latest block header. -/
  | envelopeWrongParentRoot (parentRoot expected : Root)
  /-- From Gloas: an envelope names another builder than the bid of its block.

  It holds the builder of the envelope, then that of the bid. -/
  | envelopeWrongBuilder (builder expected : BuilderIndex)
  /-- From Gloas: a payload has another gas limit than the bid of its block.

  It holds the gas limit of the payload, then that of the bid. -/
  | wrongPayloadGasLimit (gasLimit expected : UInt64)
  /-- From Gloas: a payload has another block hash than the bid of its block.

  It holds the block hash of the payload, then that of the bid. -/
  | wrongPayloadBlockHash (blockHash expected : Hash32)
  /-- From Gloas: the requests of a payload are not those that the bid of its block commits to.

  It holds the root of the requests, then the root in the bid. -/
  | wrongPayloadRequestsRoot (root expected : Root)
  /-- From Gloas: a payload is for another slot than that of the state. -/
  | wrongPayloadSlot (slot stateSlot : Slot)
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
  | .wrongParent .. => 6
  | .proposerSlashed _ => 7
  | .invalidRandaoReveal .. => 8
  | .tooManyEth1Votes .. => 9
  | .headerSlotsDiffer .. => 10
  | .headerProposersDiffer .. => 11
  | .sameHeaders .. => 12
  | .notSlashable _ => 13
  | .invalidHeaderSignature .. => 14
  | .notSlashableData .. => 15
  | .invalidIndexedAttestation .. => 16
  | .noneSlashed .. => 17
  | .payloadAttestationNotForParent .. => 18
  | .payloadAttestationWrongSlot .. => 19
  | .invalidPayloadAttestation .. => 20
  | .selfBuildBidPaid .. => 21
  | .builderNotActive _ => 22
  | .notPayloadBuilder _ => 23
  | .bidNotCovered _ => 24
  | .invalidBidSignature .. => 25
  | .tooManyBlobCommitments .. => 26
  | .bidWrongSlot .. => 27
  | .bidAtGenesis => 28
  | .bidWrongParentHash .. => 29
  | .bidRepeatsParentHash .. => 30
  | .bidWrongParentRoot .. => 31
  | .bidWrongRandao .. => 32
  | .depositIndicesDiffer .. => 33
  | .attestationTargetNotRecent .. => 34
  | .attestationTargetNotSlotEpoch .. => 35
  | .attestationTooEarly .. => 36
  | .attestationTooLate .. => 37
  | .committeeIndexOutOfRange .. => 38
  | .aggregationBitsLength .. => 39
  | .wrongAttestationSource .. => 40
  | .tooManyPendingAttestations .. => 41
  | .invalidAttestation .. => 42
  | .wrongDepositCount .. => 43
  | .invalidDepositProof .. => 44
  | .registryFull .. => 45
  | .exitingValidatorNotActive _ => 46
  | .exitAlreadyInitiated _ => 47
  | .exitNotYetValid .. => 48
  | .exitTooSoon _ => 49
  | .invalidExitSignature .. => 50
  | .zeroInclusionDelay => 51
  | .priorWithdrawalsAtLimit .. => 61
  | .wrongWithdrawals .. => 62
  | .notBlsCredentials _ => 63
  | .wrongBlsKey _ => 64
  | .invalidBlsChangeSignature .. => 65
  | .historicalRootsFull .. => 52
  | .slotNotAfter .. => 53
  | .invalidBlockSignature .. => 54
  | .wrongStateRoot .. => 55
  | .wrongPayloadParentHash .. => 66
  | .wrongPayloadRandao .. => 67
  | .wrongPayloadTimestamp .. => 68
  | .invalidExecutionPayload .. => 69
  | .historicalSummariesFull .. => 70
  | .invalidSyncAggregate .. => 71
  | .invalidSyncCommitteeKey .. => 72
  | .unknownSyncCommitteeMember .. => 73
  | .blockForkMismatch .. => 74
  | .attestationIndexNotZero _ => 75
  | .noCommitteeAttester _ => 76
  | .exitPendingWithdrawal _ => 77
  | .parentRequestsNotEmpty .. => 78
  | .wrongParentRequestsRoot .. => 79
  | .tooManyOperations .. => 80
  | .attestationIndexAboveOne _ => 81
  | .invalidEnvelopeSignature .. => 82
  | .envelopeWrongBlockRoot .. => 83
  | .envelopeWrongParentRoot .. => 84
  | .envelopeWrongBuilder .. => 85
  | .wrongPayloadGasLimit .. => 86
  | .wrongPayloadBlockHash .. => 87
  | .wrongPayloadRequestsRoot .. => 88
  | .wrongPayloadSlot .. => 89

/-- The message of an error: its constructor and its values, on one line, with roots in hex.

Two roots in hex pass the width at which a rendering would otherwise wrap. -/
instance : ToString TransitionError where
  toString error := (repr error).pretty 1000000

/-- The first position at which two arrays differ.

When one array starts the other, it is the length of the shorter one. -/
def firstDifference {α : Type} [BEq α] (a b : Array α) : Nat :=
  ((a.zip b).findIdx? fun (x, y) => x != y).getD (min a.size b.size)

/-- An error of a state accessor, as an error of the transition. -/
def liftAccessor {α : Type} (result : Except AccessorError α) : Except TransitionError α :=
  result.mapError .accessor

/-- An error of a root, as an error of the transition. -/
def liftSsz {α : Type} (result : Except Err α) : Except TransitionError α :=
  result.mapError .ssz

/-- The BLS signature checks that the transition runs.

Each takes the public keys, the message as bytes, and the signature. -/
structure SignatureChecks where
  /-- The check of one signature by one key. -/
  verify : Cryptography.Bls.BLSPubkey → ByteArray → Cryptography.Bls.BLSSignature → Bool
  /-- The check of one signature by several keys on one message. -/
  fastAggregateVerify :
    Array Cryptography.Bls.BLSPubkey → ByteArray → Cryptography.Bls.BLSSignature → Bool

/-- The checks of the BLS signature scheme, which the transition runs on a real chain. -/
def SignatureChecks.bls : SignatureChecks where
  verify := Cryptography.Bls.Signatures.verify
  fastAggregateVerify := Cryptography.Bls.Signatures.fastAggregateVerify

/-- Checks that accept every signature.

The consensus test vectors use them for the cases that carry placeholder signatures. -/
def SignatureChecks.acceptAll : SignatureChecks where
  verify _ _ _ := true
  fastAggregateVerify _ _ _ := true

/-- From Gloas: the check that a list holds no more entries than the most allowed.

From Gloas the lists of blocks and payloads have no type bound, so each step checks its own. -/
def checkCount (count : Nat) (limit : UInt64) : Except TransitionError Unit :=
  ensure (count ≤ limit.toNat) (.tooManyOperations count limit.toNat)

end EthLib.Consensus
