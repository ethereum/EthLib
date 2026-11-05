module

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

/-- An assertion of the rule: success when the condition holds, and the error otherwise. -/
def ensure (condition : Prop) [Decidable condition] (error : TransitionError) :
    Except TransitionError Unit :=
  if condition then .ok () else .error error

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
