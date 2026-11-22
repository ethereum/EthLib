module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Consensus.Gossip.ProposerPreferences
public import EthLib.Consensus.Gossip.SyncCommittee
public import EthLib.Consensus.Mutators
public import EthLib.Consensus.PayloadTimeliness
public import EthLib.Cryptography.Bls.Signatures

/-!
# `Consensus.HonestValidator`

The duties of an honest validator.

They are what it computes to propose, attest, aggregate and serve on a sync committee.

A validator finds its committee for an epoch, and whether it proposes a block.

From Altair, it finds whether it serves on a sync committee, and on which subnets.

From Gloas, it finds the slot of its payload timeliness committee, and the slots it will propose.

Each message it sends carries its BLS signature of the message's signing root.

The root joins the root of the message with a domain of a kind of message, a fork and a chain.

Each kind of message has its own domain type, so two kinds are signed under different domains.

Each duty signs one object at one epoch:

- The RANDAO reveal signs the epoch of the block, at that epoch.
- A block is signed at the epoch of its slot.
- Attestation data is signed at its target epoch.
- A selection proof signs a slot, at the epoch of the slot.
- An aggregate and proof is signed at the epoch of the aggregate's slot.
- A sync committee message signs a block root, at the current epoch.
- A sync selection proof signs selection data, at the epoch of its slot.
- A contribution and proof is signed at the epoch of its slot.
- From Gloas, the data of a payload attestation message is signed at the epoch of its slot.
- From Gloas, the preferences of a proposer are signed at the fork version of their slot's epoch.

The later forks, up to Heze, change none of these duties and only add others.

Gloas adds the payload timeliness duties and the preferences of proposers.

Heze adds the inclusion list committee and the signed inclusion list.

It also adds the view of the lists that a proposer and a builder put in the payload and the bid.

The steps that read the network or the execution layer are not specified here.

The choice of a head is one of them.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Why a duty of a validator has no result. -/
inductive ValidatorDutyError where
  /-- A state accessor fails. -/
  | accessor (error : AccessorError)
  /-- A root cannot be computed. -/
  | ssz (error : Err)
  /-- The BLS signature fails. -/
  | bls (error : BlsError)
  /-- A 64-bit operation has no result. -/
  | arith (error : ArithError)
  /-- An assignment is asked for an epoch after the last one whose committees are known. -/
  | epochTooFar (epoch lastEpoch : Epoch)
  /-- A sync committee assignment is asked for a period other than the current or the next. -/
  | periodOutOfRange (period currentPeriod : UInt64)
  /-- A step of the fork choice fails. -/
  | forkChoice (error : ForkChoiceError)
  /-- A validator holds no seat in the committee or the subcommittee of its message. -/
  | notInCommittee (validatorIndex : ValidatorIndex)
  /-- No message matches the one to aggregate.

  The error gives the slot and the block root of the message to aggregate.

  A message at that slot and root may still differ from it in another field. -/
  | noMessages (slot : Slot) (beaconBlockRoot : Root)
  /-- The bits of a committee exceed the limit of an attestation. -/
  | tooManyBits (count limit : Nat)
  /-- The bits of an attestation do not have one bit for each member of its committee. -/
  | bitsLength (count expected : Nat)
  /-- A committee or a subcommittee index is not below the number of them. -/
  | indexOutOfRange (index limit : UInt64)
  /-- From Gloas, a vote on a block of an earlier slot is given no empty or full payload status.

  The error gives the slot of the vote, then the slot of the head block. -/
  | pendingPayloadStatus (slot headSlot : Slot)

/-- The code of an error at the C boundary, one for each constructor. -/
def ValidatorDutyError.code : ValidatorDutyError → UInt32
  | .accessor _ => 1
  | .ssz _ => 2
  | .bls _ => 3
  | .arith _ => 4
  | .epochTooFar .. => 5
  | .periodOutOfRange .. => 6
  | .forkChoice _ => 7
  | .notInCommittee _ => 8
  | .noMessages .. => 9
  | .tooManyBits .. => 10
  | .bitsLength .. => 11
  | .indexOutOfRange .. => 12
  | .pendingPayloadStatus .. => 13

/-- The message of an error, with the values that its check compared. -/
instance : ToString ValidatorDutyError where
  toString
    | .accessor error => s!"a state accessor fails: {reprStr error}"
    | .ssz error => s!"a root cannot be computed: {reprStr error}"
    | .bls error => s!"BLS: {error.message}"
    | .arith error => s!"arithmetic: {reprStr error}"
    | .epochTooFar epoch lastEpoch =>
      s!"epoch {epoch} is after {lastEpoch}, the last epoch whose committees are known"
    | .periodOutOfRange period currentPeriod =>
      s!"sync committee period {period} is neither the current period {currentPeriod} " ++
        "nor the next"
    | .forkChoice error => s!"fork choice: {error}"
    | .notInCommittee index => s!"validator {index} has no seat in the committee of its message"
    | .noMessages slot root =>
      s!"no message matches the one to aggregate, at slot {slot} for block " ++
        hexString root.toList
    | .tooManyBits count limit => s!"{count} committee bits exceed the limit {limit}"
    | .bitsLength count expected =>
      s!"{count} aggregation bits, expected one for each of {expected} members"
    | .indexOutOfRange index limit => s!"index {index} is not below {limit}"
    | .pendingPayloadStatus slot headSlot =>
      s!"the head block at slot {headSlot}, not the slot {slot} of the vote, " ++
        "has a pending payload status"

/-! ## Assignments -/

/-- The first committee of some slots and indices that holds a validator.

It comes with its index and its slot.

The committees are cut from the given active validators and shuffle.

Each committee is cut with the given count of committees per slot.

A caller computes the shuffle and the count once, for all the committees of an epoch. -/
def findCommitteeOf (preset : Preset) (validatorIndex : ValidatorIndex) (perSlot : UInt64)
    (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    List (Slot × CommitteeIndex) →
      Except ValidatorDutyError (Option (Array ValidatorIndex × CommitteeIndex × Slot))
  -- No listed committee holds the validator.
  | [] => return none
  | (slot, index) :: rest => do
    -- The committee of the index at the slot, cut from the shuffle with the count per slot.
    let committee ← (beaconCommitteeOf preset slot index perSlot active shuffled).mapError .accessor
    -- The first committee that holds the validator gives the answer, with its index and slot.
    if validatorIndex ∈ committee then return some (committee, index, slot)
    -- Otherwise the search goes on with the rest.
    findCommitteeOf preset validatorIndex perSlot active shuffled rest

/-- The slots of an epoch, each with the indices of its committees, in order. -/
def committeePositions (state : BeaconState preset fork) (epoch : Epoch) :
    Except ValidatorDutyError (List (Slot × CommitteeIndex)) := do
  -- The `SLOTS_PER_EPOCH` slots of the epoch `e`, from slot `e * SLOTS_PER_EPOCH`.
  let slots ← (epochSlots preset epoch).mapError .arith
  -- The count `c` of committees per slot in `e`.
  let perSlot := getCommitteeCountPerSlot state epoch
  -- Each slot with each index `i`, for `0 ≤ i < c`, slot by slot.
  return slots.flatMap fun slot =>
    (List.range perSlot.toNat).map fun index => (slot, index.toUInt64)

/-- The committee of a validator in an epoch, with the index and the slot of the committee.

A validator that is not active in the epoch has no committee.

It fails for an epoch after the next one.

It also fails when a committee it reads, up to the one with the validator, has no value.

It fails too when the next epoch, the first slot or that slot plus an epoch overflows 64 bits.

The committees share one shuffle of the active validators, computed at most once per call. -/
def getCommitteeAssignment (state : BeaconState preset fork) (epoch : Epoch)
    (validatorIndex : ValidatorIndex) :
    Except ValidatorDutyError (Option (Array ValidatorIndex × CommitteeIndex × Slot)) := do
  -- Let `e` be the epoch asked, and `n = c + 1` for the current epoch `c`.
  let nextEpoch ← (addChecked (getCurrentEpoch state) 1).mapError .arith
  -- `e ≤ n`, since the committees of later epochs are not known yet.
  if epoch ≤ nextEpoch then
    match ← committeePositions state epoch with
    -- Only a preset with no slot in an epoch lists no committee.
    --
    -- There a failing shuffle would turn the empty answer into an error, so it is not read.
    | [] => return none
    -- The listed slots are all in the epoch, so their committees come from its shuffle.
    --
    -- The first committee alone reads the same shuffle before its cut.
    --
    -- So reading the shuffle first changes no error.
    | positions@(_ :: _) =>
      let (active, shuffled) ← (attesterShuffle state epoch).mapError .accessor
      -- The first committee of `e` that holds the validator, slot by slot and index by index.
      findCommitteeOf preset validatorIndex (getCommitteeCountPerSlot state epoch) active shuffled
        positions
  -- An epoch after `n` is an error.
  else throw (.epochTooFar epoch nextEpoch)

/-- Whether a validator proposes the block of the slot of a state. -/
def isProposer (state : BeaconState preset fork) (validatorIndex : ValidatorIndex) :
    Except ValidatorDutyError Bool := do
  -- The proposer of the slot of the state is the validator.
  return (← (getBeaconProposerIndex state).mapError .accessor) == validatorIndex

/-- From Gloas: the first of some slots whose payload timeliness committee holds a validator. -/
def findPtcSlot (config : Config) (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (validatorIndex : ValidatorIndex) : List Slot → Except ValidatorDutyError (Option Slot)
  -- No listed slot has a committee that holds the validator.
  | [] => return none
  | slot :: rest => do
    -- The payload timeliness committee of the slot.
    let committee ← (getPtc config state gloas slot).mapError .accessor
    -- The first slot whose committee holds the validator gives the answer.
    if validatorIndex ∈ committee.toList then return some slot
    -- Otherwise the search goes on with the rest.
    findPtcSlot config state gloas validatorIndex rest

/-- From Gloas: the slot of an epoch whose payload timeliness committee holds a validator.

A validator in no committee of the epoch has no slot.

It fails for an epoch more than the lookahead of seeds after the current one.

It also fails when the committee of a slot has no value.

It fails too when that last epoch, the first slot or that slot plus an epoch overflows 64 bits. -/
def getPtcAssignment (config : Config) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (epoch : Epoch) (validatorIndex : ValidatorIndex) :
    Except ValidatorDutyError (Option Slot) := do
  -- Let `e` be the epoch asked, and `c` the current epoch.
  --
  -- `e ≤ c + MIN_SEED_LOOKAHEAD`, and a later epoch is an error.
  let maxEpoch ← (addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD).mapError .arith
  unless epoch ≤ maxEpoch do throw (.epochTooFar epoch maxEpoch)
  -- The first slot of `e` whose committee holds the validator, slot by slot.
  findPtcSlot config state gloas validatorIndex (← (epochSlots preset epoch).mapError .arith)

/-- From Gloas: the slots after the slot of a state that a validator proposes, in order.

The state keeps the proposers from the start of its epoch, for the lookahead of seeds.

It fails when the first slot of the epoch, or a slot of the lookahead, overflows 64 bits. -/
def getUpcomingProposalSlots (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (validatorIndex : ValidatorIndex) : Except ValidatorDutyError (List Slot) := do
  -- The first slot `x_0 = c * SLOTS_PER_EPOCH` of the current epoch `c`.
  let startSlot ← (computeStartSlotAtEpoch preset (getCurrentEpoch state)).mapError .arith
  -- The proposers of the slots from `x_0` on, one for each slot.
  let lookahead := state.proposerLookahead (Nat.le_trans (by decide) gloas)
  -- Each offset of the lookahead gives a slot, which must be a 64-bit slot.
  let slots ← (List.finRange lookahead.size).mapM fun offset =>
    if startSlot.toNat + offset.val < 2 ^ 64 then
      .ok (startSlot + offset.val.toUInt64, lookahead[offset])
    else .error (.arith .overflow)
  -- The slots `x` with `s < x`, for the slot `s` of the state, whose proposer is the validator.
  return (slots.filter fun (slot, proposer) => state.slot < slot ∧ proposer = validatorIndex).map
    (·.1)

/-- From Altair: whether a validator serves on the sync committee of the period of an epoch.

It fails for a period other than the current one or the next. -/
def isAssignedToSyncCommittee (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (epoch : Epoch) (validatorIndex : ValidatorIndex) : Except ValidatorDutyError Bool := do
  -- The period `p = floor(e / EPOCHS_PER_SYNC_COMMITTEE_PERIOD)` of the epoch `e`.
  let period := computeSyncCommitteePeriod preset epoch
  -- The period `q` of the current epoch.
  let currentPeriod := computeSyncCommitteePeriod preset (getCurrentEpoch state)
  -- `p` is `q` or `q + 1`, since the state holds only those two committees.
  let nextPeriod ← (addChecked currentPeriod 1).mapError .arith
  unless period = currentPeriod ∨ period = nextPeriod do
    throw (.periodOutOfRange period currentPeriod)
  -- The key of the validator.
  let pubkey := (← (getValidator state validatorIndex).mapError .accessor).pubkey
  -- In period `q` the key is in the current committee.
  if period = currentPeriod then
    return (state.currentSyncCommittee altair).value.pubkeys.contains pubkey
  -- In period `q + 1` the key is in the next committee.
  else
    return (state.nextSyncCommittee altair).value.pubkeys.contains pubkey

/-- From Altair: the sync committee subnets of a validator for the next slot.

The subnets come once each, in increasing order. -/
def computeSubnetsForSyncCommittee (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (validatorIndex : ValidatorIndex) : Except ValidatorDutyError (List UInt64) := do
  -- The committee of the next slot: the current one, unless the next slot starts a new period.
  let syncCommittee ← (syncCommitteeAtNextSlot state altair).mapError .arith
  -- The key of the validator.
  let targetPubkey := (← (getValidator state validatorIndex).mapError .accessor).pubkey
  -- Let `m = floor(SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT)`, the size of a subcommittee.
  --
  -- Each seat `j` of the key gives the subnet `floor(j / m)`.
  --
  -- The subnets form a set, given here once each, in increasing order.
  return (syncSubnetsOfPubkey syncCommittee targetPubkey).mergeSort (· ≤ ·)

/-! ## Signatures -/

/-- The signature of an object by a secret key, under a domain type at an epoch. -/
def signAtEpoch {α : Type} [SszType α] (config : Config) (state : BeaconState preset fork)
    (domainType : DomainType) (epoch : Epoch) (object : α) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature := do
  -- The domain of the type at the epoch, from the state.
  let domain ← (getDomain config state domainType (some epoch)).mapError .accessor
  -- The BLS signature of the signing root of the object under that domain.
  let signingRoot ← (computeSigningRoot object domain).mapError .ssz
  (Signatures.sign key (packBytes signingRoot)).mapError .bls

/-- The RANDAO reveal of a block: the signature of the epoch of its slot. -/
def getEpochSignature (config : Config) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  -- The epoch `e` of the slot of the block.
  let epoch := computeEpochAtSlot preset block.slot
  -- The signature of `e` under the RANDAO domain at `e`.
  signAtEpoch config state DOMAIN_RANDAO epoch epoch key

/-- The signature of a block by its proposer, in the epoch of its slot. -/
def getBlockSignature (config : Config) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  -- The signature of the block under the proposer domain at the epoch of its slot.
  signAtEpoch config state DOMAIN_BEACON_PROPOSER (computeEpochAtSlot preset block.slot) block key

/-- The signature of attestation data, in its target epoch. -/
def getAttestationSignature (config : Config) (state : BeaconState preset fork)
    (attestationData : AttestationData) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  -- The signature of the data under the attester domain at its target epoch.
  signAtEpoch config state DOMAIN_BEACON_ATTESTER attestationData.target.epoch attestationData key

/-- The selection proof of a slot: the signature of the slot, in its epoch.

It decides whether the validator aggregates for its committee in that slot. -/
def getSlotSignature (config : Config) (state : BeaconState preset fork) (slot : Slot)
    (key : Signatures.SecretKey) : Except ValidatorDutyError BLSSignature :=
  -- The signature of the slot under the selection proof domain at the epoch of the slot.
  signAtEpoch config state DOMAIN_SELECTION_PROOF (computeEpochAtSlot preset slot) slot key

/-- An aggregate with the index of its aggregator and its selection proof. -/
def getAggregateAndProof (config : Config) (state : BeaconState preset fork)
    (aggregatorIndex : ValidatorIndex) (aggregate : Attestation preset fork)
    (key : Signatures.SecretKey) : Except ValidatorDutyError (AggregateAndProof preset fork) := do
  -- The aggregate and its aggregator, with the selection proof of the slot of the aggregate.
  return {
    aggregatorIndex, aggregate,
    selectionProof := ← getSlotSignature config state aggregate.data.slot key }

/-- The signature of an aggregate and proof, in the epoch of the aggregate's slot. -/
def getAggregateAndProofSignature (config : Config) (state : BeaconState preset fork)
    (aggregateAndProof : AggregateAndProof preset fork) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  -- The signature under the aggregate and proof domain at the epoch of the aggregate's slot.
  signAtEpoch config state DOMAIN_AGGREGATE_AND_PROOF
    (computeEpochAtSlot preset aggregateAndProof.aggregate.data.slot) aggregateAndProof key

/-- From Altair: the message of a sync committee member for a block root, at the slot of the state.
-/
def getSyncCommitteeMessage (config : Config) (state : BeaconState preset fork) (blockRoot : Root)
    (validatorIndex : ValidatorIndex) (key : Signatures.SecretKey) :
    Except ValidatorDutyError SyncCommitteeMessage := do
  -- The signature of the root under the sync committee domain at the current epoch.
  let signature ←
    signAtEpoch config state DOMAIN_SYNC_COMMITTEE (getCurrentEpoch state) blockRoot key
  -- The message names the slot of the state, the root and the validator.
  return { slot := state.slot, beaconBlockRoot := blockRoot, validatorIndex, signature }

/-- From Altair: the selection proof of a subcommittee at a slot, in the epoch of the slot. -/
def getSyncCommitteeSelectionProof (config : Config) (state : BeaconState preset fork)
    (slot : Slot) (subcommitteeIndex : UInt64) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  -- The signature of the slot and the subcommittee index, under the sync selection proof domain.
  signAtEpoch config state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF (computeEpochAtSlot preset slot)
    ({ slot, subcommitteeIndex } : SyncAggregatorSelectionData) key

/-- From Altair: a contribution with the index of its aggregator and its selection proof. -/
def getContributionAndProof (config : Config) (state : BeaconState preset fork)
    (aggregatorIndex : ValidatorIndex) (contribution : SyncCommitteeContribution preset)
    (key : Signatures.SecretKey) : Except ValidatorDutyError (ContributionAndProof preset) := do
  -- The selection proof of the slot and the subcommittee of the contribution.
  let selectionProof ← getSyncCommitteeSelectionProof config state contribution.slot
    contribution.subcommitteeIndex key
  -- The contribution and its aggregator, with that proof.
  return { aggregatorIndex, contribution, selectionProof }

/-- From Altair: the signature of a contribution and proof, in the epoch of its slot. -/
def getContributionAndProofSignature (config : Config) (state : BeaconState preset fork)
    (contributionAndProof : ContributionAndProof preset) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  -- The signature under the contribution and proof domain at the epoch of the slot.
  signAtEpoch config state DOMAIN_CONTRIBUTION_AND_PROOF
    (computeEpochAtSlot preset contributionAndProof.contribution.slot) contributionAndProof key

/-- From Gloas: the signature of the data of a payload attestation message, at its slot's epoch.

The message names its validator, but the signature covers only the data. -/
def getPayloadAttestationMessageSignature (config : Config) (state : BeaconState preset fork)
    (message : PayloadAttestationMessage) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature :=
  -- The signature of the data alone under the PTC attester domain at the epoch of its slot.
  signAtEpoch config state DOMAIN_PTC_ATTESTER (computeEpochAtSlot preset message.data.slot)
    message.data key

/-- From Gloas: the signature of the preferences of a proposer.

The domain is that of preferences, at the fork version of the proposal epoch.

So a proposer can sign its preferences for the first epoch of a fork in the epoch before it. -/
def getProposerPreferencesSignature (config : Config) (state : BeaconState preset fork)
    (preferences : ProposerPreferences) (key : Signatures.SecretKey) :
    Except ValidatorDutyError BLSSignature := do
  -- The signing root under the preferences domain, at the fork version of the proposal epoch.
  let root ← (proposerPreferencesSigningRoot config state preferences).mapError .ssz
  -- The BLS signature of that root.
  (Signatures.sign key (packBytes root)).mapError .bls

/-- From Gloas: the signed preferences of a proposer for a slot, on the chain of a head.

The dependent root is the block that fixes the proposers of the epoch of the slot, on that chain. -/
def getSignedProposerPreferences (config : Config) (store : Store preset fork)
    (state : BeaconState preset fork) (headRoot : Root) (proposalSlot : Slot)
    (validatorIndex : ValidatorIndex) (feeRecipient : ExecutionAddress) (targetGasLimit : UInt64)
    (key : Signatures.SecretKey) : Except ValidatorDutyError SignedProposerPreferences := do
  -- The dependent root of the epoch of the proposal slot, on the chain of the head.
  let dependentRoot ← (store.getShufflingDependentRoot headRoot
    (computeEpochAtSlot preset proposalSlot)).mapError .forkChoice
  -- The preferences of the validator for the slot, with that root.
  let message := { dependentRoot, proposalSlot, validatorIndex, feeRecipient, targetGasLimit }
  -- The preferences with their signature.
  return { message, signature := ← getProposerPreferencesSignature config state message key }

/-! ## Inclusion lists -/

/-- From Heze: the signed inclusion list of a committee member for a slot, on the chain of a head.

The dependent root is the block that fixes the committees of the epoch of the slot, on that chain.

The transactions are those that the execution layer offers from its mempool. -/
def getSignedInclusionList (config : Config) (store : Store preset fork)
    (state : BeaconState preset fork) (headRoot : Root) (slot : Slot)
    (validatorIndex : ValidatorIndex) (transactions : List InclusionListTransaction)
    (key : Signatures.SecretKey) : Except ValidatorDutyError SignedInclusionList := do
  -- The dependent root of the epoch of the slot, on the chain of the head.
  let dependentRoot ← (store.getShufflingDependentRoot headRoot
    (computeEpochAtSlot preset slot)).mapError .forkChoice
  -- The list names the slot, the member, that root and the transactions.
  let message : InclusionList :=
    { slot, validatorIndex, dependentRoot, transactions := ⟨transactions.toArray⟩ }
  -- The signature of the list by the member.
  let signature ← (getInclusionListSignature config state message key).mapError fun
    | .root error => .ssz error
    | .bls error => .bls error
  return { message, signature }

/-- From Heze: the key of the inclusion lists that a payload of a slot answers to.

A slot 0 has no slot before it, and that is an error. -/
def inclusionListView (store : Store preset fork) (parentRoot : Root) (slot : Slot) :
    Except ValidatorDutyError (Slot × Root) := do
  -- The slot `s - 1` before the slot `s`.
  let previous ← (subChecked slot 1).mapError .arith
  -- The dependent root of the epoch of `s - 1`, on the chain of the parent block.
  let dependentRoot ← (store.getShufflingDependentRoot parentRoot
    (computeEpochAtSlot preset previous)).mapError .forkChoice
  -- The key is `s - 1` with that root.
  return (previous, dependentRoot)

/-- From Heze: the transactions that a proposer asks its payload to include, on a head.

The payload is for the slot of the state.

They come from every valid list that the proposer saw, timely or not, without equivocators. -/
def getPayloadInclusionListTransactions (store : Store preset fork) (heze : .hegota ≤ fork)
    (state : BeaconState preset fork) (headRoot : Root) :
    Except ValidatorDutyError (List InclusionListTransaction) := do
  -- The key of the lists for the slot of the state, on the chain of the head.
  let (previous, dependentRoot) ← inclusionListView store headRoot state.slot
  -- The transactions of the lists under that key, timely or not, without equivocators.
  return (store.inclusionLists heze).transactions previous dependentRoot false

/-- From Heze: the bits that a builder sets in its bid, from the lists it saw. -/
def getBidInclusionListBits (store : Store preset fork) (heze : .hegota ≤ fork)
    (state : BeaconState preset fork) (bid : ExecutionPayloadBid preset fork) :
    Except ValidatorDutyError (InclusionListBits preset) := do
  -- The key of the lists for the slot of the bid, on the chain of its parent block.
  let (previous, dependentRoot) ← inclusionListView store bid.parentBlockRoot bid.slot
  -- The inclusion list committee of the slot before the bid.
  let committee ← (getInclusionListCommittee state previous).mapError .accessor
  -- A seat is set when its member sent a list that counts under the key, timely or not.
  return (store.inclusionLists heze).bits committee previous dependentRoot false

/-- From Heze: whether the bits of a bid cover every list that the proposer saw.

A proposer includes only a bid whose bits set every seat whose member sent a list that counts. -/
def isBidInclusionListInclusive (store : Store preset fork) (heze : .hegota ≤ fork)
    (state : BeaconState preset fork) (bid : ExecutionPayloadBid preset fork) :
    Except ValidatorDutyError Bool := do
  -- The key of the lists for the slot of the bid, on the chain of its parent block.
  let (previous, dependentRoot) ← inclusionListView store bid.parentBlockRoot bid.slot
  -- The inclusion list committee of the slot before the bid.
  let committee ← (getInclusionListCommittee state previous).mapError .accessor
  -- Each seat that the lists seen set, timely or not, is set in the bits of the bid.
  return (store.inclusionLists heze).isInclusive committee previous dependentRoot
    (bid.inclusionListBits heze) false

end EthLib.Consensus
