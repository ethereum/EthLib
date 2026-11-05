module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.Transition.Block`

The first steps of a block: its header, its RANDAO reveal and its vote on the deposit contract.

Also the slashings of proposers and attesters, and the check of the block signature.

The rules are those of Phase 0, which no later fork changes up to Fulu.

Gloas also rejects an indexed attestation with more indices than one slot can hold.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-- The state after the header of a block.

The block must be at the slot of the state, after the latest block, and from its proposer.

Its parent must be the latest block, and its proposer must not be slashed.

The header of the block becomes the latest one, with a zero state root until the next slot. -/
def processBlockHeader (state : BeaconState preset fork) (block : BeaconBlock preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  ensure (block.slot = state.slot) (.slotMismatch block.slot state.slot)
  ensure (state.latestBlockHeader.slot < block.slot)
    (.notNewer block.slot state.latestBlockHeader.slot)
  let proposer ← liftAccessor (getBeaconProposerIndex state)
  ensure (block.proposerIndex = proposer) (.wrongProposer block.proposerIndex proposer)
  let parentRoot ← liftSsz (hashTreeRoot state.latestBlockHeader)
  ensure (block.parentRoot = parentRoot) .wrongParent
  let bodyRoot ← liftSsz (hashTreeRoot block.body)
  let validator ← liftAccessor (getValidator state block.proposerIndex)
  ensure (validator.slashed = false) (.proposerSlashed block.proposerIndex)
  return { state with
    latestBlockHeader :=
      { slot := block.slot, proposerIndex := block.proposerIndex, parentRoot := block.parentRoot,
        stateRoot := Vector.replicate 32 0, bodyRoot } }

/-- The state after the RANDAO reveal of a block.

The reveal must be the proposer's signature of the current epoch.

Its SHA-256 hash is XORed into the mix of the epoch. -/
def processRandao (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (body : BeaconBlockBody preset fork) : Except TransitionError (BeaconState preset fork) := do
  let epoch := getCurrentEpoch state
  let proposer ← liftAccessor (getValidator state (← liftAccessor (getBeaconProposerIndex state)))
  let domain ← liftAccessor (getDomain config state DOMAIN_RANDAO)
  let signingRoot ← liftSsz (computeSigningRoot epoch domain)
  ensure (checks.verify (packBytes proposer.pubkey) (packBytes signingRoot)
    (packBytes body.randaoReveal) = true) .invalidRandaoReveal
  let mix ← liftAccessor (getRandaoMix state epoch)
  let mix := Vector.zipWith (· ^^^ ·) mix (sha256Bytes32 (packBytes body.randaoReveal))
  return { state with
    randaoMixes := state.randaoMixes.set! (epoch % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat mix }

/-- The state after the vote of a block on the deposit contract.

The vote joins the votes of the period.

It wins once more than half the slots of the period cast it.

A vote past the limit of the list is an error. -/
def processEth1Data (state : BeaconState preset fork) (body : BeaconBlockBody preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let votes := state.eth1DataVotes.data.push body.eth1Data
  if bound : votes.size ≤ preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat
  then
    let slots ← liftAccessor (liftArith
      (mulChecked preset.EPOCHS_PER_ETH1_VOTING_PERIOD preset.SLOTS_PER_EPOCH))
    let state := { state with eth1DataVotes := ⟨votes, bound⟩ }
    if slots.toNat < votes.count body.eth1Data * 2 then
      return { state with eth1Data := body.eth1Data }
    else return state
  else throw .tooManyEth1Votes

/-- Whether Casper FFG forbids a validator to sign both votes.

A double vote is two different votes for one target epoch.

A surround vote has a source and a target strictly around those of the other vote. -/
def isSlashableAttestationData (data1 data2 : AttestationData) : Bool :=
  (data1 != data2 && data1.target.epoch == data2.target.epoch) ||
    (data1.source.epoch < data2.source.epoch && data2.target.epoch < data1.target.epoch)

/-- Whether an indexed attestation is valid.

Its indices must be nonempty, strictly increasing, and from Gloas at most what one slot can hold.

Its signature must be the aggregate signature of its validators on its data.

An index that names no validator is an error. -/
def isValidIndexedAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (attestation : IndexedAttestation preset fork) :
    Except TransitionError Bool := do
  let indices := attestation.attestingIndices.data.toList
  if indices = [] ∨ indices ≠ sortedSet indices ∨
      (.glamsterdam ≤ fork ∧ maxAttesters preset fork < indices.length) then
    return false
  else
    let pubkeys ← indices.toArray.mapM fun index => do
      return packBytes (← liftAccessor (getValidator state index)).pubkey
    let domain ← liftAccessor
      (getDomain config state DOMAIN_BEACON_ATTESTER (some attestation.data.target.epoch))
    let signingRoot ← liftSsz (computeSigningRoot attestation.data domain)
    return checks.fastAggregateVerify pubkeys (packBytes signingRoot)
      (packBytes attestation.signature)

/-- The check that a signed header is signed by a key, in the epoch of its slot. -/
def checkHeaderSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (pubkey : BLSPubkey) (signed : SignedBeaconBlockHeader) :
    Except TransitionError Unit := do
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_PROPOSER
    (some (computeEpochAtSlot preset signed.message.slot)))
  let signingRoot ← liftSsz (computeSigningRoot signed.message domain)
  ensure (checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature) =
    true) .invalidHeaderSignature

/-- The state after a proposer slashing.

Its two headers must differ, with one slot and one proposer.

The proposer must have signed both.

The proposer must be slashable in the current epoch, and is slashed. -/
def processProposerSlashing (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (slashing : ProposerSlashing) :
    Except TransitionError (BeaconState preset fork) := do
  let header1 := slashing.signedHeader1.message
  let header2 := slashing.signedHeader2.message
  ensure (header1.slot = header2.slot) .headerSlotsDiffer
  ensure (header1.proposerIndex = header2.proposerIndex) .headerProposersDiffer
  ensure (header1 ≠ header2) .sameHeaders
  let proposer ← liftAccessor (getValidator state header1.proposerIndex)
  ensure (isSlashableValidator proposer (getCurrentEpoch state) = true)
    (.notSlashable header1.proposerIndex)
  checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader1
  checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader2
  liftAccessor (slashValidator config state header1.proposerIndex)

/-- One step of an attester slashing: slash a validator if it may be slashed, and record it.

The flag records whether a step has slashed a validator. -/
def slashIfSlashable (config : Config) (step : BeaconState preset fork × Bool)
    (index : ValidatorIndex) : Except TransitionError (BeaconState preset fork × Bool) := do
  let (state, slashedAny) := step
  if isSlashableValidator (← liftAccessor (getValidator state index)) (getCurrentEpoch state) then
    return (← liftAccessor (slashValidator config state index), true)
  else return (state, slashedAny)

/-- The validators in both attestations of an attester slashing, in increasing order. -/
def slashingIndices (slashing : AttesterSlashing preset fork) : List ValidatorIndex :=
  let second := slashing.attestation2.attestingIndices.data.toList
  sortedSet (slashing.attestation1.attestingIndices.data.toList.filter (· ∈ second))

/-- The state after an attester slashing.

Its two attestations must be valid, and Casper FFG must forbid signing both.

Each validator in both that may be slashed is slashed, in increasing order of index.

At least one validator must be slashed. -/
def processAttesterSlashing (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (slashing : AttesterSlashing preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  ensure (isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data = true)
    .notSlashableData
  let valid1 ← isValidIndexedAttestation config checks state slashing.attestation1
  ensure (valid1 = true) .invalidIndexedAttestation
  let valid2 ← isValidIndexedAttestation config checks state slashing.attestation2
  ensure (valid2 = true) .invalidIndexedAttestation
  let (state, slashedAny) ←
    (slashingIndices slashing).foldlM (slashIfSlashable config) (state, false)
  ensure (slashedAny = true) .noneSlashed
  return state

/-- Whether a signed block carries the signature of its proposer, in the current epoch. -/
def verifyBlockSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBeaconBlock preset fork) :
    Except TransitionError Bool := do
  let proposer ← liftAccessor (getValidator state signed.message.proposerIndex)
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_PROPOSER)
  let signingRoot ← liftSsz (computeSigningRoot signed.message domain)
  return checks.verify (packBytes proposer.pubkey) (packBytes signingRoot)
    (packBytes signed.signature)

end EthLib.Consensus
