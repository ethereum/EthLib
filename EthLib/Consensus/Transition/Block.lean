module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.Transition.Block`

The first steps of a block: its header, its RANDAO reveal and its vote on the deposit contract.

Also the slashings of proposers and attesters, and the check of the block signature.

The rules are those of Phase 0, which no later fork changes up to Fulu.

Gloas also rejects an indexed attestation with more indices than one slot can hold.

[EIP-7688] asks for such a check on each list that it makes progressive.

[EIP-7688]: https://eips.ethereum.org/EIPS/eip-7688#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-- The state after the header of a block. -/
def processBlockHeader (state : BeaconState preset fork) (block : BeaconBlock preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- The block is at the slot of the state.
  ensure (block.slot = state.slot) (.slotMismatch block.slot state.slot)
  -- The block is newer than the latest block header.
  ensure (state.latestBlockHeader.slot < block.slot)
    (.notNewer block.slot state.latestBlockHeader.slot)
  -- Its proposer index is that of the proposer of the slot.
  let proposer ← liftAccessor (getBeaconProposerIndex state)
  ensure (block.proposerIndex = proposer) (.wrongProposer block.proposerIndex proposer)
  -- Its parent root is the root of the latest block header.
  let parentRoot ← liftSsz (hashTreeRoot state.latestBlockHeader)
  ensure (block.parentRoot = parentRoot) (.wrongParent block.parentRoot parentRoot)
  let bodyRoot ← liftSsz (hashTreeRoot block.body)
  -- Its proposer is not slashed.
  --
  -- The rule checks this after it replaces the header.
  --
  -- The header holds no validator, so the order changes nothing.
  let validator ← liftAccessor (getValidator state block.proposerIndex)
  ensure (validator.slashed = false) (.proposerSlashed block.proposerIndex)
  -- The header of the block becomes the latest one, with the root of its body.
  --
  -- Its state root stays 32 zero bytes until the next slot caches it.
  return { state with
    latestBlockHeader :=
      { slot := block.slot, proposerIndex := block.proposerIndex, parentRoot := block.parentRoot,
        stateRoot := Vector.replicate 32 0, bodyRoot } }

/-- The state after the RANDAO reveal of a block. -/
def processRandao (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (body : BeaconBlockBody preset fork) : Except TransitionError (BeaconState preset fork) := do
  -- The current epoch `e` and the proposer of the slot.
  let epoch := getCurrentEpoch state
  let index ← liftAccessor (getBeaconProposerIndex state)
  let proposer ← liftAccessor (getValidator state index)
  -- The reveal is the proposer's signature of `e`, under the RANDAO domain.
  let domain ← liftAccessor (getDomain config state DOMAIN_RANDAO)
  let signingRoot ← liftSsz (computeSigningRoot epoch domain)
  ensure (checks.verify proposer.pubkey (packBytes signingRoot)
    body.randaoReveal = true) (.invalidRandaoReveal index epoch)
  -- The new mix is the mix of `e` XOR the SHA-256 hash of the reveal.
  let mix ← liftAccessor (getRandaoMix state epoch)
  let mix :=
    Vector.zipWith (· ^^^ ·) mix (Cryptography.Hash.Sha256.hash32 (packBytes body.randaoReveal))
  -- It is entry `e mod EPOCHS_PER_HISTORICAL_VECTOR` of the mixes.
  let randaoMixes ← liftAccessor (writeCircularRooted state.randaoMixes epoch mix)
  return { state with randaoMixes }

/-- The state after the vote of a block on the deposit contract.

The step exists only before Heze, which removes the vote. -/
def processEth1Data (before : fork < .hegota) (state : BeaconState preset fork)
    (body : BeaconBlockBody preset fork) : Except TransitionError (BeaconState preset fork) := do
  -- The vote `v` of the block joins the votes of the period.
  let vote := body.eth1Data before
  let votes := (state.eth1DataVotes before).data.push vote
  -- The list holds at most one vote per slot of the period, so a vote past it is an error.
  if bound : votes.size ≤ preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat
  then
    -- The period has `EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH` slots.
    let slots ← liftAccessor (liftArith
      (mulChecked preset.EPOCHS_PER_ETH1_VOTING_PERIOD preset.SLOTS_PER_EPOCH))
    let state := { state with eth1DataVotes := fun _ => ⟨votes, bound⟩ }
    -- `v` wins once twice its count of votes exceeds the slots of the period.
    if slots.toNat < votes.count vote * 2 then
      return { state with eth1Data := fun _ => vote }
    else return state
  else throw (.tooManyEth1Votes votes.size
    (preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat))

/-- Whether Casper FFG forbids a validator to sign both votes.

These are the two slashing conditions of [Casper FFG], §2.

The votes link `s_1` to `t_1` and `s_2` to `t_2`.

[Casper FFG]: https://arxiv.org/abs/1710.09437v4
-/
def isSlashableAttestationData (data1 data2 : AttestationData) : Bool :=
  -- A double vote: two different attestation data with `t_1 = t_2`, heights being epochs here.
  --
  -- The data hold the head vote too, so one link with two heads is a double vote here.
  --
  -- A surround vote: `s_1 < s_2` and `t_2 < t_1`.
  --
  -- The paper's surround also has `s_2 < t_2`, which this rule does not ask.
  (data1 != data2 && data1.target.epoch == data2.target.epoch) ||
    (data1.source.epoch < data2.source.epoch && data2.target.epoch < data1.target.epoch)

/-- Whether an indexed attestation is valid.

An index that names no validator is an error. -/
def isValidIndexedAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (attestation : IndexedAttestation preset fork) :
    Except TransitionError Bool := do
  let indices := attestation.attestingIndices.data.toList
  -- The indices are nonempty and strictly increasing: sorted, with each index once.
  --
  -- From Gloas they number at most `MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT`.
  --
  -- EIP-7688 asks for that check, since it makes the list of indices progressive.
  if indices = [] ∨ indices ≠ sortedSet indices ∨
      (.glamsterdam ≤ fork ∧ maxAttesters preset fork < indices.length) then
    return false
  else
    -- The public keys of the validators at the indices, in order.
    let pubkeys ← indices.toArray.mapM fun index => do
      return (← liftAccessor (getValidator state index)).pubkey
    -- The domain of attesters at the target epoch of the data.
    let domain ← liftAccessor
      (getDomain config state DOMAIN_BEACON_ATTESTER (some attestation.data.target.epoch))
    -- The signature is their aggregate signature of the data, which FastAggregateVerify checks.
    let signingRoot ← liftSsz (computeSigningRoot attestation.data domain)
    return checks.fastAggregateVerify pubkeys (packBytes signingRoot)
      attestation.signature

/-- The check that a signed header is signed by a key, in the epoch of its slot. -/
def checkHeaderSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (pubkey : BLSPubkey) (signed : SignedBeaconBlockHeader) :
    Except TransitionError Unit := do
  -- The domain of proposers at the epoch of the slot of the header.
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_PROPOSER
    (some (computeEpochAtSlot preset signed.message.slot)))
  -- The signature of the header verifies under the key.
  let signingRoot ← liftSsz (computeSigningRoot signed.message domain)
  ensure (checks.verify pubkey (packBytes signingRoot) signed.signature = true)
    (.invalidHeaderSignature signed.message.proposerIndex signingRoot)

/-- The state after a proposer slashing. -/
def processProposerSlashing (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (slashing : ProposerSlashing) :
    Except TransitionError (BeaconState preset fork) := do
  let header1 := slashing.signedHeader1.message
  let header2 := slashing.signedHeader2.message
  -- The two headers have one slot.
  ensure (header1.slot = header2.slot) (.headerSlotsDiffer header1.slot header2.slot)
  -- They have one proposer.
  ensure (header1.proposerIndex = header2.proposerIndex)
    (.headerProposersDiffer header1.proposerIndex header2.proposerIndex)
  -- They differ.
  ensure (header1 ≠ header2) (.sameHeaders header1.slot header1.proposerIndex)
  -- The proposer is slashable in the current epoch.
  let proposer ← liftAccessor (getValidator state header1.proposerIndex)
  ensure (isSlashableValidator proposer (getCurrentEpoch state) = true)
    (.notSlashable header1.proposerIndex)
  -- The proposer signed both headers.
  checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader1
  checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader2
  -- The proposer is slashed.
  liftAccessor (slashValidator config state header1.proposerIndex)

/-- One step of an attester slashing: slash a validator if it may be slashed, and record it.

The flag records whether a step has slashed a validator. -/
def slashIfSlashable (config : Config) (step : BeaconState preset fork × Bool)
    (index : ValidatorIndex) : Except TransitionError (BeaconState preset fork × Bool) := do
  let (state, slashedAny) := step
  -- A validator slashable in the current epoch is slashed, and the flag is set.
  if isSlashableValidator (← liftAccessor (getValidator state index)) (getCurrentEpoch state) then
    return (← liftAccessor (slashValidator config state index), true)
  else return (state, slashedAny)

/-- The validators in both attestations of an attester slashing, in increasing order. -/
def slashingIndices (slashing : AttesterSlashing preset fork) : List ValidatorIndex :=
  -- The intersection of the two sets of indices, sorted.
  let second := slashing.attestation2.attestingIndices.data.toList
  sortedSet (slashing.attestation1.attestingIndices.data.toList.filter (· ∈ second))

/-- The state after an attester slashing. -/
def processAttesterSlashing (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (slashing : AttesterSlashing preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let data1 := slashing.attestation1.data
  let data2 := slashing.attestation2.data
  -- Casper FFG forbids a validator to sign both data.
  ensure (isSlashableAttestationData data1 data2 = true)
    (.notSlashableData data1.source.epoch data1.target.epoch data2.source.epoch
      data2.target.epoch)
  -- Both indexed attestations are valid.
  let valid1 ← isValidIndexedAttestation config checks state slashing.attestation1
  ensure (valid1 = true) (.invalidIndexedAttestation 1)
  let valid2 ← isValidIndexedAttestation config checks state slashing.attestation2
  ensure (valid2 = true) (.invalidIndexedAttestation 2)
  -- Each validator in both that is slashable is slashed, in increasing order of index.
  let candidates := slashingIndices slashing
  let (state, slashedAny) ← candidates.foldlM (slashIfSlashable config) (state, false)
  -- At least one validator was slashed.
  ensure (slashedAny = true) (.noneSlashed candidates.length)
  return state

/-- Whether a signed block carries the signature of its proposer, in the current epoch. -/
def verifyBlockSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBeaconBlock preset fork) :
    Except TransitionError Bool := do
  -- The key of the proposer that the block names, and the domain of proposers at the current epoch.
  let proposer ← liftAccessor (getValidator state signed.message.proposerIndex)
  let domain ← liftAccessor (getDomain config state DOMAIN_BEACON_PROPOSER)
  -- The signature of the block verifies under that key.
  let signingRoot ← liftSsz (computeSigningRoot signed.message domain)
  return checks.verify proposer.pubkey (packBytes signingRoot)
    signed.signature

end EthLib.Consensus
