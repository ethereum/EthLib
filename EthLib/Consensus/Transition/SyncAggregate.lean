module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Transition.Block

/-!
# `Consensus.Transition.SyncAggregate`

From Altair: the signature of the sync committee that a block carries, and its rewards.

The members whose bit is set sign the root of the block at the slot before.

Each member that signed earns a reward, and the proposer earns a share of it.

Each member that did not sign pays the same amount.

The check takes the sum of the keys of the members that signed.

When all signed, that sum is the aggregate key of the committee.

When more than half signed, it is the aggregate key less the keys of those that did not sign.

Otherwise it is the sum of the keys of those that signed.

The three ways give the same sum when the aggregate key is the sum of the member keys.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-- From Altair: the keys whose sum the check of a sync aggregate uses.

A key that does not decode, or a sum of no valid key, is an error. -/
def syncParticipantPubkeys (committee : SyncCommittee preset)
    (bits : Serialization.Ssz.Bitvector preset.SYNC_COMMITTEE_SIZE.toNat) :
    Except TransitionError (Array BLSPubkey) := do
  let signed := bits.bits.toArray.countP id
  let size := preset.SYNC_COMMITTEE_SIZE.toNat
  let pairs := committee.pubkeys.toArray.zip bits.bits.toArray
  -- The rule takes the keys of the members whose bit is set.
  --
  -- The first two ways below give their sum, and the third gives the keys themselves.
  --
  -- All members signed: the aggregate key of the committee.
  if signed = size then
    return #[committee.aggregatePubkey]
  -- More than half signed: the aggregate key less the sum of the keys of the members that did not.
  else if size / 2 < signed then
    let absent := (pairs.filter (!·.2)).map (·.1)
    -- A failed sum names its first bad key by its position among the members that did not sign.
    --
    -- Some member did not sign, so the list is not empty and a bad key is the only failure.
    --
    -- The position comes from the list itself, so the fallback key is never read.
    let absentSum ← (Signatures.ethAggregatePubkeys absent).mapError fun
      | .invalidPubkey (some i) =>
        .invalidSyncCommitteeKey (absent.getD i committee.aggregatePubkey)
      | _ => .invalidSyncCommitteeKey committee.aggregatePubkey
    let total ← (G1.uncompress committee.aggregatePubkey).mapError
      fun _ => .invalidSyncCommitteeKey committee.aggregatePubkey
    -- The sum of the absent keys is no key of the committee, so this error names the aggregate key.
    let absentPoint ← (G1.uncompress absentSum).mapError
      fun _ => .invalidSyncCommitteeKey committee.aggregatePubkey
    return #[Signatures.pointToPubkey (G1.add total (G1.neg absentPoint))]
  -- Otherwise: the keys of the members that signed, in committee order.
  else
    return (pairs.filter (·.2)).map (·.1)

/-- From Altair: the check of the signature of a sync aggregate, as the Ethereum wrapper does it.
-/
def syncAggregateVerify (checks : SignatureChecks) (pubkeys : Array BLSPubkey)
    (message : ByteArray) (signature : BLSSignature) : Bool :=
  -- No key and the signature of the point at infinity pass.
  --
  -- Otherwise the fast aggregate check of the BLS signatures runs.
  (pubkeys.isEmpty && decide (signature = Signatures.G2_POINT_AT_INFINITY)) ||
    checks.fastAggregateVerify pubkeys message signature

/-- From Altair: the reward of each member of the sync committee that signs, for one slot. -/
def syncParticipantReward (state : BeaconState preset fork) : Except TransitionError Gwei := do
  let total ← liftAccessor (getTotalActiveBalance state)
  let perIncrement ← liftAccessor (getBaseRewardPerIncrement preset total)
  liftAccessor (liftArith do
    -- The total base reward `B = r * floor(T / I)`, for the reward per increment `r`.
    let increments ← divChecked total preset.EFFECTIVE_BALANCE_INCREMENT
    let base ← mulChecked perIncrement increments
    -- Then `floor(floor(B * SYNC_REWARD_WEIGHT / WEIGHT_DENOMINATOR) / SLOTS_PER_EPOCH)`.
    let weighted ← mulChecked base SYNC_REWARD_WEIGHT
    let perSlot ← divChecked (← divChecked weighted WEIGHT_DENOMINATOR) preset.SLOTS_PER_EPOCH
    -- Divided among the `SYNC_COMMITTEE_SIZE` members, rounded down.
    divChecked perSlot preset.SYNC_COMMITTEE_SIZE)

/-- From Altair: the share of the proposer for each member that signs. -/
def syncProposerReward (reward : Gwei) : Except TransitionError Gwei :=
  -- `floor(r * PROPOSER_WEIGHT / (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))`, for the reward `r`.
  liftAccessor (liftArith do
    divChecked (← mulChecked reward PROPOSER_WEIGHT) (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))

/-- From Altair: one member's step of the sync rewards, with the proposer of the slot given.

A reward changes only balances, so every step has the proposer of the state before the rewards. -/
def applySyncReward (reward proposerReward : Gwei)
    (proposer : Except AccessorError ValidatorIndex) (state : BeaconState preset fork)
    (member : ValidatorIndex × Bool) : Except TransitionError (BeaconState preset fork) :=
  -- A member that signed earns the reward, then the proposer earns its share.
  if member.2 then do
    let state ← liftAccessor (increaseBalance state member.1 reward)
    let proposer ← liftAccessor proposer
    liftAccessor (increaseBalance state proposer proposerReward)
  -- A member that did not sign pays the reward, but its balance does not go below 0.
  else liftAccessor (decreaseBalance state member.1 reward)

/-- From Altair: the index of the first validator with a key, or an error when none has it.

A key at a position of `2^64` or more has no index, an overflow. -/
def validatorIndexOfPubkey (state : BeaconState preset fork) (pubkey : BLSPubkey) :
    Except TransitionError ValidatorIndex :=
  -- The first position in the registry whose validator has the key.
  match state.validators.data.findIdx? (·.pubkey == pubkey) with
  | some position => liftAccessor (liftArith (ofNatChecked position))
  | none => .error (.unknownSyncCommitteeMember pubkey)

/-- From Altair: the state after the sync aggregate of a block.

The members whose bit is set must sign the root of the block at the slot before the state's.

At slot 0 there is no earlier block root to read, so the step fails.

A member key that no validator holds is an error. -/
def processSyncAggregate (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (aggregate : SyncAggregate preset) : Except TransitionError (BeaconState preset fork) := do
  -- The members of the current sync committee whose bit is set are the participants.
  let committee := (state.currentSyncCommittee altair).value
  let bits := aggregate.syncCommitteeBits
  let pubkeys ← syncParticipantPubkeys committee bits
  -- The slot before, `max(s, 1) - 1` for the slot `s` of the state.
  let previousSlot := saturatingSub state.slot 1
  -- The domain of the sync committee at the epoch of that slot.
  let domain ← liftAccessor (getDomain config state DOMAIN_SYNC_COMMITTEE
    (some (computeEpochAtSlot preset previousSlot)))
  -- The participants sign the root of the block at that slot.
  let root ← liftAccessor (getBlockRootAtSlot state previousSlot)
  let signingRoot ← liftSsz (computeSigningRoot root domain)
  ensure (syncAggregateVerify checks pubkeys (packBytes signingRoot)
    aggregate.syncCommitteeSignature = true)
    (.invalidSyncAggregate previousSlot (bits.bits.toArray.countP id) signingRoot)
  -- The reward of a participant, and the share of the proposer for each.
  let reward ← syncParticipantReward state
  let proposerReward ← syncProposerReward reward
  -- The validator index of each member: the first validator with its key.
  let members ← committee.pubkeys.toArray.mapM (validatorIndexOfPubkey state)
  -- The proposer is read once: the rewards change only balances, which it does not read.
  let proposer := getBeaconProposerIndex state
  -- Each member in committee order earns or pays its reward.
  (members.zip bits.bits.toArray).foldlM (applySyncReward reward proposerReward proposer) state

end EthLib.Consensus
