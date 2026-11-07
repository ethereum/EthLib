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

All members signed: the aggregate key of the committee.

More than half signed: the aggregate key less the sum of the keys of the members that did not.

Otherwise: the keys of the members that signed, in committee order.

A key that does not decode, or a sum of no valid key, is an error. -/
def syncParticipantPubkeys (committee : SyncCommittee preset)
    (bits : Serialization.Ssz.Bitvector preset.SYNC_COMMITTEE_SIZE.toNat) :
    Except TransitionError (Array ByteArray) := do
  let signed := bits.bits.toArray.countP id
  let size := preset.SYNC_COMMITTEE_SIZE.toNat
  let pairs := committee.pubkeys.toArray.zip bits.bits.toArray
  if signed = size then
    return #[packBytes committee.aggregatePubkey]
  else if size / 2 < signed then
    let absent := (pairs.filter (!·.2)).map (packBytes ·.1)
    let absentSum ← (Signatures.ethAggregatePubkeys absent).mapError
      fun _ => .invalidSyncCommitteeKey
    let total ← (G1.uncompress (packBytes committee.aggregatePubkey)).mapError
      fun _ => .invalidSyncCommitteeKey
    let absentPoint ← (G1.uncompress absentSum).mapError fun _ => .invalidSyncCommitteeKey
    return #[G1.compress (G1.add total (G1.neg absentPoint))]
  else
    return (pairs.filter (·.2)).map (packBytes ·.1)

/-- From Altair: the check of the signature of a sync aggregate, as the Ethereum wrapper does it.

No key and the signature of the point at infinity pass; otherwise the fast aggregate check runs. -/
def syncAggregateVerify (checks : SignatureChecks) (pubkeys : Array ByteArray)
    (message signature : ByteArray) : Bool :=
  (pubkeys.isEmpty && decide (signature = Signatures.G2_POINT_AT_INFINITY)) ||
    checks.fastAggregateVerify pubkeys message signature

/-- From Altair: the reward of each member of the sync committee that signs, for one slot.

It is a share of the base rewards of all active balance, per slot and per member. -/
def syncParticipantReward (state : BeaconState preset fork) : Except TransitionError Gwei := do
  let total ← liftAccessor (getTotalActiveBalance state)
  let perIncrement ← liftAccessor (getBaseRewardPerIncrement preset total)
  liftAccessor (liftArith do
    let increments ← divChecked total preset.EFFECTIVE_BALANCE_INCREMENT
    let base ← mulChecked perIncrement increments
    let weighted ← mulChecked base SYNC_REWARD_WEIGHT
    let perSlot ← divChecked (← divChecked weighted WEIGHT_DENOMINATOR) preset.SLOTS_PER_EPOCH
    divChecked perSlot preset.SYNC_COMMITTEE_SIZE)

/-- From Altair: one member's step of the sync rewards.

A member that signed earns the reward, and the proposer earns its share.

A member that did not sign pays the reward. -/
def applySyncReward (reward proposerReward : Gwei) (state : BeaconState preset fork)
    (member : ValidatorIndex × Bool) : Except TransitionError (BeaconState preset fork) :=
  if member.2 then do
    let state ← liftAccessor (increaseBalance state member.1 reward)
    let proposer ← liftAccessor (getBeaconProposerIndex state)
    liftAccessor (increaseBalance state proposer proposerReward)
  else liftAccessor (decreaseBalance state member.1 reward)

/-- From Altair: the index of the first validator with a key, or an error when none has it. -/
def validatorIndexOfPubkey (state : BeaconState preset fork) (pubkey : BLSPubkey) :
    Except TransitionError ValidatorIndex :=
  match state.validators.data.findIdx? (·.pubkey == pubkey) with
  | some index => .ok index.toUInt64
  | none => .error .unknownSyncCommitteeMember

/-- From Altair: the state after the sync aggregate of a block.

The members whose bit is set must sign the root of the block at the slot before the state's.

At slot 0 there is no earlier block root to read, so the step fails.

The signature is under the sync committee domain, at the epoch of that slot.

Each member that signed earns its reward, and the proposer its share, in committee order.

Each member that did not sign pays its reward.

A member key that no validator holds is an error. -/
def processSyncAggregate (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (aggregate : SyncAggregate preset) : Except TransitionError (BeaconState preset fork) := do
  let committee := (state.currentSyncCommittee altair).value
  let bits := aggregate.syncCommitteeBits
  let pubkeys ← syncParticipantPubkeys committee bits
  let previousSlot := saturatingSub state.slot 1
  let domain ← liftAccessor (getDomain config state DOMAIN_SYNC_COMMITTEE
    (some (computeEpochAtSlot preset previousSlot)))
  let root ← liftAccessor (getBlockRootAtSlot state previousSlot)
  let signingRoot ← liftSsz (computeSigningRoot root domain)
  ensure (syncAggregateVerify checks pubkeys (packBytes signingRoot)
    (packBytes aggregate.syncCommitteeSignature) = true) .invalidSyncAggregate
  let reward ← syncParticipantReward state
  let proposerReward ← liftAccessor (liftArith do
    divChecked (← mulChecked reward PROPOSER_WEIGHT) (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
  let members ← committee.pubkeys.toArray.mapM (validatorIndexOfPubkey state)
  (members.zip bits.bits.toArray).foldlM (applySyncReward reward proposerReward) state

end EthLib.Consensus
