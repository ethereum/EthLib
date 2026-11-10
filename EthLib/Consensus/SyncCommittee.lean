module

public import EthLib.Consensus.PayloadTimeliness

/-!
# `Consensus.SyncCommittee`

From Altair: the selection of the sync committee of the next period.

The committee is a balance-weighted selection from the validators active in the next epoch.

Its candidates are read in shuffled order, with the seed of the next epoch for sync committees.

A candidate may be drawn more than once, so the committee may hold a validator twice.

The draw is that of a proposer at the fork of the state, so it reads two random bytes from Electra.

From Electra the draw stays weighted by the effective balance, as [EIP-7251] notes.

The committee keeps the public keys of its members, and their aggregate.

The draw counter is a 64-bit integer, so the selection fails when it would reach `2^64`.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#sync-committee-selection-probability
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork}

/-- From Altair: the indices of the sync committee of the next period, with possible repeats. -/
def getNextSyncCommitteeIndices (state : BeaconState preset fork) :
    Except AccessorError (Vector ValidatorIndex preset.SYNC_COMMITTEE_SIZE.toNat) := do
  let epoch ← liftArith (addChecked (getCurrentEpoch state) 1)
  let seed ← getSeed state epoch DOMAIN_SYNC_COMMITTEE
  computeBalanceWeightedSelection state
    (← getActiveValidatorIndicesChecked state epoch).toArray seed preset.SYNC_COMMITTEE_SIZE true

/-- The aggregate of some public keys, as the public key of 48 bytes that it encodes.

Each key must be valid, and there must be at least one. -/
def aggregatePubkeys (pubkeys : Array BLSPubkey) : Except AccessorError BLSPubkey := do
  let aggregate ← (Cryptography.Bls.Signatures.ethAggregatePubkeys
    (pubkeys.map packBytes)).mapError fun _ => .invalidPubkeys
  -- The aggregate is a compressed point, so it always has 48 bytes.
  if size : aggregate.data.size = 48 then return ⟨aggregate.data, size⟩
  else throw .invalidPubkeys

/-- From Altair: the sync committee of the next period, with possible repeats.

It holds the public keys of its members in committee order, and their aggregate. -/
def getNextSyncCommittee (state : BeaconState preset fork) :
    Except AccessorError (SyncCommittee preset) := do
  let indices ← getNextSyncCommitteeIndices state
  let pubkeys ← indices.mapM fun index => return (← getValidator state index).pubkey
  return ⟨pubkeys, ← aggregatePubkeys pubkeys.toArray⟩

end EthLib.Consensus
