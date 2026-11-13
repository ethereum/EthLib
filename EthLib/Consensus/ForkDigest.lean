module

public import EthLib.Consensus.Signing

/-!
# `Consensus.ForkDigest`

Peers name the fork of a message with a fork digest of four bytes.

From Altair, a protocol that sends context bytes puts a digest in each successful chunk.

It is the digest of the epoch of the chunk's payload, and it selects the SSZ type of that payload.

Each gossip topic carries a digest too.

So a receiver must read a fork from a digest.

The digest changes only at a few epochs.

These are epoch 0 and the first epoch of each consensus fork.

From Fulu, they also include the first epoch of each blob schedule entry.

Between two such epochs, the digest and the fork stay the same.

So the receiver searches these epochs for one with the digest, and takes the fork at it.

A digest is four bytes of a hash, and from Fulu one fork can have several digests.

A configuration can also give two forks one digest, for instance with one version for both.

So the search is proved to read the right fork on a chain that passes a finite check.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

namespace Config

/-- The epochs at which the fork digest can change, in increasing order and without repeats.

They are epoch 0 and the first epoch of each consensus fork from Altair to Heze.

They also hold the first epoch of each blob schedule entry at or after the first epoch of Fulu.

[EIP-7892] mixes the blob parameters into the digest from Fulu, so an entry can change it.

[EIP-7892]: https://eips.ethereum.org/EIPS/eip-7892#modified-compute_fork_digest
-/
def digestEpochs (config : Config) : List Epoch :=
  let forks := [config.ALTAIR_FORK_EPOCH, config.BELLATRIX_FORK_EPOCH, config.CAPELLA_FORK_EPOCH,
    config.DENEB_FORK_EPOCH, config.ELECTRA_FORK_EPOCH, config.FULU_FORK_EPOCH,
    config.GLOAS_FORK_EPOCH, config.HEZE_FORK_EPOCH]
  let blobs := (config.BLOB_SCHEDULE.map (·.EPOCH)).filter (config.FULU_FORK_EPOCH ≤ ·)
  ((0 :: forks ++ blobs).mergeSort (· ≤ ·)).eraseDups

/-- Among the epochs at which the fork digest can change, the latest at or before an epoch.

Epoch 0 is one of them, so it always exists. -/
def digestStart (config : Config) (epoch : Epoch) : Epoch :=
  config.digestEpochs.foldl (fun start next => if next ≤ epoch then max start next else start) 0

end Config

/-- The first epoch with the given digest, among those at which the fork digest can change.

The search takes these epochs in increasing order, and finds none when no digest matches.

The receiver decodes a message with the types of the fork at that epoch. -/
def forkOfDigest (config : Config) (genesisValidatorsRoot : Root) (digest : ForkDigest) :
    Option Epoch :=
  config.digestEpochs.find? fun start =>
    match computeForkDigest config genesisValidatorsRoot start with
    | .ok found => found == digest
    | .error _ => false

/-- Whether the search reads the right fork back from the digest of each epoch of the list.

The list holds the epochs at which the fork digest can change.

The list has at most nine epochs, plus one for each entry of the blob schedule.

The check is weaker than asking that these digests all differ.

It also reads the epoch of a fork left at the far future, which no message carries.

So it can fail when that fork's digest equals an earlier one, though it then asks more than needed.

Two epochs of one fork may share a digest, since the search still reads that fork. -/
def digestsIdentify (config : Config) (genesisValidatorsRoot : Root) : Bool :=
  config.digestEpochs.all fun start =>
    match computeForkDigest config genesisValidatorsRoot start with
    | .ok digest =>
      (forkOfDigest config genesisValidatorsRoot digest).map config.forkAtEpoch ==
        some (config.forkAtEpoch start)
    | .error _ => false

end EthLib.Consensus
