module

public import EthLib.Consensus.ForkDigest
public import EthLib.Networking.Enr.Consensus

/-!
# `Consensus.Enr`

The consensus entries that a node writes into its node record, and how it compares a peer's.

The `eth2` entry holds the fork digest now, then the version and the epoch of the next fork.

From Fulu, the next fork is the next epoch at which the digest can change.

That counts a new blob schedule entry, a fork that [EIP-7892] calls blob-parameter-only (BPO).

The `nfd` entry holds the digest of that next fork, or four zero bytes when none is planned.

A node reads the epoch from its wall clock, not from the chain it has synced.

Provenance: the `eth2` field of the [phase0 networking text], and its [Fulu networking text].

[EIP-7892]: https://eips.ethereum.org/EIPS/eip-7892#enr
[phase0 networking text]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/phase0/p2p-interface.md#L1749-L1802
[Fulu networking text]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/fulu/p2p-interface.md#L865-L954
-/

@[expose] public section

namespace EthLib.Consensus

open Base
open Serialization.Ssz
open Networking.Enr

namespace Config

/-- The first epoch after an epoch at which the fork digest can change, if a fork is planned.

A fork left at the far future epoch is not planned. -/
def nextDigestEpoch (config : Config) (epoch : Epoch) : Option Epoch :=
  (config.digestEpochs.find? (epoch < ·)).filter (· ≠ FAR_FUTURE_EPOCH)

end Config

/-- The `eth2` value that a node writes at an epoch of its wall clock.

With no fork planned, the next version is the current one and the next epoch is the far future.

At a BPO epoch the version does not change, so the next version can equal the current one. -/
def enrForkId (config : Config) (genesisValidatorsRoot : Root) (epoch : Epoch) :
    Except Err EnrForkId := do
  let digest ← computeForkDigest config genesisValidatorsRoot epoch
  match config.nextDigestEpoch epoch with
  | some next => return ⟨digest, config.computeForkVersion next, next⟩
  | none => return ⟨digest, config.computeForkVersion epoch, FAR_FUTURE_EPOCH⟩

/-- The `nfd` value that a node writes at an epoch: the digest of the next fork.

With no fork planned, it is four zero bytes, the default value of a fork digest. -/
def nextForkDigest (config : Config) (genesisValidatorsRoot : Root) (epoch : Epoch) :
    Except Err ForkDigest :=
  match config.nextDigestEpoch epoch with
  | some next => computeForkDigest config genesisValidatorsRoot next
  | none => return Vector.replicate 4 0

/-- The `eth2` value of a bootnode record made before genesis, when the root is not known yet.

It takes the digest of the genesis epoch with a zero root, and plans no fork. -/
def bootnodeForkId (config : Config) : Except Err EnrForkId := do
  let digest ← computeForkDigest config (Vector.replicate 32 0) GENESIS_EPOCH
  return ⟨digest, config.GENESIS_FORK_VERSION, FAR_FUTURE_EPOCH⟩

/-- Whether a node writes the Fulu entries `cgc` and `nfd` at an epoch.

The Fulu networking text says that they "MUST be added once" Fulu has an epoch.

A node from Fulu on writes them too, a rule of EthLib so that its reader accepts the record.

That case differs only at the far future epoch, or when a fork after Fulu is planned but not Fulu.
-/
def writesFuluEntries (config : Config) (epoch : Epoch) : Bool :=
  config.FULU_FORK_EPOCH ≠ FAR_FUTURE_EPOCH || .fusaka ≤ config.forkAtEpoch epoch

/-- The consensus entries of a node at an epoch, as pairs in key order for a new record.

The node gives its attestation subnets, its sync committee subnets and its custody group count.

The subnets are written even when no bit is set, which the sources allow.

The sync committee subnets are written from Altair. -/
def consensusPairs {count : UInt64} (config : Config) (genesisValidatorsRoot : Root)
    (epoch : Epoch) (attnets : Attnets count) (syncnets : Syncnets) (cgc : UInt64) :
    Except Err (List (ByteArray × Serialization.Rlp.Item)) := do
  let fork := config.forkAtEpoch epoch
  let key (k : ConsensusKey) := k.name.toUTF8
  let eth2 ← SszType.serialize (← enrForkId config genesisValidatorsRoot epoch)
  let attnets ← SszType.serialize attnets
  let syncnets ← SszType.serialize syncnets
  -- A fork digest is four bytes, which are its SSZ encoding.
  let nfd := (← nextForkDigest config genesisValidatorsRoot epoch).toArray
  let fulu := writesFuluEntries config epoch
  return [(key .attnets, .bytes attnets)] ++
    (if fulu then [(key .cgc, Serialization.Rlp.Codec.toItem cgc)] else []) ++
    [(key .eth2, .bytes eth2)] ++
    (if fulu then [(key .nfd, .bytes ⟨nfd⟩)] else []) ++
    (if .altair ≤ fork then [(key .syncnets, .bytes syncnets)] else [])

/-- Whether a node may disconnect from a peer for their fork entries, at an epoch.

A different fork digest now means another fork or another chain, so the node may disconnect.

With the same digest, a different next fork stops the two only from the earlier next fork epoch.

The Fulu networking text has a node weigh `nfd` with the next fork of `eth2`.

On a mismatch, the node "MUST NOT disconnect before the fork boundary", and it may from then on.

Each `nfd` is none for a peer that does not write it. -/
def mayDisconnect (localId remoteId : EnrForkId) (localNfd remoteNfd : Option ForkDigest)
    (epoch : Epoch) : Bool :=
  if localId.forkDigest ≠ remoteId.forkDigest then true
  else if localId = remoteId ∧ localNfd = remoteNfd then false
  else min localId.nextForkEpoch remoteId.nextForkEpoch ≤ epoch

end EthLib.Consensus
