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

[EIP-7892]: https://eips.ethereum.org/EIPS/eip-7892#enr
-/

@[expose] public section

namespace EthLib.Consensus

open Base
open Serialization.Ssz
open Networking.Enr

namespace Config

/-- The first epoch after an epoch at which the fork digest can change, if a fork is planned. -/
def nextDigestEpoch (config : Config) (epoch : Epoch) : Option Epoch :=
  -- The least epoch above the epoch `e` at which the digest can change.
  --
  -- A fork left at `FAR_FUTURE_EPOCH` is not planned, so it gives none.
  (config.digestEpochs.find? (epoch < ·)).filter (· ≠ FAR_FUTURE_EPOCH)

end Config

/-- The `eth2` value that a node writes at an epoch of its wall clock.

At a BPO epoch the version does not change, so the next version can equal the current one. -/
def enrForkId (config : Config) (genesisValidatorsRoot : Root) (epoch : Epoch) :
    Except Err EnrForkId := do
  -- The fork digest of the epoch `e`, under the root of the genesis validators.
  let digest ← computeForkDigest config genesisValidatorsRoot epoch
  match config.nextDigestEpoch epoch with
  -- With a next fork at epoch `f`, the next version is the fork version at `f`, and the epoch `f`.
  | some next => return ⟨digest, config.computeForkVersion next, next⟩
  -- With none, the next version is the fork version at `e`, and the epoch `FAR_FUTURE_EPOCH`.
  | none => return ⟨digest, config.computeForkVersion epoch, FAR_FUTURE_EPOCH⟩

/-- The `nfd` value that a node writes at an epoch: the digest of the next fork. -/
def nextForkDigest (config : Config) (genesisValidatorsRoot : Root) (epoch : Epoch) :
    Except Err ForkDigest :=
  match config.nextDigestEpoch epoch with
  -- With a next fork at epoch `f`, the fork digest of `f`.
  | some next => computeForkDigest config genesisValidatorsRoot next
  -- With none, four zero bytes, the default value of a fork digest.
  | none => return Vector.replicate 4 0

/-- The `eth2` value of a bootnode record made before genesis, when the root is not known yet. -/
def bootnodeForkId (config : Config) : Except Err EnrForkId := do
  -- The fork digest of `GENESIS_EPOCH`, under a root of 32 zero bytes.
  let digest ← computeForkDigest config (Vector.replicate 32 0) GENESIS_EPOCH
  -- No fork is planned: the next version is `GENESIS_FORK_VERSION`, at `FAR_FUTURE_EPOCH`.
  return ⟨digest, config.GENESIS_FORK_VERSION, FAR_FUTURE_EPOCH⟩

/-- Whether a node writes the Fulu entries `cgc` and `nfd` at an epoch.

A node must write them once Fulu has an epoch.

A node from Fulu on writes them too, a rule of EthLib so that its reader accepts the record.

That case differs only at the far future epoch, or when a fork after Fulu is planned but not Fulu.
-/
def writesFuluEntries (config : Config) (epoch : Epoch) : Bool :=
  -- `FULU_FORK_EPOCH` is not `FAR_FUTURE_EPOCH`, or the fork at the epoch is from Fulu.
  config.FULU_FORK_EPOCH ≠ FAR_FUTURE_EPOCH || .fusaka ≤ config.forkAtEpoch epoch

/-- The consensus entries of a node at an epoch, as pairs in key order for a new record.

The node gives its attestation subnets, its sync committee subnets and its custody group count.

The subnets are written even when no bit is set, which the sources allow. -/
def consensusPairs {count : UInt64} (config : Config) (genesisValidatorsRoot : Root)
    (epoch : Epoch) (attnets : Attnets count) (syncnets : Syncnets) (cgc : UInt64) :
    Except Err (List (ByteArray × Serialization.Rlp.Item)) := do
  -- The fork `F` at the epoch `e`.
  let fork := config.forkAtEpoch epoch
  let key (k : ConsensusKey) := k.name.toUTF8
  -- The `eth2` value is the SSZ encoding of the fork ID at `e`.
  let eth2 ← SszType.serialize (← enrForkId config genesisValidatorsRoot epoch)
  -- The subnets are their SSZ encodings, as bit vectors.
  let attnets ← SszType.serialize attnets
  let syncnets ← SszType.serialize syncnets
  -- A fork digest is four bytes, which are its SSZ encoding.
  let nfd := (← nextForkDigest config genesisValidatorsRoot epoch).toArray
  let fulu := writesFuluEntries config epoch
  -- The pairs are sorted by key, as EIP-778 specifies.
  --
  -- The order is `attnets`, `cgc`, `eth2`, `nfd`, `syncnets`.
  --
  -- `cgc` and `nfd` come only when the node writes the Fulu entries, and `syncnets` from Altair.
  return [(key .attnets, .bytes attnets)] ++
    (if fulu then [(key .cgc, Serialization.Rlp.Codec.toItem cgc)] else []) ++
    [(key .eth2, .bytes eth2)] ++
    (if fulu then [(key .nfd, .bytes ⟨nfd⟩)] else []) ++
    (if .altair ≤ fork then [(key .syncnets, .bytes syncnets)] else [])

/-- Whether a node may disconnect from a peer for their fork entries, at an epoch.

A node weighs the `nfd` of a peer together with the next fork of its `eth2`.

On a mismatch, the node must not disconnect before the fork boundary, and it may from then on.

Each `nfd` is none for a peer that does not write it. -/
def mayDisconnect (localId remoteId : EnrForkId) (localNfd remoteNfd : Option ForkDigest)
    (epoch : Epoch) : Bool :=
  -- A different fork digest now means another fork or another chain, so the node may disconnect.
  if localId.forkDigest ≠ remoteId.forkDigest then true
  -- The same fork ID and the same `nfd`: both agree on the next fork, so the node keeps the peer.
  else if localId = remoteId ∧ localNfd = remoteNfd then false
  -- Otherwise the next forks differ, and the two part only from the earlier next fork epoch.
  else min localId.nextForkEpoch remoteId.nextForkEpoch ≤ epoch

end EthLib.Consensus
