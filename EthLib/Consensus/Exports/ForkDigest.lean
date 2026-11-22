module

public import EthLib.Consensus.Enr
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.ForkDigest
public import EthLib.Networking.Exports.Enr
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.ForkDigest`

C-ABI exports for the fork that a fork digest names.

A caller names a configuration, with the replacements that a `dict` gives.

The exports take the tuple of their arguments as typed Python values.

An unknown configuration name, or a replacement that does not read, has code 0.

A root that is not 32 bytes, or a digest that is not 4 bytes, has code 0 too.
-/

public section

namespace EthLib.Consensus.Exports

open Base
open EthLib.Exports (Result PyValue UnreadArgument pyExport toResult)
open Serialization.Ssz (SszType)
open Networking.Enr

/-- The epochs at which the fork digest can change, in increasing order and without repeats. -/
def digestEpochsOf (args : String × Option PyValue) : Result (List UInt64) := do
  let (name, replacements) := args
  return (← configWithValue name replacements).digestEpochs

/-- The epochs at which the fork digest can change, in increasing order and without repeats.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_digest_epochs]
def digestEpochsExport (args : PyValue) : Result PyValue := pyExport digestEpochsOf args

/-- The first epoch with the given digest, among those at which it can change, with its fork. -/
def forkOfDigestOf (args : String × Option PyValue × Root × ForkDigest) :
    Result (Option (UInt64 × String)) := do
  let (name, replacements, genesisValidatorsRoot, digest) := args
  let config ← configWithValue name replacements
  return (forkOfDigest config genesisValidatorsRoot digest).map fun start =>
    (start, (config.forkAtEpoch start).name)

/-- The first epoch with the given digest, among those at which it can change, with its fork.

`None` when no such epoch has the digest.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_fork_of_digest]
def forkOfDigestExport (args : PyValue) : Result PyValue := pyExport forkOfDigestOf args

/-- Whether the digest of each epoch at which it can change reads back the fork at that epoch. -/
def digestsIdentifyOf (args : String × Option PyValue × Root) : Result Bool := do
  let (name, replacements, genesisValidatorsRoot) := args
  return digestsIdentify (← configWithValue name replacements) genesisValidatorsRoot

/-- Whether the digest of each epoch at which it can change reads back the fork at that epoch.

The first such epoch with a digest then has the fork of every epoch with that digest.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_digests_identify]
def digestsIdentifyExport (args : PyValue) : Result PyValue := pyExport digestsIdentifyOf args

/-- The `eth2` value that a node writes at an epoch, as its digest, next version and next epoch. -/
def enrForkIdOf (args : String × Option PyValue × Root × UInt64) :
    Result (ForkDigest × Version × UInt64) := do
  let (name, replacements, genesisValidatorsRoot, epoch) := args
  let config ← configWithValue name replacements
  let e ← toResult "root rejected" (enrForkId config genesisValidatorsRoot epoch)
  return (e.forkDigest, e.nextForkVersion, e.nextForkEpoch)

/-- The `eth2` value that a node writes at an epoch, as its digest, next version and next epoch.

From Fulu, the next fork is the next epoch at which the digest can change, BPO epochs included.

With no fork planned, the next version is the current one and the next epoch is `2^64 - 1`.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_enr_fork_id]
def enrForkIdExport (args : PyValue) : Result PyValue := pyExport enrForkIdOf args

/-- The `nfd` value that a node writes at an epoch: the digest of the next fork. -/
def nextForkDigestOf (args : String × Option PyValue × Root × UInt64) : Result ForkDigest := do
  let (name, replacements, genesisValidatorsRoot, epoch) := args
  let config ← configWithValue name replacements
  toResult "root rejected" (nextForkDigest config genesisValidatorsRoot epoch)

/-- The `nfd` value that a node writes at an epoch: the digest of the next fork.

With no fork planned, it is four zero bytes.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_next_fork_digest]
def nextForkDigestExport (args : PyValue) : Result PyValue := pyExport nextForkDigestOf args

/-- The `eth2` value of a bootnode record made before genesis, as its three fields. -/
def bootnodeForkIdOf (args : String × Option PyValue) : Result (ForkDigest × Version × UInt64) := do
  let (name, replacements) := args
  let e ← toResult "configuration rejected" (bootnodeForkId (← configWithValue name replacements))
  return (e.forkDigest, e.nextForkVersion, e.nextForkEpoch)

/-- The `eth2` value of a bootnode record made before genesis, as its three fields.

It is the digest of the genesis epoch with a zero root, then the genesis version, and no fork.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_bootnode_fork_id]
def bootnodeForkIdExport (args : PyValue) : Result PyValue := pyExport bootnodeForkIdOf args

/-- A signed "v4" record of a consensus node at an epoch, with its consensus entries.

The subnets come as the SSZ bytes of their bitvectors.

A private key or a record that is rejected comes back with code 0.

So does a record with no RLP encoding. -/
def consensusRecordOf (args : String × Option PyValue × Root × UInt64 × ByteArray × UInt64 ×
    ByteArray × ByteArray × UInt64) : Result ByteArray := do
  let (name, replacements, genesisValidatorsRoot, epoch, secretKey, seq, attnets, syncnets,
    cgc) := args
  let config ← configWithValue name replacements
  let sk ← Networking.Enr.Exports.privateKeyOf secretKey
  let attnets ← toResult "attnets rejected"
    (SszType.deserialize (Attnets config.ATTESTATION_SUBNET_COUNT) attnets)
  let syncnets ← toResult "syncnets rejected" (SszType.deserialize Syncnets syncnets)
  let pairs ← toResult "root rejected"
    (consensusPairs config genesisValidatorsRoot epoch attnets syncnets cgc)
  -- A record error has no code among those of SSZ, so it comes back with code 0.
  let r ← toResult none ((makeRecordV4 sk seq pairs).mapError fun e =>
    UnreadArgument.mk s!"record rejected: {Networking.Enr.Exports.message e}")
  Networking.Enr.Exports.encodeRecord (fun _ => 0) r

/-- A signed "v4" record of a consensus node at an epoch, with its consensus entries.

The arguments are the configuration, the root, the epoch, the private key and the sequence number.

Then come the attestation and sync committee subnets, as SSZ bytes, and the custody group count.

The record holds `eth2`, `attnets`, `syncnets` from Altair, and `cgc` and `nfd` once Fulu is set.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_enr_record]
def consensusRecordExport (args : PyValue) : Result PyValue := pyExport consensusRecordOf args

end EthLib.Consensus.Exports
