module

public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.ForkDigest

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
open EthLib.Exports (Result PyValue pyExport)

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

end EthLib.Consensus.Exports
