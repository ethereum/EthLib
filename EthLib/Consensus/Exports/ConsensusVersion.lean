module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Consensus.ConsensusVersion

/-!
# `Exports.ConsensusVersion`

C-ABI exports for the consensus version of a fork, as the Beacon and Builder APIs name it.

A caller names a fork as its case is written, such as `dencun`.

An unknown fork name, or an unknown version name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base
open EthLib.Exports (Result PyValue pyExport forkOfName)

/-- The name of the consensus version of a fork, if it has one. -/
def consensusVersionOf (fork : String) : Result (Option String) := do
  return (← forkOfName fork.toUTF8).consensusVersion?.map (·.name)

/-- The name of the consensus version of a fork, or none before Phase 0 and at Hegotá. -/
@[export eth_consensus_consensus_version]
def consensusVersionExport (args : PyValue) : Result PyValue :=
  pyExport consensusVersionOf args

/-- The first fork of a consensus version, read from its exact name. -/
def consensusVersionForkOf (name : String) : Result String := do
  let some version := ConsensusVersion.ofName? name | throw (0, s!"no consensus version {name}")
  return version.fork.name

/-- The name of the first fork of a consensus version, read from its exact name. -/
@[export eth_consensus_consensus_version_fork]
def consensusVersionForkExport (args : PyValue) : Result PyValue :=
  pyExport consensusVersionForkOf args

end EthLib.Consensus.Exports
