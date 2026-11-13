module

public import EthLib.Base.Fork
public import EthLib.Consensus.Config

/-!
# `Consensus.ConsensusVersion`

The Beacon API and the Builder API name the fork of the data that a response carries.

They write it as a consensus version, one lowercase name per fork of the consensus layer.

The consensus version of a fork is that of the latest consensus fork at or before it.

So a fork of only the execution layer or the blob schedule keeps the version before it.

The [`ConsensusVersion` schema] of the Beacon API lists the names up to Gloas.

The Builder API takes the names from Bellatrix on, since it starts at the Merge.

[`ConsensusVersion` schema]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/beacon-node-oapi.yaml#L378-L381
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- A fork of the consensus layer, as the Beacon API names it.

The cases follow the order of the [`ConsensusVersion` schema].

[`ConsensusVersion` schema]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/beacon-node-oapi.yaml#L378-L381
-/
inductive ConsensusVersion where
  /-- Phase 0, the launch of the beacon chain. -/
  | phase0
  /-- Altair. -/
  | altair
  /-- Bellatrix. -/
  | bellatrix
  /-- Capella, the consensus half of Shapella. -/
  | capella
  /-- Deneb, the consensus half of Dencun. -/
  | deneb
  /-- Electra, the consensus half of Pectra. -/
  | electra
  /-- Fulu, the consensus half of Fusaka. -/
  | fulu
  /-- Gloas, the consensus half of Glamsterdam. -/
  | gloas
  deriving DecidableEq, Repr

namespace ConsensusVersion

/-- A version is before another when it comes earlier in the list. -/
instance : LT ConsensusVersion := ⟨fun a b => a.ctorIdx < b.ctorIdx⟩

/-- A version is at or before another when it comes no later in the list. -/
instance : LE ConsensusVersion := ⟨fun a b => a.ctorIdx ≤ b.ctorIdx⟩

instance (a b : ConsensusVersion) : Decidable (a < b) := Nat.decLt _ _

instance (a b : ConsensusVersion) : Decidable (a ≤ b) := Nat.decLe _ _

/-- Every version, in order. -/
def all : List ConsensusVersion :=
  [phase0, altair, bellatrix, capella, deneb, electra, fulu, gloas]

/-- The name of a version, exactly as the schema writes it. -/
def name : ConsensusVersion → String
  | phase0 => "phase0"
  | altair => "altair"
  | bellatrix => "bellatrix"
  | capella => "capella"
  | deneb => "deneb"
  | electra => "electra"
  | fulu => "fulu"
  | gloas => "gloas"

/-- The version with a name, if one has it.

The schema fixes each name exactly, so no other spelling names a version, not even in uppercase. -/
def ofName? (s : String) : Option ConsensusVersion :=
  all.find? (·.name == s)

/-- The first fork of the timeline that has this version. -/
def fork : ConsensusVersion → Fork
  | phase0 => .phase0
  | altair => .altair
  | bellatrix => .bellatrix
  | capella => .shapella
  | deneb => .dencun
  | electra => .pectra
  | fulu => .fusaka
  | gloas => .glamsterdam

/-- The fork version that a configuration gives to a version. -/
def forkVersion (config : Config) : ConsensusVersion → Version
  | phase0 => config.GENESIS_FORK_VERSION
  | altair => config.ALTAIR_FORK_VERSION
  | bellatrix => config.BELLATRIX_FORK_VERSION
  | capella => config.CAPELLA_FORK_VERSION
  | deneb => config.DENEB_FORK_VERSION
  | electra => config.ELECTRA_FORK_VERSION
  | fulu => config.FULU_FORK_VERSION
  | gloas => config.GLOAS_FORK_VERSION

end ConsensusVersion

end EthLib.Consensus

namespace EthLib.Base.Fork

open EthLib.Consensus (ConsensusVersion)

/-- The consensus version of a fork: that of the latest consensus fork at or before it.

A fork of the blob schedule, BPO1 to BPO5, has the version of Fulu.

Before Phase 0 the beacon chain does not exist, so no fork there has a version.

The schema names no version for Heze yet, so Hegotá has none. -/
def consensusVersion? (fork : Fork) : Option ConsensusVersion :=
  if .hegota ≤ fork then none
  else if .glamsterdam ≤ fork then some .gloas
  else if .fusaka ≤ fork then some .fulu
  else if .pectra ≤ fork then some .electra
  else if .dencun ≤ fork then some .deneb
  else if .shapella ≤ fork then some .capella
  else if .bellatrix ≤ fork then some .bellatrix
  else if .altair ≤ fork then some .altair
  else if .phase0 ≤ fork then some .phase0
  else none

end EthLib.Base.Fork
