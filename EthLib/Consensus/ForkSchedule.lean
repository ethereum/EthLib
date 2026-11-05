module

public import EthLib.Base.Fork
public import EthLib.Consensus.Config

/-!
# `Consensus.ForkSchedule`

A configuration gives the first epoch and the version of each fork of the consensus layer.

The fork at an epoch is the latest of these forks whose first epoch is at or before it.

From Fulu on, the blob schedule raises the most blobs in a block at given epochs.

Such a change is not a fork of the consensus layer.

So the fork at an epoch is never one of BPO1 to BPO5.

From Gloas on, a gas limit schedule recommends a gas limit at given epochs, without a validity rule.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

namespace Config

/-- The fork of the consensus layer at an epoch.

It is the latest consensus fork whose first epoch is at or before the epoch. -/
def forkAtEpoch (config : Config) (epoch : Epoch) : Fork :=
  if config.HEZE_FORK_EPOCH ≤ epoch then .hegota
  else if config.GLOAS_FORK_EPOCH ≤ epoch then .glamsterdam
  else if config.FULU_FORK_EPOCH ≤ epoch then .fusaka
  else if config.ELECTRA_FORK_EPOCH ≤ epoch then .pectra
  else if config.DENEB_FORK_EPOCH ≤ epoch then .dencun
  else if config.CAPELLA_FORK_EPOCH ≤ epoch then .shapella
  else if config.BELLATRIX_FORK_EPOCH ≤ epoch then .bellatrix
  else if config.ALTAIR_FORK_EPOCH ≤ epoch then .altair
  else .phase0

/-- The version of a fork: that of the latest consensus fork at or before it.

A fork that changes only the execution layer, or only the blob schedule, keeps that version.

The configuration lists the forks up to Heze, the last fork on the timeline. -/
def forkVersion (config : Config) (fork : Fork) : Version :=
  if .hegota ≤ fork then config.HEZE_FORK_VERSION
  else if .glamsterdam ≤ fork then config.GLOAS_FORK_VERSION
  else if .fusaka ≤ fork then config.FULU_FORK_VERSION
  else if .pectra ≤ fork then config.ELECTRA_FORK_VERSION
  else if .dencun ≤ fork then config.DENEB_FORK_VERSION
  else if .shapella ≤ fork then config.CAPELLA_FORK_VERSION
  else if .bellatrix ≤ fork then config.BELLATRIX_FORK_VERSION
  else if .altair ≤ fork then config.ALTAIR_FORK_VERSION
  else config.GENESIS_FORK_VERSION

/-- The version of the fork at an epoch. -/
def computeForkVersion (config : Config) (epoch : Epoch) : Version :=
  config.forkVersion (config.forkAtEpoch epoch)

end Config

/-- From Fulu: the blob limit in force at an epoch, with the epoch from which it holds. -/
structure BlobParameters where
  /-- The first epoch of the limit. -/
  epoch : Epoch
  /-- The most blobs in one block. -/
  maxBlobsPerBlock : UInt64
  deriving DecidableEq, Repr

/-- The entry of a schedule with the latest first epoch at or before an epoch.

Among entries with that same first epoch, the first in the schedule wins. -/
def latestStarted {α : Type} (first : α → Epoch) (entries : List α) (epoch : Epoch) :
    Option α :=
  -- The merge sort is stable, so entries with equal epochs keep their order.
  (entries.mergeSort fun a b => first b ≤ first a).find? (first · ≤ epoch)

namespace Config

/-- From Fulu: the blob limit at an epoch.

It is the limit of the schedule entry with the latest first epoch at or before the epoch.

Among entries with that same first epoch, the first in the schedule wins.

With no such entry, the limit of Electra holds, from the first epoch of Electra.

[EIP-7892] adds the schedule.

[EIP-7892]: https://eips.ethereum.org/EIPS/eip-7892#consensus-layer-configuration
-/
def getBlobParameters (config : Config) (epoch : Epoch) : BlobParameters :=
  match latestStarted (·.EPOCH) config.BLOB_SCHEDULE epoch with
  | some entry => ⟨entry.EPOCH, entry.MAX_BLOBS_PER_BLOCK⟩
  | none => ⟨config.ELECTRA_FORK_EPOCH, config.MAX_BLOBS_PER_BLOCK_ELECTRA⟩

/-- From Gloas: the gas limit that the schedule recommends at an epoch, if any.

It is the limit of the entry with the latest first epoch at or before the epoch.

With no such entry, the schedule recommends nothing.

[EIP-8261] adds the schedule, which changes no validity rule.

The EIP also has clients ignore the schedule for duties before the first epoch of Gloas.

Every entry starts at or after that epoch, so the schedule recommends nothing before it anyway.

[EIP-8261]: https://eips.ethereum.org/EIPS/eip-8261#gas-limit-schedule
-/
def getScheduledGasLimit (config : Config) (epoch : Epoch) : Option UInt64 :=
  (latestStarted (·.EPOCH) config.GAS_LIMIT_SCHEDULE epoch).map (·.GAS_LIMIT)

end Config

end EthLib.Consensus
